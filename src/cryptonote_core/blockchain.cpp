// Copyright (c) 2014-2018, The Monero Project
//
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without modification, are
// permitted provided that the following conditions are met:
//
// 1. Redistributions of source code must retain the above copyright notice, this list of
//    conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright notice, this list
//    of conditions and the following disclaimer in the documentation and/or other
//    materials provided with the distribution.
//
// 3. Neither the name of the copyright holder nor the names of its contributors may be
//    used to endorse or promote products derived from this software without specific
//    prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND ANY
// EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL
// THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
// PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
// STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF
// THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
//
// Parts of this file are originally copyright (c) 2012-2013 The Cryptonote developers

#include <algorithm>
#include <cstdio>
#include <boost/filesystem.hpp>
#include <boost/range/adaptor/reversed.hpp>

#include "include_base_utils.h"
#include "cryptonote_basic/cryptonote_basic_impl.h"
#include "tx_pool.h"
#include "blockchain.h"
#include "blockchain_db/blockchain_db.h"
#include "cryptonote_basic/cryptonote_boost_serialization.h"
#include "cryptonote_config.h"
#include "cryptonote_basic/miner.h"
#include "misc_language.h"
#include "profile_tools.h"
#include "file_io_utils.h"
#include "common/int-util.h"
#include "common/threadpool.h"
#include "common/boost_serialization_helper.h"
#include "warnings.h"
#include "crypto/hash.h"
#include "cryptonote_core.h"
#include "ringct/rctSigs.h"
#include "common/perf_timer.h"
#if defined(PER_BLOCK_CHECKPOINT)
#include "blocks/blocks.h"
#endif

#undef MONERO_DEFAULT_LOG_CATEGORY
#define MONERO_DEFAULT_LOG_CATEGORY "blockchain"

#define FIND_BLOCKCHAIN_SUPPLEMENT_MAX_SIZE (100*1024*1024) // 100 MB

using namespace crypto;

//#include "serialization/json_archive.h"

/* TODO:
 *  Clean up code:
 *    Possibly change how outputs are referred to/indexed in blockchain and wallets
 *
 */

using namespace cryptonote;
using epee::string_tools::pod_to_hex;

DISABLE_VS_WARNINGS(4267)

#define MERROR_VER(x) MCERROR("verify", x)

// used to overestimate the block reward when estimating a per kB to use
#define BLOCK_REWARD_OVERESTIMATE (10 * 1000000000000)

static const struct {
  uint8_t version;
  uint64_t height;
  uint8_t threshold;
  time_t time;
} mainnet_hard_forks[] = {
  { 1, 1, 0, 1519744920},
  { 2, 2, 0, 1519744922},
  { 3, 3, 0, 1519744923},
  { 4, 24831, 0, 1524668700},
  { 5, 24861, 0, 1524968340},
  { 7, 89500, 0, 1534378192},
};
static const uint64_t mainnet_hard_fork_version_1_till = 0;

static const struct {
  uint8_t version;
  uint64_t height;
  uint8_t threshold;
  time_t time;
} testnet_hard_forks[] = {

};
static const uint64_t testnet_hard_fork_version_1_till = 624633;

static const struct {
  uint8_t version;
  uint64_t height;
  uint8_t threshold;
  time_t time;
} stagenet_hard_forks[] = {

};

//------------------------------------------------------------------
Blockchain::Blockchain(tx_memory_pool& tx_pool) :
  m_db(), m_tx_pool(tx_pool), m_hardfork(NULL), m_timestamps_and_difficulties_height(0), m_current_block_cumul_sz_limit(0), m_current_block_cumul_sz_median(0),
  m_enforce_dns_checkpoints(false), m_max_prepare_blocks_threads(4), m_db_blocks_per_sync(1), m_db_sync_mode(db_async), m_db_default_sync(false), m_fast_sync(true), m_show_time_stats(false), m_sync_counter(0), m_cancel(false),
  m_difficulty_for_next_block_top_hash(crypto::null_hash),
  m_difficulty_for_next_block(1)
{
  LOG_PRINT_L3("Blockchain::" << __func__);
}
//------------------------------------------------------------------
bool Blockchain::have_tx(const crypto::hash &id) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  // WARNING: this function does not take m_blockchain_lock, and thus should only call read only
  // m_db functions which do not depend on one another (ie, no getheight + gethash(height-1), as
  // well as not accessing class members, even read only (ie, m_invalid_blocks). The caller must
  // lock if it is otherwise needed.
  return m_db->tx_exists(id);
}
//------------------------------------------------------------------
bool Blockchain::have_tx_keyimg_as_spent(const crypto::key_image &key_im) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  // WARNING: this function does not take m_blockchain_lock, and thus should only call read only
  // m_db functions which do not depend on one another (ie, no getheight + gethash(height-1), as
  // well as not accessing class members, even read only (ie, m_invalid_blocks). The caller must
  // lock if it is otherwise needed.
  return  m_db->has_key_image(key_im);
}
//------------------------------------------------------------------
// This function makes sure that each "input" in an input (mixins) exists
// and collects the public key for each from the transaction it was included in
// via the visitor passed to it.
template <class visitor_t>
bool Blockchain::scan_outputkeys_for_indexes(size_t tx_version, const txin_to_key& tx_in_to_key, visitor_t &vis, const crypto::hash &tx_prefix_hash, uint64_t* pmax_related_block_height) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);

  // ND: Disable locking and make method private.
  //CRITICAL_REGION_LOCAL(m_blockchain_lock);

  // verify that the input has key offsets (that it exists properly, really)
  if(!tx_in_to_key.key_offsets.size())
    return false;

  // cryptonote_format_utils uses relative offsets for indexing to the global
  // outputs list.  that is to say that absolute offset #2 is absolute offset
  // #1 plus relative offset #2.
  // TODO: Investigate if this is necessary / why this is done.
  std::vector<uint64_t> absolute_offsets = relative_output_offsets_to_absolute(tx_in_to_key.key_offsets);
  std::vector<output_data_t> outputs;

  bool found = false;
  auto it = m_scan_table.find(tx_prefix_hash);
  if (it != m_scan_table.end())
  {
    auto its = it->second.find(tx_in_to_key.k_image);
    if (its != it->second.end())
    {
      outputs = its->second;
      found = true;
    }
  }

  if (!found)
  {
    try
    {
      m_db->get_output_key(tx_in_to_key.amount, absolute_offsets, outputs, true);
      if (absolute_offsets.size() != outputs.size())
      {
        MERROR_VER("Output does not exist! amount = " << tx_in_to_key.amount);
        return false;
      }
    }
    catch (...)
    {
      MERROR_VER("Output does not exist! amount = " << tx_in_to_key.amount);
      return false;
    }
  }
  else
  {
    // check for partial results and add the rest if needed;
    if (outputs.size() < absolute_offsets.size() && outputs.size() > 0)
    {
      MDEBUG("Additional outputs needed: " << absolute_offsets.size() - outputs.size());
      std::vector < uint64_t > add_offsets;
      std::vector<output_data_t> add_outputs;
      for (size_t i = outputs.size(); i < absolute_offsets.size(); i++)
        add_offsets.push_back(absolute_offsets[i]);
      try
      {
        m_db->get_output_key(tx_in_to_key.amount, add_offsets, add_outputs, true);
        if (add_offsets.size() != add_outputs.size())
        {
          MERROR_VER("Output does not exist! amount = " << tx_in_to_key.amount);
          return false;
        }
      }
      catch (...)
      {
        MERROR_VER("Output does not exist! amount = " << tx_in_to_key.amount);
        return false;
      }
      outputs.insert(outputs.end(), add_outputs.begin(), add_outputs.end());
    }
  }

  size_t count = 0;
  for (const uint64_t& i : absolute_offsets)
  {
    try
    {
      output_data_t output_index;
      try
      {
        // get tx hash and output index for output
        if (count < outputs.size())
          output_index = outputs.at(count);
        else
          output_index = m_db->get_output_key(tx_in_to_key.amount, i);

        // call to the passed boost visitor to grab the public key for the output
        if (!vis.handle_output(output_index.unlock_time, output_index.pubkey, output_index.commitment) && get_current_hard_fork_version() >= 6)
        {
          MERROR_VER("Failed to handle_output for output no = " << count << ", with absolute offset " << i);
          return false;
        }
      }
      catch (...)
      {
        if (get_current_hard_fork_version() >= 6){
        MERROR_VER("Output does not exist! amount = " << tx_in_to_key.amount << ", absolute_offset = " << i);
        return false;
        }
      }

      // if on last output and pmax_related_block_height not null pointer
      if(++count == absolute_offsets.size() && pmax_related_block_height)
      {
        // set *pmax_related_block_height to tx block height for this output
        auto h = output_index.height;
        if(*pmax_related_block_height < h)
        {
          *pmax_related_block_height = h;
        }
      }

    }
    catch (const OUTPUT_DNE& e)
    {
      MERROR_VER("Output does not exist: " << e.what());
      return false;
    }
    catch (const TX_DNE& e)
    {
      MERROR_VER("Transaction does not exist: " << e.what());
      return false;
    }

  }

  return true;
}
//------------------------------------------------------------------
uint64_t Blockchain::get_current_blockchain_height() const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  // WARNING: this function does not take m_blockchain_lock, and thus should only call read only
  // m_db functions which do not depend on one another (ie, no getheight + gethash(height-1), as
  // well as not accessing class members, even read only (ie, m_invalid_blocks). The caller must
  // lock if it is otherwise needed.
  return m_db->height();
}
//------------------------------------------------------------------
//FIXME: possibly move this into the constructor, to avoid accidentally
//       dereferencing a null BlockchainDB pointer
bool Blockchain::init(BlockchainDB* db, const network_type nettype, bool offline, const cryptonote::test_options *test_options)
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_tx_pool);
  CRITICAL_REGION_LOCAL1(m_blockchain_lock);

  if (db == nullptr)
  {
    LOG_ERROR("Attempted to init Blockchain with null DB");
    return false;
  }
  if (!db->is_open())
  {
    LOG_ERROR("Attempted to init Blockchain with unopened DB");
    delete db;
    return false;
  }

  m_db = db;

  m_nettype = test_options != NULL ? FAKECHAIN : nettype;
  m_offline = offline;
  if (m_hardfork == nullptr)
  {
    if (m_nettype ==  FAKECHAIN || m_nettype == STAGENET)
      m_hardfork = new HardFork(*db, 1, 0);
    else if (m_nettype == TESTNET)
      m_hardfork = new HardFork(*db, 1, testnet_hard_fork_version_1_till);
    else
      m_hardfork = new HardFork(*db, 1, mainnet_hard_fork_version_1_till);
  }
  if (m_nettype == FAKECHAIN)
  {
    for (size_t n = 0; test_options->hard_forks[n].first; ++n)
      m_hardfork->add_fork(test_options->hard_forks[n].first, test_options->hard_forks[n].second, 0, n + 1);
  }
  else if (m_nettype == TESTNET)
  {
    for (size_t n = 0; n < sizeof(testnet_hard_forks) / sizeof(testnet_hard_forks[0]); ++n)
      m_hardfork->add_fork(testnet_hard_forks[n].version, testnet_hard_forks[n].height, testnet_hard_forks[n].threshold, testnet_hard_forks[n].time);
  }
  else if (m_nettype == STAGENET)
  {
    for (size_t n = 0; n < sizeof(stagenet_hard_forks) / sizeof(stagenet_hard_forks[0]); ++n)
      m_hardfork->add_fork(stagenet_hard_forks[n].version, stagenet_hard_forks[n].height, stagenet_hard_forks[n].threshold, stagenet_hard_forks[n].time);
  }
  else
  {
    for (size_t n = 0; n < sizeof(mainnet_hard_forks) / sizeof(mainnet_hard_forks[0]); ++n)
      m_hardfork->add_fork(mainnet_hard_forks[n].version, mainnet_hard_forks[n].height, mainnet_hard_forks[n].threshold, mainnet_hard_forks[n].time);
  }
  m_hardfork->init();

  m_db->set_hard_fork(m_hardfork);

  // if the blockchain is new, add the genesis block
  // this feels kinda kludgy to do it this way, but can be looked at later.
  // TODO: add function to create and store genesis block,
  //       taking testnet into account
  if(!m_db->height())
  {
    MINFO("Blockchain not loaded, generating genesis block.");
    block bl = boost::value_initialized<block>();
    block_verification_context bvc = boost::value_initialized<block_verification_context>();
    if (m_nettype == TESTNET)
    {
      generate_genesis_block(bl, config::testnet::GENESIS_TX, config::testnet::GENESIS_NONCE);
    }
    else if (m_nettype == STAGENET)
    {
      generate_genesis_block(bl, config::stagenet::GENESIS_TX, config::stagenet::GENESIS_NONCE);
    }
    else
    {
      generate_genesis_block(bl, config::GENESIS_TX, config::GENESIS_NONCE);
    }
    add_new_block(bl, bvc);
    CHECK_AND_ASSERT_MES(!bvc.m_verifivation_failed, false, "Failed to add genesis block to blockchain");
  }
  // TODO: if blockchain load successful, verify blockchain against both
  //       hard-coded and runtime-loaded (and enforced) checkpoints.
  else
  {
  }

  if (m_nettype != FAKECHAIN)
  {
    // ensure we fixup anything we found and fix in the future
    m_db->fixup();
  }

  m_db->block_txn_start(true);
  // check how far behind we are
  uint64_t top_block_timestamp = m_db->get_top_block_timestamp();
  uint64_t timestamp_diff = time(NULL) - top_block_timestamp;

  // genesis block has no timestamp, could probably change it to have timestamp of 1341378000...
  if(!top_block_timestamp)
    timestamp_diff = time(NULL) - 1341378000;

  // create general purpose async service queue

  m_async_work_idle = std::unique_ptr < boost::asio::io_service::work > (new boost::asio::io_service::work(m_async_service));
  // we only need 1
  m_async_pool.create_thread(boost::bind(&boost::asio::io_service::run, &m_async_service));

#if defined(PER_BLOCK_CHECKPOINT)
  if (m_nettype != FAKECHAIN)
    load_compiled_in_block_hashes();
#endif

  MINFO("Blockchain initialized. last block: " << m_db->height() - 1 << ", " << epee::misc_utils::get_time_interval_string(timestamp_diff) << " time ago, current difficulty: " << get_difficulty_for_next_block());
  m_db->block_txn_stop();

  uint64_t num_popped_blocks = 0;
  while (true)
  {
    const uint64_t top_height = m_db->height() - 1;
    const crypto::hash top_id = m_db->top_block_hash();
    const block top_block = m_db->get_top_block();
    const uint8_t ideal_hf_version = get_ideal_hard_fork_version(top_height);
    if (ideal_hf_version <= 1 || ideal_hf_version == top_block.major_version)
    {
      if (num_popped_blocks > 0)
        MGINFO("Initial popping done, top block: " << top_id << ", top height: " << top_height << ", block version: " << (uint64_t)top_block.major_version);
      break;
    }
    else
    {
      if (num_popped_blocks == 0)
        MGINFO("Current top block " << top_id << " at height " << top_height << " has version " << (uint64_t)top_block.major_version << " which disagrees with the ideal version " << (uint64_t)ideal_hf_version);
      if (num_popped_blocks % 100 == 0)
        MGINFO("Popping blocks... " << top_height);
      ++num_popped_blocks;
      block popped_block;
      std::vector<transaction> popped_txs;
      try
      {
        m_db->pop_block(popped_block, popped_txs);
      }
      // anything that could cause this to throw is likely catastrophic,
      // so we re-throw
      catch (const std::exception& e)
      {
        MERROR("Error popping block from blockchain: " << e.what());
        throw;
      }
      catch (...)
      {
        MERROR("Error popping block from blockchain, throwing!");
        throw;
      }
    }
  }
  if (num_popped_blocks > 0)
  {
    m_timestamps_and_difficulties_height = 0;
    m_hardfork->reorganize_from_chain_height(get_current_blockchain_height());
    m_tx_pool.on_blockchain_dec(m_db->height()-1, get_tail_id());
  }

  update_next_cumulative_size_limit();
  return true;
}
//------------------------------------------------------------------
bool Blockchain::init(BlockchainDB* db, HardFork*& hf, const network_type nettype, bool offline)
{
  if (hf != nullptr)
    m_hardfork = hf;
  bool res = init(db, nettype, offline, NULL);
  if (hf == nullptr)
    hf = m_hardfork;
  return res;
}
//------------------------------------------------------------------
bool Blockchain::store_blockchain()
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  // lock because the rpc_thread command handler also calls this
  CRITICAL_REGION_LOCAL(m_db->m_synchronization_lock);

  TIME_MEASURE_START(save);
  // TODO: make sure sync(if this throws that it is not simply ignored higher
  // up the call stack
  try
  {
    m_db->sync();
  }
  catch (const std::exception& e)
  {
    MERROR(std::string("Error syncing blockchain db: ") + e.what() + "-- shutting down now to prevent issues!");
    throw;
  }
  catch (...)
  {
    MERROR("There was an issue storing the blockchain, shutting down now to prevent issues!");
    throw;
  }

  TIME_MEASURE_FINISH(save);
  if(m_show_time_stats)
    MINFO("Blockchain stored OK, took: " << save << " ms");
  return true;
}
//------------------------------------------------------------------
bool Blockchain::deinit()
{
  LOG_PRINT_L3("Blockchain::" << __func__);

  MTRACE("Stopping blockchain read/write activity");

 // stop async service
  m_async_work_idle.reset();
  m_async_pool.join_all();
  m_async_service.stop();

  // as this should be called if handling a SIGSEGV, need to check
  // if m_db is a NULL pointer (and thus may have caused the illegal
  // memory operation), otherwise we may cause a loop.
  if (m_db == NULL)
  {
    throw DB_ERROR("The db pointer is null in Blockchain, the blockchain may be corrupt!");
  }

  try
  {
    m_db->close();
    MTRACE("Local blockchain read/write activity stopped successfully");
  }
  catch (const std::exception& e)
  {
    LOG_ERROR(std::string("Error closing blockchain db: ") + e.what());
  }
  catch (...)
  {
    LOG_ERROR("There was an issue closing/storing the blockchain, shutting down now to prevent issues!");
  }

  delete m_hardfork;
  m_hardfork = NULL;
  delete m_db;
  m_db = NULL;
  return true;
}
//------------------------------------------------------------------
// This function tells BlockchainDB to remove the top block from the
// blockchain and then returns all transactions (except the miner tx, of course)
// from it to the tx_pool
block Blockchain::pop_block_from_blockchain()
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);

  m_timestamps_and_difficulties_height = 0;

  block popped_block;
  std::vector<transaction> popped_txs;

  try
  {
    m_db->pop_block(popped_block, popped_txs);
  }
  // anything that could cause this to throw is likely catastrophic,
  // so we re-throw
  catch (const std::exception& e)
  {
    LOG_ERROR("Error popping block from blockchain: " << e.what());
    throw;
  }
  catch (...)
  {
    LOG_ERROR("Error popping block from blockchain, throwing!");
    throw;
  }

  // return transactions from popped block to the tx_pool
  for (transaction& tx : popped_txs)
  {
    if (!is_coinbase(tx))
    {
      cryptonote::tx_verification_context tvc = AUTO_VAL_INIT(tvc);

      // FIXME: HardFork
      // Besides the below, popping a block should also remove the last entry
      // in hf_versions.
      //
      // FIXME: HardFork
      // This is not quite correct, as we really want to add the txes
      // to the pool based on the version determined after all blocks
      // are popped.
      uint8_t version = get_current_hard_fork_version();

      // We assume that if they were in a block, the transactions are already
      // known to the network as a whole. However, if we had mined that block,
      // that might not be always true. Unlikely though, and always relaying
      // these again might cause a spike of traffic as many nodes re-relay
      // all the transactions in a popped block when a reorg happens.
      bool r = m_tx_pool.add_tx(tx, tvc, true, true, false, version);
      if (!r)
      {
        LOG_ERROR("Error returning transaction to tx_pool");
      }
    }
  }

  m_blocks_longhash_table.clear();
  m_scan_table.clear();
  m_blocks_txs_check.clear();
  m_check_txin_table.clear();

  update_next_cumulative_size_limit();
  m_tx_pool.on_blockchain_dec(m_db->height()-1, get_tail_id());

  return popped_block;
}
//------------------------------------------------------------------
bool Blockchain::reset_and_set_genesis_block(const block& b)
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);
  m_timestamps_and_difficulties_height = 0;
  m_alternative_chains.clear();
  m_db->reset();
  m_hardfork->init();

  block_verification_context bvc = boost::value_initialized<block_verification_context>();
  add_new_block(b, bvc);
  update_next_cumulative_size_limit();
  return bvc.m_added_to_main_chain && !bvc.m_verifivation_failed;
}
//------------------------------------------------------------------
crypto::hash Blockchain::get_tail_id(uint64_t& height) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);
  height = m_db->height() - 1;
  return get_tail_id();
}
//------------------------------------------------------------------
crypto::hash Blockchain::get_tail_id() const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  // WARNING: this function does not take m_blockchain_lock, and thus should only call read only
  // m_db functions which do not depend on one another (ie, no getheight + gethash(height-1), as
  // well as not accessing class members, even read only (ie, m_invalid_blocks). The caller must
  // lock if it is otherwise needed.
  return m_db->top_block_hash();
}
//------------------------------------------------------------------
/*TODO: this function was...poorly written.  As such, I'm not entirely
 *      certain on what it was supposed to be doing.  Need to look into this,
 *      but it doesn't seem terribly important just yet.
 *
 * puts into list <ids> a list of hashes representing certain blocks
 * from the blockchain in reverse chronological order
 *
 * the blocks chosen, at the time of this writing, are:
 *   the most recent 11
 *   powers of 2 less recent from there, so 13, 17, 25, etc...
 *
 */
bool Blockchain::get_short_chain_history(std::list<crypto::hash>& ids) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);
  uint64_t i = 0;
  uint64_t current_multiplier = 1;
  uint64_t sz = m_db->height();

  if(!sz)
    return true;

  m_db->block_txn_start(true);
  bool genesis_included = false;
  uint64_t current_back_offset = 1;
  while(current_back_offset < sz)
  {
    ids.push_back(m_db->get_block_hash_from_height(sz - current_back_offset));

    if(sz-current_back_offset == 0)
    {
      genesis_included = true;
    }
    if(i < 10)
    {
      ++current_back_offset;
    }
    else
    {
      current_multiplier *= 2;
      current_back_offset += current_multiplier;
    }
    ++i;
  }

  if (!genesis_included)
  {
    ids.push_back(m_db->get_block_hash_from_height(0));
  }
  m_db->block_txn_stop();

  return true;
}
//------------------------------------------------------------------
crypto::hash Blockchain::get_block_id_by_height(uint64_t height) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  // WARNING: this function does not take m_blockchain_lock, and thus should only call read only
  // m_db functions which do not depend on one another (ie, no getheight + gethash(height-1), as
  // well as not accessing class members, even read only (ie, m_invalid_blocks). The caller must
  // lock if it is otherwise needed.
  try
  {
    return m_db->get_block_hash_from_height(height);
  }
  catch (const BLOCK_DNE& e)
  {
  }
  catch (const std::exception& e)
  {
    MERROR(std::string("Something went wrong fetching block hash by height: ") + e.what());
    throw;
  }
  catch (...)
  {
    MERROR(std::string("Something went wrong fetching block hash by height"));
    throw;
  }
  return null_hash;
}
//------------------------------------------------------------------
bool Blockchain::get_block_by_hash(const crypto::hash &h, block &blk, bool *orphan) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);

  // try to find block in main chain
  try
  {
    blk = m_db->get_block(h);
    if (orphan)
      *orphan = false;
    return true;
  }
  // try to find block in alternative chain
  catch (const BLOCK_DNE& e)
  {
    blocks_ext_by_hash::const_iterator it_alt = m_alternative_chains.find(h);
    if (m_alternative_chains.end() != it_alt)
    {
      blk = it_alt->second.bl;
      if (orphan)
        *orphan = true;
      return true;
    }
  }
  catch (const std::exception& e)
  {
    MERROR(std::string("Something went wrong fetching block by hash: ") + e.what());
    throw;
  }
  catch (...)
  {
    MERROR(std::string("Something went wrong fetching block hash by hash"));
    throw;
  }

  return false;
}
//------------------------------------------------------------------
// This function aggregates the cumulative difficulties and timestamps of the
// last DIFFICULTY_BLOCKS_COUNT blocks and passes them to next_difficulty,
// returning the result of that call.  Ignores the genesis block, and can use
// less blocks than desired if there aren't enough.
difficulty_type Blockchain::get_difficulty_for_next_block()
{
  LOG_PRINT_L3("Blockchain::" << __func__);

  CRITICAL_REGION_LOCAL(m_difficulty_lock);
  // we can call this without the blockchain lock, it might just give us
  // something a bit out of date, but that's fine since anything which
  // requires the blockchain lock will have acquired it in the first place,
  // and it will be unlocked only when called from the getinfo RPC
  crypto::hash top_hash = get_tail_id();
  if (top_hash == m_difficulty_for_next_block_top_hash)
    return m_difficulty_for_next_block;

  CRITICAL_REGION_LOCAL1(m_blockchain_lock);
  std::vector<uint64_t> timestamps;
  std::vector<difficulty_type> difficulties;
  uint8_t version = get_current_hard_fork_version();
  auto height = m_db->height();
  size_t difficulty_blocks_count = 0;
  if(version < 5){
   difficulty_blocks_count = DIFFICULTY_BLOCKS_COUNT;
 }else if(version >= 5 && version < 7){
   difficulty_blocks_count = DIFFICULTY_BLOCKS_COUNT;
 }else if(version >= 7){
   difficulty_blocks_count = DIFFICULTY_BLOCKS_COUNT_V3;
 }
  // ND: Speedup
  // 1. Keep a list of the last 735 (or less) blocks that is used to compute difficulty,
  //    then when the next block difficulty is queried, push the latest height data and
  //    pop the oldest one from the list. This only requires 1x read per height instead
  //    of doing 735 (DIFFICULTY_BLOCKS_COUNT).
  if (m_timestamps_and_difficulties_height != 0 && ((height - m_timestamps_and_difficulties_height) == 1) && m_timestamps.size() >= difficulty_blocks_count)
  {
    uint64_t index = height - 1;
   m_timestamps.push_back(m_db->get_block_timestamp(index));
   m_difficulties.push_back(m_db->get_block_cumulative_difficulty(index));

   while (m_timestamps.size() > difficulty_blocks_count)
     m_timestamps.erase(m_timestamps.begin());
   while (m_difficulties.size() > difficulty_blocks_count)
     m_difficulties.erase(m_difficulties.begin());

   m_timestamps_and_difficulties_height = height;
   timestamps = m_timestamps;
   difficulties = m_difficulties;
  }
  else
  {
    size_t offset = height - std::min < size_t > (height, static_cast<size_t>(difficulty_blocks_count));
      if (offset == 0){
        ++offset;
      }

      timestamps.clear();
      difficulties.clear();
      if (height > offset)
      {
        timestamps.reserve(height - offset);
        difficulties.reserve(height - offset);
      }
      for (; offset < height; offset++)
      {
        timestamps.push_back(m_db->get_block_timestamp(offset));
        difficulties.push_back(m_db->get_block_cumulative_difficulty(offset));
      }

      m_timestamps_and_difficulties_height = height;
      m_timestamps = timestamps;
      m_difficulties = difficulties;
  }
  size_t target = get_difficulty_target();
  difficulty_type diff;
  //IF FORKING THIS PLEASE CHANGE IT TO YOUR LIKINGS
  //TRITON HAD A MISHAP ON BLOCK VERSION 4
  if(version <= 3){
    if(height == 24830){
      diff = 335687327;
    }else {
     diff = next_difficulty(std::move(timestamps), std::move(difficulties), target,height - 1);
   }
  }else if(version == 4){
    //HARDCODE VERSION 4 DIFFICULTIES
    int startHeight = 24831;
    int difficultiesforv4 [32] = {334548400,330009535,330209072,330252077,330298610,331947716,332574156,331515192,332574156,331515192,331120332,330840255,331866703,332366852,329906693,330494043,330699033,330858012,331210050,331142467,332613428,333252897,334161767,334594058,334764297,335859071,336394300,337546011,336886799,336147226,10000000};

    diff = difficultiesforv4[(height + 1) - startHeight];
  }else if(version >= 5 && version < 7){
    if(height >= 24861 && height <= 24921){
      diff = 10000000;
    }else if(height == 24922){

      diff = 51286833;

    }else if(height >= 24923 && height <= 25000){

        int difficultiesforv5_1 [77] = {50744095,50738436,46352241,40626859,40460733,40309070,37418692,37261152,37200894,36539370,36400448,36396224,35754940,35558266,32017970,31532443,31417428,31334391,31249155,31163104,31081880,31000451,30934438,30860283,30759856,30707361,30632579,30557438,30471116,30410223,30321113,30241782,30181080,30104586,30029595,29958659,29884795,29805492,29727460,29580599,29507388,29441407,29362454,29289175,29210489,
        29132679,29073585,2899295,28926886,2884949,28781241,28704783,28635317,28567962,28493865,28420474,28340805,28267054,28191071,28115424,28034413,27964485,27911101,27837253,27766992,27689465,27613821,27543061,27469072,2739888,27318672,27248257,27170156,27094922,26098514,26018914,25884986};

        diff = difficultiesforv5_1[(height) - 24923];
        if(height == 25000){
          diff = 25884986;
        }
      }else if(height >= 25001 && height <= 25500){

        int difficultiesforv5_2 [501] = {25818315,25743830,25622902,25558093,25496533,25426121,25356862,25282917,25179337,25126156,25055972,24985711,24926029,24854219,24781811,24734754,24665546,
        24595504,24513511,24443798,24365146,24284920,24214778,24152829,24078084,24003734,23942368,23871352,23799862,23727754,23664439,23590024,23529023,23449883,23387036,23320143,23248756,23186009,23120531,23040565,22967900,22895585,22826470,22755319,22682697,22604040,22520681,22447975,22384159,22315947,22242376,22172689,22101110,22034105,21973304,21905839,21832779,21766276,21695355,21622276,21560975,21476586,21411577,21342601,21271584,21204788,
        21129655,21066133,20994584,20918720,20850589,20776196,20701190,20633967,20565087,20485546,20409488,20339780,20253676,20177920,20110440,20042790,19973430,19903869,19833131,19765317,19695460,19625695,19559170,19490922,19418267,19345780,19267018,19189559,19116369,19048991,18975270,18900455,18826126,18754278,18754278,18685513,18609439,18530538,18455229,18383886,18311987,18243126,18169071,18103311,18032019,17937728,17870618,17798745,17726669,
        17657708,17594870,17526716,17450616,17374331,17300790,17226388,17154919,17084390,17017668,16946997,16872668,16797868,16723030,16648955,16563102,16486596,16416188,16332751,16246907,16164843,16081084,15995203,15918879,15828898,15745363,15663328,15591203,15513066,15431297,15347583,15259675,15174292,15094821,15020912,14934724,14846839,14778011,14692711,14605849,14519739,14441982,14363647,14279858,14199368,14113555,14026175,13936813,13850999,
        13763264,13676168,13592375,13499944,13420268,13333483,13251879,13164872,13076240,12990101,12907765,12821972,12731416,12635166,12549769,12463843,12374970,12285926,12199013,12112699,12021799,11928928,11837791,11750072,11657129,11564714,11472385,11384323,11307395,11217513,11126871,11035899,10945269,10858978,10771683,10682070,10590218,10500874,10412562,10327785,10236769,10146140,10052099,9956648,9868445,9778455,9679998,9585293,9494892,
        9402911,9312608,9221859,9131839,9042376,8956402,8870904,8781345,8693767,8604605,8518756,8429212,8339378,8252817,8165428,8075252,7983907,7892999,7832662,8720689,8813434,10433598,10829371,10697932,10563267,10437012,10314649,10180386,10048788,9917262,9784741,9651563,9516954,9384802,9254693,9137340,9005963,8873068,8742579,8610246,8481474,8348761,8215727,8082863,7951503,7819016,7680163,7541959,7407393,
        7271629,7136657,7003568,6867715,6946059,7446703,7392609,7922274,7763110,7881152,7703332,7731195,7693832,7625665,7487202,7372760,7185078,7058469,6910535,6724453,6625098,6434800,7111299,8921735,8725615,8521815,10162668,9949402,9645178,9886174,9630269,9263183,9522346,9648056,17648119,19813443,20045000,20078877,20190249,20274123,20280836,20304705,20369648,20360448,20548149,20547480,20531248,20524384,20584010,
        20580714,20624110,20651613,20680516,20679744,20643831,20674967,20692130,20763138,20814170,20805469,20780858,20774154,20766070,20793438,20798702,20807038,20812220,20804562,20810691,20806734,20793040,20774129,20772783,20759632,20752280,20743492,20730166,20737795,20740897,20723935,20741350,20747861,20751450,20743142,20739542,20719023,20706273,20696025,20688079,20677176,20677908,20670721,20659530,20656904,20657964,32362088,32690298,34002495,
        33865549,33901325,35126334,34941020,35058291,34972968,34795264,34844015,35758685,35633056,35692930,35714310,35815041,35843110,35955441,35909903,35748667,35747739,36160740,36367649,36425706,36849011,36875595,37044314,37200745,37049397,36873009,37213154,37241738,37302183,37157111,37359290,37135880,37384487,37316269,37348197,37747077,37659338,37244794,37519790,37554860,37683592,37596347,37588306,37727205,38026002,38495912,38409105,38398594,
        38361270,38246064,38088722,38288206,38237507,38012412,38015089,38046467,37933317,37750707,37612072,37558659,37818287,37925907,38011703,38084906,38002447,38148951,38128360,38127387,38238217,38158303,38332866,38404980,38377617,38396105,38821978,39261529,39331796,40079770,40343654,40485261,40495133,40063813,40161135,39935151,39617111,39680202,39643357,39554269,39557163,39316679,39552417,40012678,40589185,40530103,40568980,40617686,40826332,
        40976012,40934533,40999149,41299676,41852692,41466148,41429827,41362536,41539500,41765479,41890510,41918265,43697214,43569481,43526006,43684045,42875407,42936088,42782852,43205331,43652259,43959369,44223568,44209728,44417065,44403023,44580370,44833679,45181808,45323118,45235202,45016165,44856676,44972912,45171756,44977306,44895283,45251818,45372090,45256287,45122617,45029775,44578453};

        diff = difficultiesforv5_2[(height) - 25001];
        if(height == 25001){
          MERROR(diff);
        }
      }else if(height > 25500 && height <= 26000){

        int difficultiesforv5_3 [504] = {44490440,44417546,44493485,44589152,44431566,44253612,
        44446292,44295292,44413897,44668466,44871561,44822906,44829718,44884866,45171262,45336051,45355752,45060898,45119499,45077057,44871774,44848665,45232909,45347509,45658521,46148058,46175417,46339745,46229362,46196026,46080116,46236496,46206616,46231041,45750494,46545024,46453258,46182735,46069381,46227442,46354158,46193870,46305873,46494042,46419856,46530224,46844072,46832852,47176228,47327464,47291565,47570031,47636207,47422540,47821172,
        47993432,48233929,48444346,48317908,48154543,48096612,47996031,48209104,48222879,48637074,48718486,48850331,49017380,49829265,49723537,49695064,49933159,50133589,50096026,49782055,49702421,49793379,49535838,49712912,49950295,50081768,50231818,50323697,50681958,50852340,50780121,51018435,51093877,50581098,50278064,50259324,50399767,50465382,50074009,50255926,50534280,50739725,50836279,51022770,50769026,50972785,50581511,49792811,50231292,
        49984343,49987204,49378595,49565928,49676047,49686139,49452937,49471835,49520090,49432768,48309247,48133070,48397461,48447341,48880006,48907142,49133966,49161369,49159808,49062834,48990132,48726025,48818139,48992538,46686534,46706898,46464075,45592527,46464075,45592527,44702634,44809343,44534673,43953351,42579514,41897169,41848697,41853969,41602579,41639062,41285938,39812016,39115180,37363959,37242853,36375499,36508746,36353086,36266827,
        36250309,35925345,35761095,35512426,35095986,33632412,33265755,32027871,31447899,31392089,30952722,31068659,30964350,31006411,31123163,31022097,31073921,3119201,31245494,31106944,31052829,31158280,31003787,31128439,31164182,31237989,31266478,31280685,31273297,31379223,31204578,31228613,31019002,31121032,31121381,30980965,30995402,31030045,31082387,31177845,31288910,31256051,31266506,30654255,30660177,30676977,30613554,30591614,30663639,
        30763130,30734292,30754762,30608436,30716618,30773425,30795320,30885101,30698499,30574234,30573893,30633019,30627270,30574217,30652067,30616091,30591753,30673433,30718685,30758076,30754233,30782878,30759624,30820553,30667474,30698927,30567664,30313522,30341697,30393508,30253719,30200299,30223540,30068977,30092287,30087629,30029225,29963504,30040818,30090318,29917013,29951050,29810479,29895200,29974318,30007132,29722896,29711603,
        29686501,29550299,29621301,29649368,29397411,29414564,29345387,29273996,29365356,29394213,29410846,29490975,29489641,29504307,29519337,29523055,29476206,29492410,29485892,29477989,29550116,29480365,29478862,29531417,29403760,29375008,29378078,29421369,29463248,29519319,29445207,29422342,29433825,29363058,29365615,29163941,29211778,29189905,29206300,29194224,29191163,29191853,29190772,29204628,29198557,29200634,29167189,29160982,29137005,
        29130714,29127020,29039517,29058088,29021325,29070561,29026030,28998027,28970751,28989918,28807592,28793546,28788059,28675879,28605587,28437016,28431342,28411325,28283183,28276729,28253651,28033600,27928682,27876789,27974140,27944005,27935721,27859546,27805129,27753482,27740518,27478138,27454249,27454513,27379269,27357848,27193799,27165269,27003661,26966541,26934808,26900385,26867680,26695123,26591970,26226884,26204680,26190218,26080448,
        26079714,26082839,26096655,26047936,26037217,25955476,25915021,25843936,25730489,25500702,25565429,25333776,25355732,25326112,25294857,25235370,25001945,24853581,24787577,24679432,24389341,24346290,24271031,24228190,24202727,24195014,24171777,24089240,24080619,24069094,23942633,23817968,23736487,23761748,23697384,23598520,23445902,23193729,23162782,23140159,23106870,23096218,23046958,23065366,22983352,22975320,22961353,23014338,22748400,
        22717284,22700643,22684577,22536149,22447888,22317091,22218983,22184593,22182605,22109955,22051108,21896424,21871823,21716513,21691029,21667268,21649433,21565550,21527153,21500948,21448571,21415386,21436676,21416331,21383516,21396141,21314317,21300699,21233115,21166599,21105032,21055076,21030514,21072621,21091165,21074925,21031112,21031226,21025009,20893725,20878499,20874675,20749683,20717237,20687885,20657079,20624178,20563212,20482889,
        20484273,20435832,20411672,20442197,20463276,20405856,20370748,20296858,20320463,20279932,20251249,20180115,20154397,19956551,19949693,19851934,19821589,19911262,19835189,19837622,19820473,19877306,19799108,19777747,19702934,19677827,19634702,19579718,19581281,19715786,19692219,19606391,19621257,19583114,19564501,19518309,19502203,19479421,19463276,19457910,19452900,19419477,19391245,19696297,19678171,19646240,19777090,19888452,19835600,
        19831388,19908663,20111916,20247215,20211918,20201554,20234019};

        diff = difficultiesforv5_3[(height) - 25501];

      }else if(height > 26000 && height <= 26500){

        int difficultiesforv5_4 [504] = {20229534,20279300,20605499,20763404,21198263,21230921,21446674,21389280,21375213,21409582,21394613,21500845,21545458,21639352,21792902,22346286,22498666,23105677,23383387,23407425,23657866,23592024,23665416,23650701,23524658,23581805,23553562,23399732,23347921,23454636,23490704,23398467,23449133,23314906,23267910,23223264,23151027,23101944,23089950,23050721,23168980,23069037,
        23208820,23127401,23119304,23175307,23167308,23142004,23099501,23026085,22948778,22928764,22924085,23360035,23327968,23326914,23339593,23353522,23314127,23245828,23275884,23244823,23338760,23258479,23183692,23158349,23099128,23227813,23332054,23277093,23190893,23192322,23243962,23166229,23125466,23120705,22984939,22915000,22880084,22817868,22806100,22810879,22776977,22926212,22899974,22968824,23141002,23122200,23091518,23196710,23209797,
        23144215,23288606,23263988,23264183,23285679,23327248,23310052,23283202,23422244,23364826,23353222,23346991,23298596,23275678,23500326,23507700,23529987,23672078,23620421,23605141,23869220,23739613,23819755,23884931,23871462,23845911,23800664,23717518,23724515,23632301,23604125,23618243,23662101,23656694,23608274,23615276,23563705,23612162,23614362,23524871,23674506,23717462,23663293,23696325,23697334,23685961,23697440,23758604,23753863,
        23835817,23830270,24028179,23997598,24015483,24002981,24041687,24001334,23953058,23919182,23899668,23884148,23852996,23866295,23840693,23806719,23749153,23741229,23747295,23787452,23803228,23767195,23818805,23810681,23840554,23733559,23862261,23911190,23903522,24004056,23998844,24114397,24102302,24137952,24276179,24060809,24096789,24341484,24347035,24313783,24159992,24079682,24095246,24172252,24047419,24054921,24017872,24326779,24339043,
        24324144,24302741,24518818,24705196,24773984,24965659,24923363,24935731,24932615,24955868,25127575,25245172,25750598,25671156,25485565,25467120,25415664,25442120,25449957,25353879,25292188,25468295,25492724,25480255,25661597,26101968,26024891,26219635,26298810,26143028,26075962,26140530,26489662,26869870,27088370,27244492,27929349,27942198,28035707,28077898,28082625,28087820,28028515,28025082,27943341,27938087,28036391,28314988,28527279,
        28348364,28507914,28647675,28979136,29550466,29552375,29664897,29566923,29613370,29738119,29709475,29859977,29737926,29734639,29664396,30326515,30386026,30598028,30578801,30924518,31082782,31484150,31669965,31802855,31650842,31877759,31979572,32546307,32496815,33024010,33131973,33162553,33165493,33593611,33619145,33485666,33590162,33536265,33563634,33591566,33643149,33584176,33721018,33623455,33756653,34034463,33967101,33876348,33942373,
        33996350,33943025,33752562,33535578,33557370,33683262,34303288,34303518,34470025,34812455,34814673,34853780,34698394,34640683,34607636,34868610,34494507,34444636,34388671,34348170,34353931,34464189,34366596,34603975,34650394,34531901,34156134,34164928,34067898,34836877,34958718,35235287,35482085,35480478,35666301,35773172,35739473,35604390,35799477,35532464,35667328,35763156,35884795,35762934,35719359,35646361,35366120,35530345,35530714,
        35082457,34908599,34598874,34520707,34371943,34156159,34129331,34163500,34164480,34161090,33936468,33817169,34155591,34167870,34271386,34366714,34190368,34287591,34386958,34240102,34390573,34347609,33907880,33549597,33515012,33380316,33482892,33365617,33052487,33156397,32793676,32955303,32989832,32997520,32781813,32791065,32812194,32742868,32818983,32865620,32738925,32829020,32899651,33022516,33096811,33151297,33179587,33300143,32941670,
        32622511,32941438,32863765,32891010,32946865,32871577,32841358,32622127,32717560,32672477,32478146,32302874,32258257,32001388,31968421,32103397,32109411,32160390,32202148,32207672,32213130,32245564,32073450,32168614,32245260,32290153,32299814,32342541,32297901,32286286,32350466,32236143,32294624,32147159,32204729,32157347,32234881,32213495,32269528,31559329,31572041,31547905,31607595,31782557,31674679,31587526,31613111,31466190,31551185,
        31492830,31613667,31733682,31646678,31755750,31783177,31508330,31394785,31386657,31271223,31319020,31313330,31288474,30907310,30928247,30735406,30826211,30849346,30861149,30565007,30672566,30744461,30530767,30450663,30500841,30572040,30716734,30733008,30573427,30445900,30482675,30440634,30468746,30493541,30396665,30337874,30286465,30476497,30470057,30491498,30537247,30472603,30286862,30279307,30207377,30235287,30187010,30250014,30306855,
        30299032,30401554,30359085,30290171,30332746,30118733,30155301,30165837,29873946,29930024,29754736,29720926,29733297,29805056,29766886,29522257,29489836};

        diff = difficultiesforv5_4[(height) - 26001];

      }else if(height > 26500 && height <= 26720){

        int difficultiesforv5_5 [504] = {29455602,29457353,29423509,29466800,29397080,29337820,29333016,29126534,29103253,29083987,29114439,29103370,29035611,29062102,28979911,29015771,28986905,28918191,28803956,28821572,28825570,28996020,28956643,29006706,29106751,29215270,29234648,29170193,29039479,29080628,28850079,28854978,
        28747297,28761462,28972043,28870962,28860956,28857089,28784783,28912123,28923169,28707629,28701017,28714574,28739111,28668477,28684321,28667454,28640659,28539709,28351232,28342571,28324055,28284365,28364493,28257785,28312810,28320696,28381392,28320881,28215753,28272118,28444023,28586010,28613996,28638984,28634715,28681929,28713555,28593488,28593871,28674019,28661202,28607319,28558457,28786683,28735531,28916810,28939205,28920501,28992955,
        28992904,28801924,28754721,28638740,28682156,28580630,28420302,28449983,28358835,28425016,28465936,28380549,28350893,28504969,28419676,28374687,28548860,28517553,28569343,28558228,28354631,28319926,28298430,28332175,28313815,28204356,28213245,28213407,28316676,28055600,28107042,28152444,28022868,27982082,27923480,27639711,27637823,27513437,27503469,27406584,27366130,27374570,27320481,27298045,27341012,27234279,26858258,26846380,26805073,
        26786601,26801304,26847902,26837038,26889503,26833278,26824563,26853596,26901422,26944391,26887571,26899869,26891044,26554276,26588512,26520682,26452833,26177690,26217173,26327191,26179134,26178340,26176568,26130757,25982171,25750620,25735773,25698608,25773263,25555614,25614240,25543475,25696511,25615995,25621026,25662726,25550393,25586449,25618074,25598041,25434159,25498838,25591261,25648866,25666375,25522801,25435309,25360900,25387591,
        25196928,25125323,25121499,25087375,25062383,24995807,25053405,24943807,24853948,24719623,24724680,24702689,24748099,24890002,24916341,24923792,25087371,25167342,25288833,25323952,25356938,25375956,25282420,25165149,24821960,24712545,24811902,24858009,24764345,24586665,24438050,24160755,24258459,24226487,24145885,24143321,24119050,24040798,24232812,24382268,24443773};

        diff = difficultiesforv5_5[(height) - 26501];

   }else if(height > 26721 && height <= 27189){
     int difficultiesforv5_6 [490] = {24509257,24391409,24385246,24471365,24445111,24524892,24489223,24478922,24474471,24379459,24350827,24330505,24307460,24324553,24242221,24291270,24257047,24185001,24108521,23993970,23961015,23958023,23931128,24012713,23893610,23962642,23858326,23761777,23613688,23551069,23585447,23755816,23734354,23697976,23760906,23656138,23889493,23735180,23738734,23700360,23735259,23683914,23667209,23696023,23665496,
       23525125,23608287,23583025,23510751,23517891,23516393,23540718,23484762,23528764,23499375,23542917,23475234,23548813,23447189,23424419,23208175,23232135,23193039,23568635,23511716,23552095,23312693,23351553,23376159,23302946,23205416,23156002,23184301,23171655,23179626,23066040,23064268,23064851,23048304,23176657,23190028,23181600,23234674,23167202,23129045,23148845,23292642,23237253,23336484,23306624,23172281,23187526,23308378,23315072,
       23164368,23234364,23270192,23210391,23193180,23239572,23204628,23252202,23300589,23296570,23318862,23316791,23258009,23338946,23361649,23364910,23323434,23309367,23312837,23284710,23098726,23129697,23117725,23120390,22911676,22912297,22856975,22818790,22850483,22828799,22850356,22839552,22837449,22937343,22862323,22833401,22987902,22935536,22981636,23013332,22983140,22919864,22898902,23023893,23045469,23063961,23083856,23107896,23102968,
       23113372,23060424,23161846,23277242,23228882,23121016,23007738,22919644,22948138,22768968,22736794,22699242,22707192,22675306,22726412,22687733,22652684,22626144,22643616,22556073,22566821,22492428,22465824,22368390,22441625,22395313,22594878,22590917,22651140,22614839,22607405,22672750,22666960,22601684,22689165,22728963,22788551,22913531,22873951,22986552,22890665,22835887,22800305,22809926,22807938,22930675,23065694,23069908,23084073,
       23063723,23044501,23124976,23107730,23083889,23006144,23066712,23165179,23102214,23085418,23094464,23126547,23112309,23099558,23172079,23146382,23090027,23035295,23038547,23030678,23028241,23068719,23000884,23041887,23051519,23089142,22999784,22915377,23063067,22906565,23041192,22954885,22938757,22971237,23096442,23104366,23158099,23064142,23021259,23104107,23130813,23177588,23218248,23262295,23270104,23245789,23216215,23215655,23191962,
       23188832,23184956,23142232,23130113,23179793,23133580,23074523,23054954,23282141,23288831,23272211,23374838,23400791,23733711,23473704,23730256,23789084,23822572,23896402,23999297,23981439,24034284,24029745,23985775,24032752,24334676,24334396,24270292,24223321,24198463,24147989,24136718,24104044,24142073,24175348,24163129,24151125,24142401,24192130,24182197,24196052,24585726,24622268,24550476,24571784,24826606,24816214,24760745,24909900,
       24868995,24790791,24836396,24954003,25269594,25290079,25338998,25279428,25584820,25597674,25665860,25632735,25749508,25773389,25720992,25834911,25859179,25853333,25880905,25821262,26123626,25917188,25825182,25954638,25825718,26035927,26064309,26016757,26262359,26206031,26211937,26251050,26324406,26391359,26340863,26652669,26549499,26828283,26912475,26860868,26847451,26787445,26633354,26546912,26625941,26523770,26558946,26414048,26354350,
       26409678,26569394,26732588,27249533,27341097,27316526,27351505,27151768,27378798,27614262,27991545,27912639,27922229,28086878,28127178,28135458,28316947,27983300,27954580,27791166,27698446,27850480,28064026,28158031,28247845,28327724,28236402,28316036,28303053,28569602,28455191,28466279,28557709,28504330,28482726,28442430,28384393,28429610,28448946,28602483,28617433,28642259,28412502,28609877,28493523,28480689,28700290,28845524,29079116,
       29313519,29246884,29248927,29239823,29280253,29411738,29419939,29861225,29637312,29838881,29709897,29692693,29692005,29709684,29723443,29500987,29443452,29140042,29298572,29248105,29260678,29116208,29078204,29057530,29053613,29067761,29099217,29158477,29139110,29103649,29169868,29477260,29216742,29333254,29337528,29410393,29412323,29692320,29729597,29766409,30138673,29866588,29738977,30033045,30111653,30353895,30149988,30495476,30537796,
       30538208,30584417,30653531,30711022,30584306,30795021,30927610,30895895,30735450,30903819,30835801,30619481,30711814,30702483,30758890,30763642,30995268,30966868,30802798,30868059,30654727,30569571,30561452,30328266,30365689,30401061,30354263,30287085,30382851,30397257,30215599,30052057};
       diff = difficultiesforv5_6[(height) - 26722];

   }else if(height > 27189 && height <= 27776){
     int difficultiesforv5_7 [586] = {29947065,29901852,29641920,29645956,29363549,29470007,29559483,30081647,30025879,30113027,30137241,30008629,29891494,29663817,29587238,29717471,29732368,29940723,29980768,30002409,30115658,30193529,30194284,29995052,30153360,30289155,30338154,30293757,30240892,30103369,29965468,29908184,29922969,29908690,29822398,29875482,29990292,30081839,30270618,30090353,30062226,30338532,30522936,30502981,30442296,
       30425300,30349655,30377131,30395453,30397615,30283322,30298599,29963988,30071242,30051831,30281458,30118044,30272513,30292181,30036108,30035199,30038559,29919275,29868374,29837746,30031258,30016242,30019704,30008624,30020672,30085258,30001988,30193283,30187185,30202985,29966423,30042968,29856288,29772941,29786509,29600329,29501045,29414705,29336420,29203502,29278202,29251702,29136199,29099748,29212116,29001067,28887197,28859711,28701424,
       28329125,28237205,28268208,28438476,28550723,28489954,28400727,28237879,28328458,28277196,28000073,27788382,27794910,27946559,28053433,28004548,27667118,27692143,27861861,27942580,27910435,27957678,27694934,27595934,27507644,27523933,27488208,27346955,27354395,26963746,26968665,26982476,27016121,27007531,26957309,27225080,27223867,27247032,27227305,27278068,27315586,27299800,27401190,27312444,27261435,27250192,27238481,27283039,27172034,
       27180573,27207015,27094230,27196807,27236538,27260668,27301840,27173944,27103625,27154456,27194506,27147528,27208651,26930811,27034293,27107984,27103947,27184193,27134820,27157784,27133451,26911782,26945503,26955897,26880228,26923360,26768968,26810398,26876897,26882673,27012014,27024549,27111360,27096876,27139352,27172587,27180794,27275638,27279471,27084330,27000548,26797662,26707551,26732585,26650447,26593652,26387661,26377988,26393473,
       26400532,26375210,26173802,26148824,26179523,26155698,26001323,26181210,26265973,26259295,26298438,26378295,26270115,26331666,26379669,26326462,26280785,26269936,26281443,26283163,26231931,26299392,26283179,26340543,26329180,26324896,26349887,26270430,26280177,26211982,26169741,26199159,26218347,26161638,26173593,26262208,26309868,26309130,26306964,26282329,26298451,26338818,26333796,26420537,26455056,26458638,26492124,26406604,26291665,
       26184610,26096298,26054496,26056292,26170709,26213922,26325484,26390902,26408600,26377500,26352082,26342511,26419211,26424289,26434415,26475720,26324173,26336777,26355507,26368789,26354997,26267657,25969782,26042249,26062445,26010778,25915750,25913699,25921165,26078913,26156405,26025767,25996451,25893095,25853565,25647368,25510781,25429847,25400501,25380509,25425493,25403686,25283315,25295259,25305094,25364175,25326902,25148774,25134999,
       25046850,25034898,25198812,25358771,25344647,25149116,25129071,25130090,25025207,25000665,24989105,24803695,24533132,24490973,24360637,24264072,24340723,24295230,24212222,24345505,24261564,24177908,24147601,24111781,24077136,24066070,24028417,23915314,23845689,23840519,23828839,23881369,23846122,23791018,23761609,23543090,23520585,23505635,22904552,22906181,22973351,22964255,22985956,22955683,22998261,23112245,23085831,23200515,23229433,
       23224892,23196408,23192493,23182855,23245115,23332885,23343869,23450385,23507868,23490677,23619306,23618882,23552760,23556326,23566010,23483424,23476645,23477070,23488364,23499926,23527866,23394654,23529802,23748412,24013064,23960963,23884877,23847927,23916737,23895888,23851464,23874691,23809606,23760049,23773333,23495776,23388491,23319834,23178573,23057004,23059947,22867290,22854763,22916003,22721794,22628543,22535716,22553593,22516951,
       22574153,22633612,22673882,22633129,22596627,22635993,22663433,22658253,22658770,22581040,22764499,22717761,22719677,22630173,22615911,22618390,22652357,22671355,22601940,22629359,22627683,22666530,22827333,22680484,22624936,22633886,22625355,22624924,22473919,22371871,22494761,22475048,22427062,22346151,22281366,22217707,22117299,21891098,21864518,21878323,21848344,21807441,21852923,21841733,21957377,21946395,22069080,21994960,22088255,
       22113824,22021240,22113387,22118212,21961097,21967459,22014806,21937456,21932855,21976441,21971752,21941178,21981529,21976512,21931033,22018516,22195456,22180222,22153897,22086923,21996276,21914653,21937324,21948872,21818399,21834294,21974575,22094493,22120314,22102883,22083894,22020392,22168055,22099390,21970431,21974177,21813275,21809784,21928939,21969170,21973257,21984224,21849181,21923788,21881406,22116269,22108651,22018041,21934094,
       21911632,21935216,21930884,21911995,21924074,21958736,21936573,21906371,21921341,21858399,21898705,21897194,21898529,21787559,21751782,21816343,21745015,21589622,21636719,21524100,21487944,21474257,21356900,21368371,21402675,21374947,21337919,21398650,21389075,21570899,21550860,21544546,21263947,21231384,21263396,21197922,20970800,21120590,21080383,20948420,20968733,20995686,21078145,21086265,21077568,21051475,20974707,20961858,20939184,
       20979301,20972222,20877742,20842750,20767191,20755309,20913720,20916362,21040413,21092353,21058859,21094947,21125363,21260289,21232942,21023448,20948901,20955956,21065387,21006452,20972629,20980216,21074139,21074864,21057971,21004117,20850332,20835824,20910441,20907800,20894361,20905437,21003582,20981069,20971210,20946131,20993041,20901122,20850198,20826712,20804664,20813786,20812872,20823626,20863587,20918346,20908080,20874807,20829587,
       20866136,20909626};
     diff = difficultiesforv5_7[(height) - 27190];

   }else if(height > 27776 && height <= 28081){
     int difficultiesforv5_8 [305] = {20901777,20812450,20770179,20778528,20805588,20826900,20797582,20743200,20850932,20822324,20816252,20751799,20765567,20851291,20937379,21014245,21031277,20990723,21090538,21025644,20974561,20937222,20901731,20752579,20768123,20726943,20718119,20629360,20598518,20584163,20718124,20681825,20596027,20390885,20454925,20458236,20645797,20646167,20463430,20493117,20535679,20437445,20388966,20369789,20397601,
       20561360,20437320,20511669,20530919,20598955,20685229,20767006,20691569,20611676,20320838,20341836,20378310,20385594,20300920,20064566,20131023,20264235,20244747,20252484,20248571,20206999,20187887,20250677,20421894,20401875,20400842,20534157,20577062,20360695,20517080,20774645,20746970,20832311,20788881,20813420,20871625,20988069,20993865,21046147,21080766,21104526,21078878,21040997,21011834,20990101,21204407,21293958,21228654,21243703,
       21174479,21190036,21228841,21238301,21436990,21422175,21382748,21961575,22033308,21946884,21918242,21873717,21904590,21905424,21878302,21856859,21825139,21857704,21850183,21841601,21888636,21836489,21763614,21749438,21658859,21620438,21578090,21402350,21462373,21414762,21469813,21475802,21432734,21487200,21474197,21565577,21659610,21660186,21692428,21848203,21845123,21828882,21810596,21866301,21926412,21917503,21894492,21884045,21916568,
       21949105,22082563,22292807,22313422,22566104,22713886,22767296,22931414,23049989,23049149,23312286,23285465,23334978,23495951,23606883,23702635,23692514,23764590,23637811,23539729,23634204,23511673,23579340,23450907,23347104,23382427,23455810,23448459,23423665,23495141,23446333,23564810,23628317,23650568,23631978,23714655,23805767,23803377,23816158,23820229,23873303,23729194,23971965,23932086,23941370,24060169,24262993,24406014,24407338,
       24303887,24393031,24551767,24572737,24689954,24798930,25179100,25010976,24992173,25030731,25053952,24937334,24890837,24868714,24892149,24879570,24963261,24940843,24913998,25035926,25049067,25072516,25405396,25450646,25477555,25550516,25677694,25698357,25658907,25689147,25682860,25756472,25824651,25774849,25828220,25931945,25961982,26041417,26193243,26346293,26264200,26467814,26674696,26760361,26824640,26817462,26736304,26735187,26751096,
       26909884,26938277,27079718,27266544,27270962,27542476,27477348,27339682,27269895,27420473,27488534,27774781,27754481,27705741,27766423,27750719,27866048,27991180,27942710,27912934,27777551,27687280,27657372,27726862,27479695,27574936,27631995,27716459,27759322,27770531,27819677,28028958,28035829,28030271,28203323,28483389,28553748,28692072,28751155,28760057,28950802,28932478,28951870,28879474,28928127,28784929,28623026,28646626,28672652,
       28650829,29263063,29308924,29245159,29341984,29848655,29853856,29864971,30018155,29929556,30006694,29868249,29869443,29908954,29965220};
     diff = difficultiesforv5_8[(height) - 27777];

   }else if(height > 28081 && height <= 29629){
     int difficultiesforv5_9 [1548] = {30160227,30243252,30220944,30202791,30240047,30469520,30461101,30647880,30668835,30410277,30517332,30428473,30372081,30461022,30510086,30550666,30514963,30481048,31016506,31192903,31296733,31379730,31585718,31510102,31570468,31644161,31624116,31728581,31618849,31852841,31838160,31700529,31540380,31441748,31425265,31467565,31487848,31516823,31431360,31401872,31591761,31806634,31893287,31691118,31614041,
       31483495,31607994,31550925,31295723,31340034,31446646,31529491,31518237,31586715,31620641,31825273,31944438,31864215,31854507,31822972,31813592,31861618,31695617,31675245,31506260,31588905,31907412,31890530,31911385,31951761,31995734,31996996,31882951,32028319,32151477,32236198,32355330,32398855,32282028,32394855,32395893,32623024,32622371,31938030,31967519,32108917,32225022,32616362,32641631,32698126,32832809,32761608,33218130,33264308,
       33372779,33187140,33313585,33421010,33431129,33391206,33684973,33594012,33676820,33562573,33614038,33626321,33860719,34041189,34519623,34606667,34552253,34541988,34824483,35559813,35571928,35435683,35544495,35762139,35761089,35832125,35676731,35766622,35935031,35856926,35786130,35749616,35767414,36051959,36057792,36098639,36199160,36338961,36513274,36537831,36563868,36568946,36630444,36684100,36829329,36831036,37005748,37311106,37378547,
       37610621,37563472,37283628,37552225,37494437,37559523,37396793,37322772,37332499,37366239,37232126,36895664,36901360,36922711,36946122,37039692,37220543,37190951,37217772,37281976,37416357,37503236,37536622,37406464,37359307,37499563,37475628,37624095,37574723,37823301,37962389,37987719,38517229,38521511,38666764,38678333,38579914,38093914,38130175,37930483,37998222,37977386,38015691,38031706,37954851,38027309,38060998,37976098,37854493,
       37817270,37935582,37891653,37977357,37907881,37878171,37880391,37946861,37932972,38034401,37899888,37978283,38017047,38110406,38079420,38009054,38123820,38234011,38442261,38506561,38476964,38468048,38487501,38811367,38864625,39100618,39285442,39145128,39468641,39496786,39460427,39505701,39790230,39470439,39469078,39422930,39422703,39186124,39282050,39492388,39088909,39165614,39230446,39279589,39122321,38846967,39210296,39211468,39241776,
       39168120,39144901,39197913,39296562,39226957,39538796,39606535,39761945,39834356,39554172,39551619,38416333,38764630,37989788,37953790,38095085,38150625,38256231,37932136,37842732,37860317,37738668,37743666,37619846,37644290,37474067,37532879,37384054,37420508,37238912,37276858,37269257,37247404,37316569,36931843,37159743,37187543,37087964,37203623,37290631,37229896,37132814,37274090,37337058,37259972,36896750,36892479,36940571,36958845,
       36628866,36352056,36491194,36464788,36466009,36457402,36541846,36321579,36290391,35991887,35942448,35621810,35848572,35237597,35310094,35395728,35506173,35612196,35605282,35460156,35466401,35537617,35655390,35834725,35559267,35750333,35923428,35902070,35923355,36259894,36043648,35688237,35608607,35534853,35649302,35532678,35384590,35398189,35070642,34915583,34938497,34851453,34880129,34428421,34330564,34270956,34485949,34496898,34573310,
       34367076,34314252,34409092,34422264,34504832,34452319,34493246,34213997,34264106,33845719,33663971,33649039,33602884,33641524,33762432,33510058,33390941,33344508,33283160,32831538,32890910,32898297,32705214,32697199,32685733,32709290,32769637,32692848,32944929,32920977,32715369,33030100,33115048,32961522,32991163,33033494,33102165,33217742,33173227,33083094,33030777,33087159,33069507,32968914,32828804,32828473,32856540,32933567,32998578,
       33122900,33026220,32748321,32895106,32894175,32921215,32894160,32892259,32922719,33045856,33031328,33117810,32807794,32686895,32747275,32899703,32727121,32909613,32979710,33313396,33300400,33333519,33344332,33384396,33395657,33183481,33175678,33185605,33304597,33179983,32917361,32912080,32951911,33103322,33204334,33327582,33357928,33314423,33359422,33375581,33092233,33103179,33186293,33305185,33211315,32982722,32842517,32875975,33055084,
       33026746,33108148,32941742,32955877,32916313,33239229,33165249,32958809,32895078,32971279,32970794,33078463,33096819,33142430,33183148,33213773,33195872,33431136,33415263,33433824,33463500,33507798,33338161,33464467,33444338,33590590,33606975,33639798,33630141,33695931,33859137,33714189,33580418,33626347,33679228,33703634,33739984,33847914,33821138,33835208,33796111,33600279,33726149,33714091,33669250,33769692,33766603,33839669,33862544,
       34127912,34092024,34096332,34145399,34096019,34229291,34227044,34253947,34248739,34104949,34101300,33905251,33787261,33787115,33780408,33753018,33660501,33605597,33809663,33712959,33812249,33898301,34026651,34103132,34130414,34045561,34193405,34511962,34507698,34602092,34568233,34504155,34461383,33975165,33890314,33735434,33738333,33701359,33717580,33836602,33830185,33660322,33720521,33753995,33790123,33776088,33717066,33619672,33611187,
       33507107,33439466,33345380,33495548,33443284,33498977,33593695,33263447,33147376,33143650,33161096,33160160,33151977,32977038,33057181,33099940,33024111,33018213,33030619,32457090,32534416,32492152,32094567,31891690,31859390,31880601,31943802,31692947,31678517,31656185,31679802,31548607,31405511,31357139,31255410,31228152,31138872,31112828,31105720,30701517,30630083,30599235,30524812,30584358,30519289,30098711,30149271,29815520,29794207,
       29968277,30007711,30045343,30080443,30178119,30048343,30104229,30242078,29890241,29827890,29684651,29515775,29511860,29491851,29489401,29464638,29483123,29503742,29499733,29341258,29364626,29046924,29035307,29031211,29033678,28976849,29002474,29544921,29489528,29908751,29972186,29964838,29967278,29906958,30040350,30108041,30119968,30135516,29996262,29977928,29974154,30042865,29994563,30020283,30019692,30145573,29979021,29975737,29702261,
       29676100,29887494,29858011,29552920,29628136,29445378,29433549,29456856,29537229,29497190,29355071,29430752,29673436,29553810,29487104,29472411,29592671,29680417,29648583,29617709,29629004,29385287,29298535,29440237,29503817,29641271,29558668,29770545,29785635,30259331,30264463,30058136,29830432,29666977,29765760,29893400,29908135,29795927,29762519,29665321,29899506,29865991,29898127,29900852,29870707,29830283,29917047,29951713,29935699,
       29808434,29776390,29814947,29940376,29947617,30191889,30088119,30091727,30159145,30103680,30449169,30507334,30551867,30473302,30420256,30355728,30521374,30607058,30647898,30506938,30485266,30539555,30408055,30612025,30578462,30997858,31205742,31138199,31134707,31219468,31002428,31229481,31439029,31451069,31490737,31869648,31825922,31806377,31700170,31664788,31545160,31491631,31489861,31525767,31418350,31378737,31369318,31111629,31070566,
       31113998,31004575,30952163,30901467,30905908,30962573,31023963,30806802,30733779,30501283,30650753,30616888,30535372,30258915,30142521,30062983,30034463,30118577,30385383,30246402,30214173,30271523,30325500,30274494,30057462,30057309,30101525,30085796,30338249,30450400,30465456,30468931,30472132,30431351,30346699,30225017,30092658,30089257,30040136,30030888,29932123,30044157,29818996,29804759,29776333,29898470,30170845,30029085,29975398,
       29733523,29649558,29625698,29692799,29703936,29694880,29658662,29916095,29856577,29845895,29751360,29729738,29831657,29951512,29973440,29765023,29754686,29773048,29959056,29840574,29828609,29941211,29956091,30214535,30303721,30283950,30261642,29845140,29838662,29885623,29832250,29825356,29796709,29721203,29740765,29755719,29698335,29688879,29917716,29880831,29791734,29885847,29830420,29848793,29837280,29800773,29752373,29725980,29846666,
       29717104,29640677,29618657,29570707,29520487,29294337,29260768,29275936,29440604,29486509,29474265,29505675,29420313,29366256,29333519,29248724,29187139,29244546,29159602,29167363,29159977,29123386,29081092,29062717,29023799,29023022,28927192,29023287,29146709,29095917,29012633,29026963,29109383,29141535,29094532,29059941,28926336,28879778,28834755,28705940,28701881,28786919,28350993,28344737,28263194,28179424,28107575,28134524,28135267,
       28555679,28613741,28720520,28641227,28672101,28630939,28611274,28658183,28758199,28738045,28735879,28736600,28723082,28696885,28816491,28547364,28500660,28520598,28491498,28445801,28729138,28640407,28656812,28886175,28988104,28968121,28902940,28941164,28904816,29065173,28869663,28910512,28953920,28917336,28851379,29282792,29263045,29341222,29714654,29680045,29712883,29618345,29600741,29828862,29772584,29770427,29758366,29919981,30058036,
       30093615,30124619,30046579,30179771,30228115,30107847,30520993,30494376,30503232,30547998,30518405,30414084,31018632,30998199,31341763,31350809,31333484,31237231,31306526,31288020,31307607,31422309,31338843,31361389,31667079,31638918,31701771,32011718,31906161,31730404,31757707,31817816,31880118,31717059,31638367,31829563,31854901,32253511,32219331,32200066,32297089,32497515,32574097,32438633,32519762,32523640,32421891,32316001,32142232,
       32112127,32043469,31987818,31989667,32065332,32208293,32396920,32315446,32454899,32411563,32558361,32533346,32529447,32704741,32675976,33026668,33107659,32906750,32894557,33191939,33196104,33421494,33355450,33356502,33317093,33223613,33379360,33388142,33383459,33393080,33328862,33272579,33312628,33457872,33487693,33595441,33550458,33719984,33884553,33870187,33882405,34007453,34160110,34168706,34139947,34150016,34072384,34161098,34438818,
       34625197,34590313,34576827,34570897,34709239,34607774,34739441,34602252,34242667,34056976,34087415,33973389,33970602,34003568,34232980,34309387,34553625,34573069,34633041,34608475,34599562,34532403,34823173,34715649,34576844,34744802,34791066,34841910,34862777,34935357,34903731,34948921,34878264,34923074,34989761,35099329,35097663,35074254,35209408,35300875,35212671,34804598,34612940,34717098,34819248,34667942,34884981,34711392,34716097,
       34777545,34597096,34549156,34525599,34517052,34939964,34981278,35028721,34912344,34740504,34769041,34794082,34836666,34764740,35060099,34830614,34997467,35095526,34981455,34972409,34619996,34546345,34550401,34814538,34689847,34887231,34952060,34910926,35014339,35239483,35400500,35673509,35719584,35727052,35885027,36020232,36071950,35901172,35726060,35754979,36016512,35992584,35998379,35940182,35922641,35755903,35626098,35683971,35637227,
       35611660,35613808,35764331,35609852,35655052,35587515,35431239,35471973,35564087,35919924,35803938,35738437,35626268,35487333,35768610,35863980,36226705,36325536,36390697,36366822,36382566,36350730,36366041,36343044,36358987,36143265,36222308,36392514,36566163,36547682,36546551,36931840,36998912,36923681,36965011,36998724,36836273,36854356,36899875,36875498,36830781,36861252,36833249,37388989,37394314,37384903,37424072,37455860,37462951,
       37712846,37588993,37519314,37609891,37614488,37211011,37078138,37141375,37123364,37181946,37159185,37031383,37099416,37048099,37167427,36824973,37028615,37156565,37198476,37285933,37354445,37490282,37519737,37537951,37456700,37466338,37510124,37231963,37382995,37053218,37043721,37148311,37083847,36906838,37047833,36901502,36837937,36360706,36362962,36390792,36330721,36537514,36554989,36652268,36529046,36450710,36576973,36552993,36240157,
       36306373,36244741,36430729,36635863,36691376,36589127,36762537,36776303,36561448,37198069,37224672,37367752,37538273,37707919,37575343,37574747,37604638,37527044,37637155,37574039,37527968,37427024,37449944,37332203,37271719,37227435,37223530,37160922,37227866,37334955,37371401,37831992,38019601,37980054,38157295,37999228,37845051,38028842,38035695,37737882,37649457,37703269,37841674,37787099,37772891,37490523,37540717,37373406,37451071,
       37507410,37605473,37661322,37691913,37674266,37740533,38137038,38192868,38355410,38337672,38341825,38482344,38499472,38500957,38514639,38475372,38483647,38560770,38643565,38335371,38193862,38350058,38397385,38206922,38246412,38257478,38366630,38580185,38609195,38334017,38447174,38404197,38316026,38367802,38402813,38434862,38501483,38537773,38670165,38723167,38888393,38929572,39108853,38893399,39159449,39295050,39317436,39362045,39359393,
       39507604,39346137,39227416,39098436,39155885,39078337,38646546,38654109,38772142,38679732,38887627,38788506,38824928,38833243,38959597,39327826,39389502,39505384,39532241,39375607,39282286,39452050,39475977,39326869,39359043,39366421,39467864,39511637,39443052,39577585,39648787,39768139,39674746,39898459,39648202,39868003,39817142,39816082,39915166,39935091,39993756,40068993,40139595,40038324,40036160,40026771,40207256,40342824,40472843,
       40239712,40026537,40001907,40064022,40367213,40313528,40275208,40340926,40145967,40072847,39933809,39819091,39905493,39998589,40213280,40281367,40287534,40333244,40324948,40307735,40266348,40421767,40375414,40551351,41009143,41244248,41266740,41388192,41254714,41197114,41309623,41380250,41450904,41386781,41359328,41355149,41412141,41399667,41455018,41560818,41779206,41730431,41734896,41763496,41813598,41827395,41819024,41784792,41868460,
       41968342,41881583,41809199,41788954,41884014,41960917,41912118,42043384,42317233,42496160,42347312,42355455,42151172,42130516,42099229,42091994,41537306,41761820,41375150,41500297,41392617,41459814,41546790,41736395,41718567,42033827,41945392,42007645,41912295,42061384,41849378,42170197,42166055,42238672,42431901,42296747,42708662,42628205,42580400,42521655,42777674,42897507,42925558,43246612,43173383,43307343,43091167,42952643,42874761,
       42710748,42741920,42718018,42771351,42892592,43154536,43149426,42936760,42956368,42797786,42896541,42941937,42812142,43062240,43023589,42982933,42960669,43025967,42971972,43422527,43454206,43588773,43761113,43944767,44014951,43973590,44129372,43996963,44179606,44394463,44257766,44058764,44056845,43964966,43834176,43741629,43777937,43811883,43873000,43971058,44113822,44418716,44008146,44033881,44036472,44011981,44065167,44061294,44027949,
       44150801,44197742,44328488,44582656,44639015,44740066,44837768,44979805,45021655,44723643,44707390,44724935,44442938,44472925,44404347,44227167,43825534,43752062,43792289,43797621,43748247,44159779,44272005,44391480,44228173,44024581,44087639,44370252,44257159,44262822,44443566,44522737,44573394,};
     diff = difficultiesforv5_9[(height) - 28082];

   }else{
     diff = next_difficulty(std::move(timestamps), std::move(difficulties), target,height - 1);

   }
  }else if(version >= 7){
     diff = next_difficulty_v3(std::move(timestamps), std::move(difficulties), target,height - 1);
  }
  m_difficulty_for_next_block_top_hash = top_hash;
  m_difficulty_for_next_block = diff;
  return diff;
}
//------------------------------------------------------------------
// This function removes blocks from the blockchain until it gets to the
// position where the blockchain switch started and then re-adds the blocks
// that had been removed.
bool Blockchain::rollback_blockchain_switching(std::list<block>& original_chain, uint64_t rollback_height)
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);

  // fail if rollback_height passed is too high
  if (rollback_height > m_db->height())
  {
    return true;
  }

  m_timestamps_and_difficulties_height = 0;

  // remove blocks from blockchain until we get back to where we should be.
  while (m_db->height() != rollback_height)
  {
    pop_block_from_blockchain();
  }

  // make sure the hard fork object updates its current version
  m_hardfork->reorganize_from_chain_height(rollback_height);

  //return back original chain
  for (auto& bl : original_chain)
  {
    block_verification_context bvc = boost::value_initialized<block_verification_context>();
    bool r = handle_block_to_main_chain(bl, bvc);
    CHECK_AND_ASSERT_MES(r && bvc.m_added_to_main_chain, false, "PANIC! failed to add (again) block while chain switching during the rollback!");
  }

  m_hardfork->reorganize_from_chain_height(rollback_height);

  MINFO("Rollback to height " << rollback_height << " was successful.");
  if (original_chain.size())
  {
    MINFO("Restoration to previous blockchain successful as well.");
  }
  return true;
}
//------------------------------------------------------------------
// This function attempts to switch to an alternate chain, returning
// boolean based on success therein.
bool Blockchain::switch_to_alternative_blockchain(std::list<blocks_ext_by_hash::iterator>& alt_chain, bool discard_disconnected_chain)
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);

  m_timestamps_and_difficulties_height = 0;

  // if empty alt chain passed (not sure how that could happen), return false
  CHECK_AND_ASSERT_MES(alt_chain.size(), false, "switch_to_alternative_blockchain: empty chain passed");

  // verify that main chain has front of alt chain's parent block
  if (!m_db->block_exists(alt_chain.front()->second.bl.prev_id))
  {
    LOG_ERROR("Attempting to move to an alternate chain, but it doesn't appear to connect to the main chain!");
    return false;
  }

  // pop blocks from the blockchain until the top block is the parent
  // of the front block of the alt chain.
  std::list<block> disconnected_chain;
  while (m_db->top_block_hash() != alt_chain.front()->second.bl.prev_id)
  {
    block b = pop_block_from_blockchain();
    disconnected_chain.push_front(b);
  }

  auto split_height = m_db->height();

  //connecting new alternative chain
  for(auto alt_ch_iter = alt_chain.begin(); alt_ch_iter != alt_chain.end(); alt_ch_iter++)
  {
    auto ch_ent = *alt_ch_iter;
    block_verification_context bvc = boost::value_initialized<block_verification_context>();

    // add block to main chain
    bool r = handle_block_to_main_chain(ch_ent->second.bl, bvc);

    // if adding block to main chain failed, rollback to previous state and
    // return false
    if(!r || !bvc.m_added_to_main_chain)
    {
      MERROR("Failed to switch to alternative blockchain");

      // rollback_blockchain_switching should be moved to two different
      // functions: rollback and apply_chain, but for now we pretend it is
      // just the latter (because the rollback was done above).
      rollback_blockchain_switching(disconnected_chain, split_height);

      // FIXME: Why do we keep invalid blocks around?  Possibly in case we hear
      // about them again so we can immediately dismiss them, but needs some
      // looking into.
      add_block_as_invalid(ch_ent->second, get_block_hash(ch_ent->second.bl));
      MERROR("The block was inserted as invalid while connecting new alternative chain, block_id: " << get_block_hash(ch_ent->second.bl));
      m_alternative_chains.erase(*alt_ch_iter++);

      for(auto alt_ch_to_orph_iter = alt_ch_iter; alt_ch_to_orph_iter != alt_chain.end(); )
      {
        add_block_as_invalid((*alt_ch_to_orph_iter)->second, (*alt_ch_to_orph_iter)->first);
        m_alternative_chains.erase(*alt_ch_to_orph_iter++);
      }
      return false;
    }
  }

  // if we're to keep the disconnected blocks, add them as alternates
  if(!discard_disconnected_chain)
  {
    //pushing old chain as alternative chain
    for (auto& old_ch_ent : disconnected_chain)
    {
      block_verification_context bvc = boost::value_initialized<block_verification_context>();
      bool r = handle_alternative_block(old_ch_ent, get_block_hash(old_ch_ent), bvc);
      if(!r)
      {
        MERROR("Failed to push ex-main chain blocks to alternative chain ");
        // previously this would fail the blockchain switching, but I don't
        // think this is bad enough to warrant that.
      }
    }
  }

  //removing alt_chain entries from alternative chains container
  for (auto ch_ent: alt_chain)
  {
    m_alternative_chains.erase(ch_ent);
  }

  m_hardfork->reorganize_from_chain_height(split_height);

  MGINFO_GREEN("REORGANIZE SUCCESS! on height: " << split_height << ", new blockchain size: " << m_db->height());
  return true;
}
//------------------------------------------------------------------
// This function calculates the difficulty target for the block being added to
// an alternate chain.
difficulty_type Blockchain::get_next_difficulty_for_alternative_chain(const std::list<blocks_ext_by_hash::iterator>& alt_chain, block_extended_info& bei) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  std::vector<uint64_t> timestamps;
  std::vector<difficulty_type> cumulative_difficulties;

  // if the alt chain isn't long enough to calculate the difficulty target
  // based on its blocks alone, need to get more blocks from the main chain
  if(alt_chain.size()< DIFFICULTY_BLOCKS_COUNT)
  {
    CRITICAL_REGION_LOCAL(m_blockchain_lock);

    // Figure out start and stop offsets for main chain blocks
    size_t main_chain_stop_offset = alt_chain.size() ? alt_chain.front()->second.height : bei.height;
    size_t main_chain_count = DIFFICULTY_BLOCKS_COUNT - std::min(static_cast<size_t>(DIFFICULTY_BLOCKS_COUNT), alt_chain.size());
    main_chain_count = std::min(main_chain_count, main_chain_stop_offset);
    size_t main_chain_start_offset = main_chain_stop_offset - main_chain_count;

    if(!main_chain_start_offset)
      ++main_chain_start_offset; //skip genesis block

    // get difficulties and timestamps from relevant main chain blocks
    for(; main_chain_start_offset < main_chain_stop_offset; ++main_chain_start_offset)
    {
      timestamps.push_back(m_db->get_block_timestamp(main_chain_start_offset));
      cumulative_difficulties.push_back(m_db->get_block_cumulative_difficulty(main_chain_start_offset));
    }

    // make sure we haven't accidentally grabbed too many blocks...maybe don't need this check?
    CHECK_AND_ASSERT_MES((alt_chain.size() + timestamps.size()) <= DIFFICULTY_BLOCKS_COUNT, false, "Internal error, alt_chain.size()[" << alt_chain.size() << "] + vtimestampsec.size()[" << timestamps.size() << "] NOT <= DIFFICULTY_WINDOW[]" << DIFFICULTY_BLOCKS_COUNT);

    for (auto it : alt_chain)
    {
      timestamps.push_back(it->second.bl.timestamp);
      cumulative_difficulties.push_back(it->second.cumulative_difficulty);
    }
  }
  // if the alt chain is long enough for the difficulty calc, grab difficulties
  // and timestamps from it alone
  else
  {
    timestamps.resize(static_cast<size_t>(DIFFICULTY_BLOCKS_COUNT));
    cumulative_difficulties.resize(static_cast<size_t>(DIFFICULTY_BLOCKS_COUNT));
    size_t count = 0;
    size_t max_i = timestamps.size()-1;
    // get difficulties and timestamps from most recent blocks in alt chain
    for(auto it: boost::adaptors::reverse(alt_chain))
    {
      timestamps[max_i - count] = it->second.bl.timestamp;
      cumulative_difficulties[max_i - count] = it->second.cumulative_difficulty;
      count++;
      if(count >= DIFFICULTY_BLOCKS_COUNT)
        break;
    }
  }

  // FIXME: This will fail if fork activation heights are subject to voting
  size_t target =  DIFFICULTY_TARGET_V2;
  size_t height = alt_chain.size();
  // calculate the difficulty target for the block and return it
  difficulty_type diff = 0;
  if(get_current_hard_fork_version() < 5)
    diff = next_difficulty(timestamps, cumulative_difficulties, target,height - 1);
  if(get_current_hard_fork_version() >= 5 && get_current_hard_fork_version() < 7)
    if(height >= 24860 && height <= 24922){
        diff = 10000000;
      }

    diff =  next_difficulty(timestamps, cumulative_difficulties, target,height - 1 );
  if(get_current_hard_fork_version() >= 7)
    diff =  next_difficulty_v3(timestamps, cumulative_difficulties, target,height - 1);

  return diff;

}
//------------------------------------------------------------------
// This function does a sanity check on basic things that all miner
// transactions have in common, such as:
//   one input, of type txin_gen, with height set to the block's height
//   correct miner tx unlock time
//   a non-overflowing tx amount (dubious necessity on this check)
bool Blockchain::prevalidate_miner_transaction(const block& b, uint64_t height)
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CHECK_AND_ASSERT_MES(b.miner_tx.vin.size() == 1, false, "coinbase transaction in the block has no inputs");
  CHECK_AND_ASSERT_MES(b.miner_tx.vin[0].type() == typeid(txin_gen), false, "coinbase transaction in the block has the wrong type");
  if(boost::get<txin_gen>(b.miner_tx.vin[0]).height != height)
  {
    MWARNING("The miner transaction in block has invalid height: " << boost::get<txin_gen>(b.miner_tx.vin[0]).height << ", expected: " << height);
    return false;
  }
  MDEBUG("Miner tx hash: " << get_transaction_hash(b.miner_tx));
  CHECK_AND_ASSERT_MES(b.miner_tx.unlock_time == height + CRYPTONOTE_MINED_MONEY_UNLOCK_WINDOW, false, "coinbase transaction transaction has the wrong unlock time=" << b.miner_tx.unlock_time << ", expected " << height + CRYPTONOTE_MINED_MONEY_UNLOCK_WINDOW);

  //check outs overflow
  //NOTE: not entirely sure this is necessary, given that this function is
  //      designed simply to make sure the total amount for a transaction
  //      does not overflow a uint64_t, and this transaction *is* a uint64_t...
  if(!check_outs_overflow(b.miner_tx))
  {
    MERROR("miner transaction has money overflow in block " << get_block_hash(b));
    return false;
  }

  return true;
}
//------------------------------------------------------------------
// This function validates the miner transaction reward
bool Blockchain::validate_miner_transaction(const block& b, size_t cumulative_block_size, uint64_t fee, uint64_t& base_reward, uint64_t already_generated_coins, bool &partial_block_reward, uint8_t version)
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  //validate reward
  uint64_t money_in_use = 0;
  for (auto& o: b.miner_tx.vout)
    money_in_use += o.amount;
  partial_block_reward = false;

  if (version == 4) {
    for (auto &o: b.miner_tx.vout) {
      if (!is_valid_decomposed_amount(o.amount)) {
        MERROR_VER("miner tx output " << print_money(o.amount) << " is not a valid decomposed amount");
        return false;
      }
    }
  }

  std::vector<size_t> last_blocks_sizes;
  get_last_n_blocks_sizes(last_blocks_sizes, CRYPTONOTE_REWARD_BLOCKS_WINDOW);
  if (!get_block_reward(epee::misc_utils::median(last_blocks_sizes), cumulative_block_size, already_generated_coins, fee, base_reward, version,m_db->height()))
  {
    MERROR_VER("block size " << cumulative_block_size << " is bigger than allowed for this blockchain");
    return false;
  }
  if(base_reward + fee < money_in_use && version > 1)
  {
    MERROR_VER("coinbase transaction spend too much money (" << print_money(money_in_use) << "). Block reward is " << print_money(base_reward + fee) << "(" << print_money(base_reward) << "+" << print_money(fee) << ")" << " AGC: " << print_money(already_generated_coins));
    return false;
  }
  if(version >= 7){
      CHECK_AND_ASSERT_MES(money_in_use - fee <= base_reward, false, "base reward calculation bug");
    if(base_reward + fee != money_in_use){
      partial_block_reward = true;
    base_reward = money_in_use - fee;
	}
}
  return true;
}
//------------------------------------------------------------------
// get the block sizes of the last <count> blocks, and return by reference <sz>.
void Blockchain::get_last_n_blocks_sizes(std::vector<size_t>& sz, size_t count) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);
  auto h = m_db->height();

  // this function is meaningless for an empty blockchain...granted it should never be empty
  if(h == 0)
    return;

  m_db->block_txn_start(true);
  // add size of last <count> blocks to vector <sz> (or less, if blockchain size < count)
  size_t start_offset = h - std::min<size_t>(h, count);
  for(size_t i = start_offset; i < h; i++)
  {
    sz.push_back(m_db->get_block_size(i));
  }
  m_db->block_txn_stop();
}
//------------------------------------------------------------------
uint64_t Blockchain::get_current_cumulative_blocksize_limit() const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  return m_current_block_cumul_sz_limit;
}
//------------------------------------------------------------------
uint64_t Blockchain::get_current_cumulative_blocksize_median() const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  return m_current_block_cumul_sz_median;
}
//------------------------------------------------------------------
//TODO: This function only needed minor modification to work with BlockchainDB,
//      and *works*.  As such, to reduce the number of things that might break
//      in moving to BlockchainDB, this function will remain otherwise
//      unchanged for the time being.
//
// This function makes a new block for a miner to mine the hash for
//
// FIXME: this codebase references #if defined(DEBUG_CREATE_BLOCK_TEMPLATE)
// in a lot of places.  That flag is not referenced in any of the code
// nor any of the makefiles, howeve.  Need to look into whether or not it's
// necessary at all.
bool Blockchain::create_block_template(block& b, const account_public_address& miner_address, difficulty_type& diffic, uint64_t& height, uint64_t& expected_reward, const blobdata& ex_nonce)
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  size_t median_size;
  uint64_t already_generated_coins;

  CRITICAL_REGION_BEGIN(m_blockchain_lock);
  height = m_db->height();

  b.major_version = m_hardfork->get_current_version();
  if (b.major_version >= BLOCK_MAJOR_VERSION_2 && b.major_version < BLOCK_MAJOR_VERSION_7) {
	  b.minor_version = 0;
	  b.parent_block.major_version = BLOCK_MAJOR_VERSION_1;
	  b.parent_block.minor_version = 1;
	  b.parent_block.number_of_transactions = 1;
	  //create MM tag
	  tx_extra_merge_mining_tag mm_tag = boost::value_initialized<decltype(mm_tag)>();
	  if (!append_mm_tag_to_extra(b.parent_block.miner_tx.extra, mm_tag)) {
		  MERROR("Failed to append merge mining tag to extra of the parent block miner transaction");
		  return false;
	  }
  } else if (b.major_version == BLOCK_MAJOR_VERSION_1) {
    b.minor_version = 0;
  } else {
    b.minor_version = m_hardfork->get_ideal_version();
  }

  b.prev_id = get_tail_id();
  b.timestamp = time(NULL);

  uint64_t median_ts;
  if (!check_block_timestamp(b, median_ts))
  {
    b.timestamp = median_ts;
  }

  diffic = get_difficulty_for_next_block();
  CHECK_AND_ASSERT_MES(diffic, false, "difficulty overhead.");

  median_size = m_current_block_cumul_sz_limit / 2;
  already_generated_coins = m_db->get_block_already_generated_coins(height - 1);

  CRITICAL_REGION_END();

  size_t txs_size;
  uint64_t fee;
  if (!m_tx_pool.fill_block_template(b, median_size, already_generated_coins, txs_size, fee, expected_reward, m_hardfork->get_current_version(),height))
  {
    return false;
  }
#if defined(DEBUG_CREATE_BLOCK_TEMPLATE)
  size_t real_txs_size = 0;
  uint64_t real_fee = 0;
  CRITICAL_REGION_BEGIN(m_tx_pool.m_transactions_lock);
  for(crypto::hash &cur_hash: b.tx_hashes)
  {
    auto cur_res = m_tx_pool.m_transactions.find(cur_hash);
    if (cur_res == m_tx_pool.m_transactions.end())
    {
      LOG_ERROR("Creating block template: error: transaction not found");
      continue;
    }
    tx_memory_pool::tx_details &cur_tx = cur_res->second;
    real_txs_size += cur_tx.blob_size;
    real_fee += cur_tx.fee;
    if (cur_tx.blob_size != get_object_blobsize(cur_tx.tx))
    {
      LOG_ERROR("Creating block template: error: invalid transaction size");
    }
    if (cur_tx.tx.version == 1)
    {
      uint64_t inputs_amount;
      if (!get_inputs_money_amount(cur_tx.tx, inputs_amount))
      {
        LOG_ERROR("Creating block template: error: cannot get inputs amount");
      }
      else if (cur_tx.fee != inputs_amount - get_outs_money_amount(cur_tx.tx))
      {
        LOG_ERROR("Creating block template: error: invalid fee");
      }
    }
    else
    {
      if (cur_tx.fee != cur_tx.tx.rct_signatures.txnFee)
      {
        LOG_ERROR("Creating block template: error: invalid fee");
      }
    }
  }
  if (txs_size != real_txs_size)
  {
    LOG_ERROR("Creating block template: error: wrongly calculated transaction size");
  }
  if (fee != real_fee)
  {
    LOG_ERROR("Creating block template: error: wrongly calculated fee");
  }
  CRITICAL_REGION_END();
  MDEBUG("Creating block template: height " << height <<
      ", median size " << median_size <<
      ", already generated coins " << already_generated_coins <<
	  ", expected reward " << expected_reward <<
      ", transaction size " << txs_size <<
      ", fee " << fee);
#endif

  /*
   two-phase miner transaction generation: we don't know exact block size until we prepare block, but we don't know reward until we know
   block size, so first miner transaction generated with fake amount of money, and with phase we know think we know expected block size
   */
  //make blocks coin-base tx looks close to real coinbase tx to get truthful blob size
  uint8_t hf_version = m_hardfork->get_current_version();
  size_t max_outs = hf_version >= 4 ? 1 : 11;
  bool r = construct_miner_tx(height, median_size, already_generated_coins, txs_size, fee, miner_address, b.miner_tx, ex_nonce, max_outs, hf_version);
  CHECK_AND_ASSERT_MES(r, false, "Failed to construct miner tx, first chance");
  size_t cumulative_size = txs_size + get_object_blobsize(b.miner_tx);
#if defined(DEBUG_CREATE_BLOCK_TEMPLATE)
  MDEBUG("Creating block template: miner tx size " << get_object_blobsize(b.miner_tx) <<
      ", cumulative size " << cumulative_size);
#endif
  for (size_t try_count = 0; try_count != 10; ++try_count)
  {
    r = construct_miner_tx(height, median_size, already_generated_coins, cumulative_size, fee, miner_address, b.miner_tx, ex_nonce, max_outs, hf_version);

    CHECK_AND_ASSERT_MES(r, false, "Failed to construct miner tx, second chance");
    size_t coinbase_blob_size = get_object_blobsize(b.miner_tx);
    if (coinbase_blob_size > cumulative_size - txs_size)
    {
      cumulative_size = txs_size + coinbase_blob_size;
#if defined(DEBUG_CREATE_BLOCK_TEMPLATE)
      MDEBUG("Creating block template: miner tx size " << coinbase_blob_size <<
          ", cumulative size " << cumulative_size << " is greater than before");
#endif
      continue;
    }

    if (coinbase_blob_size < cumulative_size - txs_size)
    {
      size_t delta = cumulative_size - txs_size - coinbase_blob_size;
#if defined(DEBUG_CREATE_BLOCK_TEMPLATE)
      MDEBUG("Creating block template: miner tx size " << coinbase_blob_size <<
          ", cumulative size " << txs_size + coinbase_blob_size <<
          " is less than before, adding " << delta << " zero bytes");
#endif
      b.miner_tx.extra.insert(b.miner_tx.extra.end(), delta, 0);
      //here  could be 1 byte difference, because of extra field counter is varint, and it can become from 1-byte len to 2-bytes len.
      if (cumulative_size != txs_size + get_object_blobsize(b.miner_tx))
      {
        CHECK_AND_ASSERT_MES(cumulative_size + 1 == txs_size + get_object_blobsize(b.miner_tx), false, "unexpected case: cumulative_size=" << cumulative_size << " + 1 is not equal txs_cumulative_size=" << txs_size << " + get_object_blobsize(b.miner_tx)=" << get_object_blobsize(b.miner_tx));
        b.miner_tx.extra.resize(b.miner_tx.extra.size() - 1);
        if (cumulative_size != txs_size + get_object_blobsize(b.miner_tx))
        {
          //fuck, not lucky, -1 makes varint-counter size smaller, in that case we continue to grow with cumulative_size
          MDEBUG("Miner tx creation has no luck with delta_extra size = " << delta << " and " << delta - 1);
          cumulative_size += delta - 1;
          continue;
        }
        MDEBUG("Setting extra for block: " << b.miner_tx.extra.size() << ", try_count=" << try_count);
      }
    }
    CHECK_AND_ASSERT_MES(cumulative_size == txs_size + get_object_blobsize(b.miner_tx), false, "unexpected case: cumulative_size=" << cumulative_size << " is not equal txs_cumulative_size=" << txs_size << " + get_object_blobsize(b.miner_tx)=" << get_object_blobsize(b.miner_tx));
#if defined(DEBUG_CREATE_BLOCK_TEMPLATE)
    MDEBUG("Creating block template: miner tx size " << coinbase_blob_size <<
        ", cumulative size " << cumulative_size << " is now good");
#endif
    return true;
  }
  LOG_ERROR("Failed to create_block_template with " << 10 << " tries");
  return false;
}
//------------------------------------------------------------------
// for an alternate chain, get the timestamps from the main chain to complete
// the needed number of timestamps for the BLOCKCHAIN_TIMESTAMP_CHECK_WINDOW.
bool Blockchain::complete_timestamps_vector(uint64_t start_top_height, std::vector<uint64_t>& timestamps)
{
  LOG_PRINT_L3("Blockchain::" << __func__);

  if(timestamps.size() >= BLOCKCHAIN_TIMESTAMP_CHECK_WINDOW)
    return true;

  CRITICAL_REGION_LOCAL(m_blockchain_lock);
  size_t need_elements = BLOCKCHAIN_TIMESTAMP_CHECK_WINDOW - timestamps.size();
  CHECK_AND_ASSERT_MES(start_top_height < m_db->height(), false, "internal error: passed start_height not < " << " m_db->height() -- " << start_top_height << " >= " << m_db->height());
  size_t stop_offset = start_top_height > need_elements ? start_top_height - need_elements : 0;
  while (start_top_height != stop_offset)
  {
    timestamps.push_back(m_db->get_block_timestamp(start_top_height));
    --start_top_height;
  }
  return true;
}
//------------------------------------------------------------------
// If a block is to be added and its parent block is not the current
// main chain top block, then we need to see if we know about its parent block.
// If its parent block is part of a known forked chain, then we need to see
// if that chain is long enough to become the main chain and re-org accordingly
// if so.  If not, we need to hang on to the block in case it becomes part of
// a long forked chain eventually.
bool Blockchain::handle_alternative_block(const block& b, const crypto::hash& id, block_verification_context& bvc)
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);
  m_timestamps_and_difficulties_height = 0;
  uint64_t block_height = get_block_height(b);
  if(0 == block_height)
  {
    MERROR_VER("Block with id: " << epee::string_tools::pod_to_hex(id) << " (as alternative), but miner tx says height is 0.");
    bvc.m_verifivation_failed = true;
    return false;
  }
  // this basically says if the blockchain is smaller than the first
  // checkpoint then alternate blocks are allowed.  Alternatively, if the
  // last checkpoint *before* the end of the current chain is also before
  // the block to be added, then this is fine.
  if (!m_checkpoints.is_alternative_block_allowed(get_current_blockchain_height(), block_height))
  {
    MERROR_VER("Block with id: " << id << std::endl << " can't be accepted for alternative chain, block height: " << block_height << std::endl << " blockchain height: " << get_current_blockchain_height());
    bvc.m_verifivation_failed = true;
    return false;
  }

  // this is a cheap test
  if (!m_hardfork->check_for_height(b, block_height))
  {
    LOG_PRINT_L1("Block with id: " << id << std::endl << "has old version for height " << block_height);
    bvc.m_verifivation_failed = true;
    return false;
  }

  //block is not related with head of main chain
  //first of all - look in alternative chains container
  auto it_prev = m_alternative_chains.find(b.prev_id);
  bool parent_in_main = m_db->block_exists(b.prev_id);
  if(it_prev != m_alternative_chains.end() || parent_in_main)
  {
    //we have new block in alternative chain

    //build alternative subchain, front -> mainchain, back -> alternative head
    blocks_ext_by_hash::iterator alt_it = it_prev; //m_alternative_chains.find()
    std::list<blocks_ext_by_hash::iterator> alt_chain;
    std::vector<uint64_t> timestamps;
    while(alt_it != m_alternative_chains.end())
    {
      alt_chain.push_front(alt_it);
      timestamps.push_back(alt_it->second.bl.timestamp);
      alt_it = m_alternative_chains.find(alt_it->second.bl.prev_id);
    }

    // if block to be added connects to known blocks that aren't part of the
    // main chain -- that is, if we're adding on to an alternate chain
    if(alt_chain.size())
    {
      // make sure alt chain doesn't somehow start past the end of the main chain
      CHECK_AND_ASSERT_MES(m_db->height() > alt_chain.front()->second.height, false, "main blockchain wrong height");

      // make sure that the blockchain contains the block that should connect
      // this alternate chain with it.
      if (!m_db->block_exists(alt_chain.front()->second.bl.prev_id))
      {
        MERROR("alternate chain does not appear to connect to main chain...");
        return false;
      }

      // make sure block connects correctly to the main chain
      auto h = m_db->get_block_hash_from_height(alt_chain.front()->second.height - 1);
      CHECK_AND_ASSERT_MES(h == alt_chain.front()->second.bl.prev_id, false, "alternative chain has wrong connection to main chain");
      complete_timestamps_vector(m_db->get_block_height(alt_chain.front()->second.bl.prev_id), timestamps);
    }
    // if block not associated with known alternate chain
    else
    {
      // if block parent is not part of main chain or an alternate chain,
      // we ignore it
      CHECK_AND_ASSERT_MES(parent_in_main, false, "internal error: broken imperative condition: parent_in_main");

      complete_timestamps_vector(m_db->get_block_height(b.prev_id), timestamps);
    }

    // verify that the block's timestamp is within the acceptable range
    // (not earlier than the median of the last X blocks)
    if(!check_block_timestamp(timestamps, b))
    {
      MERROR_VER("Block with id: " << id << std::endl << " for alternative chain, has invalid timestamp: " << b.timestamp);
      bvc.m_verifivation_failed = true;
      return false;
    }

    // FIXME: consider moving away from block_extended_info at some point
    block_extended_info bei = boost::value_initialized<block_extended_info>();
    bei.bl = b;
    bei.height = alt_chain.size() ? it_prev->second.height + 1 : m_db->get_block_height(b.prev_id) + 1;

    bool is_a_checkpoint;
    if(!m_checkpoints.check_block(bei.height, id, is_a_checkpoint))
    {
      LOG_ERROR("CHECKPOINT VALIDATION FAILED");
      bvc.m_verifivation_failed = true;
      return false;
    }

    // Check the block's hash against the difficulty target for its alt chain
    difficulty_type current_diff = get_next_difficulty_for_alternative_chain(alt_chain, bei);
    CHECK_AND_ASSERT_MES(current_diff, false, "!!!!!!! DIFFICULTY OVERHEAD !!!!!!!");
    crypto::hash proof_of_work = null_hash;
    if (!check_proof_of_work(bei.bl, current_diff, proof_of_work))
	   {
		MERROR_VER("Block with id: " << id << std::endl << " for alternative chain, does not have enough proof of work: " << proof_of_work << std::endl << "unexpected difficulty: " << current_diff);
		MDEBUG("Block info - ts " << bei.bl.timestamp << " nonce " << bei.bl.nonce);
		bvc.m_verifivation_failed = true;
		return false;
	 }
    /*if(!check_hash(proof_of_work, current_diff))
    {
      MERROR_VER("Block with id: " << id << std::endl << " for alternative chain, does not have enough proof of work: " << proof_of_work << std::endl << " expected difficulty: " << current_diff);
      bvc.m_verifivation_failed = true;
      return false;
    }*/

    if(!prevalidate_miner_transaction(b, bei.height))
    {
      MERROR_VER("Block with id: " << epee::string_tools::pod_to_hex(id) << " (as alternative) has incorrect miner transaction.");
      bvc.m_verifivation_failed = true;
      return false;
    }

    // FIXME:
    // this brings up an interesting point: consider allowing to get block
    // difficulty both by height OR by hash, not just height.
    difficulty_type main_chain_cumulative_difficulty = m_db->get_block_cumulative_difficulty(m_db->height() - 1);
    if (alt_chain.size())
    {
      bei.cumulative_difficulty = it_prev->second.cumulative_difficulty;
    }
    else
    {
      // passed-in block's previous block's cumulative difficulty, found on the main chain
      bei.cumulative_difficulty = m_db->get_block_cumulative_difficulty(m_db->get_block_height(b.prev_id));
    }
    bei.cumulative_difficulty += current_diff;

    // add block to alternate blocks storage,
    // as well as the current "alt chain" container
    auto i_res = m_alternative_chains.insert(blocks_ext_by_hash::value_type(id, bei));
    CHECK_AND_ASSERT_MES(i_res.second, false, "insertion of new alternative block returned as it already exist");
    alt_chain.push_back(i_res.first);

    // FIXME: is it even possible for a checkpoint to show up not on the main chain?
    if(is_a_checkpoint)
    {
      //do reorganize!
      MGINFO_GREEN("###### REORGANIZE on height: " << alt_chain.front()->second.height << " of " << m_db->height() - 1 << ", checkpoint is found in alternative chain on height " << bei.height);

      bool r = switch_to_alternative_blockchain(alt_chain, true);

      if(r) bvc.m_added_to_main_chain = true;
      else bvc.m_verifivation_failed = true;

      return r;
    }
    else if(main_chain_cumulative_difficulty < bei.cumulative_difficulty) //check if difficulty bigger then in main chain
    {
      //do reorganize!
      MGINFO_GREEN("###### REORGANIZE on height: " << alt_chain.front()->second.height << " of " << m_db->height() - 1 << " with cum_difficulty " << m_db->get_block_cumulative_difficulty(m_db->height() - 1) << std::endl << " alternative blockchain size: " << alt_chain.size() << " with cum_difficulty " << bei.cumulative_difficulty);

      bool r = switch_to_alternative_blockchain(alt_chain, false);
      if (r)
        bvc.m_added_to_main_chain = true;
      else
        bvc.m_verifivation_failed = true;
      return r;
    }
    else
    {
      MGINFO_BLUE("----- BLOCK ADDED AS ALTERNATIVE ON HEIGHT " << bei.height << std::endl << "id:\t" << id << std::endl << "PoW:\t" << proof_of_work << std::endl << "difficulty:\t" << current_diff);
      return true;
    }
  }
  else
  {
    //block orphaned
    bvc.m_marked_as_orphaned = true;
    MERROR_VER("Block recognized as orphaned and rejected, id = " << id << ", height " << block_height
        << ", parent in alt " << (it_prev != m_alternative_chains.end()) << ", parent in main " << parent_in_main
        << " (parent " << b.prev_id << ", current top " << get_tail_id() << ", chain height " << get_current_blockchain_height() << ")");
  }

  return true;
}
//------------------------------------------------------------------
bool Blockchain::get_blocks(uint64_t start_offset, size_t count, std::list<std::pair<cryptonote::blobdata,block>>& blocks, std::list<cryptonote::blobdata>& txs) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);
  if(start_offset >= m_db->height())
    return false;

  if (!get_blocks(start_offset, count, blocks))
  {
    return false;
  }

  for(const auto& blk : blocks)
  {
    std::list<crypto::hash> missed_ids;
    get_transactions_blobs(blk.second.tx_hashes, txs, missed_ids);
    CHECK_AND_ASSERT_MES(!missed_ids.size(), false, "has missed transactions in own block in main blockchain");
  }

  return true;
}
//------------------------------------------------------------------
bool Blockchain::get_blocks(uint64_t start_offset, size_t count, std::list<std::pair<cryptonote::blobdata,block>>& blocks) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);
  if(start_offset >= m_db->height())
    return false;

  for(size_t i = start_offset; i < start_offset + count && i < m_db->height();i++)
  {
    blocks.push_back(std::make_pair(m_db->get_block_blob_from_height(i), block()));
    if (!parse_and_validate_block_from_blob(blocks.back().first, blocks.back().second))
    {
      LOG_ERROR("Invalid block");
      return false;
    }
  }
  return true;
}
//------------------------------------------------------------------
//TODO: This function *looks* like it won't need to be rewritten
//      to use BlockchainDB, as it calls other functions that were,
//      but it warrants some looking into later.
//
//FIXME: This function appears to want to return false if any transactions
//       that belong with blocks are missing, but not if blocks themselves
//       are missing.
bool Blockchain::handle_get_objects(NOTIFY_REQUEST_GET_OBJECTS::request& arg, NOTIFY_RESPONSE_GET_OBJECTS::request& rsp)
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);
  m_db->block_txn_start(true);
  rsp.current_blockchain_height = get_current_blockchain_height();
  std::list<std::pair<cryptonote::blobdata,block>> blocks;
  get_blocks(arg.blocks, blocks, rsp.missed_ids);

  for (const auto& bl: blocks)
  {
    std::list<crypto::hash> missed_tx_ids;
    std::list<cryptonote::blobdata> txs;

    // FIXME: s/rsp.missed_ids/missed_tx_id/ ?  Seems like rsp.missed_ids
    //        is for missed blocks, not missed transactions as well.
    get_transactions_blobs(bl.second.tx_hashes, txs, missed_tx_ids);

    if (missed_tx_ids.size() != 0)
    {
      LOG_ERROR("Error retrieving blocks, missed " << missed_tx_ids.size()
          << " transactions for block with hash: " << get_block_hash(bl.second)
          << std::endl
      );

      // append missed transaction hashes to response missed_ids field,
      // as done below if any standalone transactions were requested
      // and missed.
      rsp.missed_ids.splice(rsp.missed_ids.end(), missed_tx_ids);
	  m_db->block_txn_stop();
      return false;
    }

    rsp.blocks.push_back(block_complete_entry());
    block_complete_entry& e = rsp.blocks.back();
    //pack block
    e.block = bl.first;
    //pack transactions
    for (const cryptonote::blobdata& tx: txs)
      e.txs.push_back(tx);
  }
  //get another transactions, if need
  std::list<cryptonote::blobdata> txs;
  get_transactions_blobs(arg.txs, txs, rsp.missed_ids);
  //pack aside transactions
  for (const auto& tx: txs)
    rsp.txs.push_back(tx);

  m_db->block_txn_stop();
  return true;
}
//------------------------------------------------------------------
bool Blockchain::get_alternative_blocks(std::list<block>& blocks) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);

  for (const auto& alt_bl: m_alternative_chains)
  {
    blocks.push_back(alt_bl.second.bl);
  }
  return true;
}
//------------------------------------------------------------------
size_t Blockchain::get_alternative_blocks_count() const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);
  return m_alternative_chains.size();
}
//------------------------------------------------------------------
// This function adds the output specified by <amount, i> to the result_outs container
// unlocked and other such checks should be done by here.
void Blockchain::add_out_to_get_random_outs(COMMAND_RPC_GET_RANDOM_OUTPUTS_FOR_AMOUNTS::outs_for_amount& result_outs, uint64_t amount, size_t i) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);

  COMMAND_RPC_GET_RANDOM_OUTPUTS_FOR_AMOUNTS::out_entry& oen = *result_outs.outs.insert(result_outs.outs.end(), COMMAND_RPC_GET_RANDOM_OUTPUTS_FOR_AMOUNTS::out_entry());
  oen.global_amount_index = i;
  output_data_t data = m_db->get_output_key(amount, i);
  oen.out_key = data.pubkey;
}

uint64_t Blockchain::get_num_mature_outputs(uint64_t amount) const
{
  uint64_t num_outs = m_db->get_num_outputs(amount);
  // ensure we don't include outputs that aren't yet eligible to be used
  // outpouts are sorted by height
  while (num_outs > 0)
  {
    const tx_out_index toi = m_db->get_output_tx_and_index(amount, num_outs - 1);
    const uint64_t height = m_db->get_tx_block_height(toi.first);
    if (height + CRYPTONOTE_DEFAULT_TX_SPENDABLE_AGE <= m_db->height())
      break;
    --num_outs;
  }

  return num_outs;
}

std::vector<uint64_t> Blockchain::get_random_outputs(uint64_t amount, uint64_t count) const
{
  uint64_t num_outs = get_num_mature_outputs(amount);

  std::vector<uint64_t> indices;

  std::unordered_set<uint64_t> seen_indices;

  // if there aren't enough outputs to mix with (or just enough),
  // use all of them.  Eventually this should become impossible.
  if (num_outs <= count)
  {
    for (uint64_t i = 0; i < num_outs; i++)
    {
      // get tx_hash, tx_out_index from DB
      tx_out_index toi = m_db->get_output_tx_and_index(amount, i);

      // if tx is unlocked, add output to indices
      if (is_tx_spendtime_unlocked(m_db->get_tx_unlock_time(toi.first)))
      {
        indices.push_back(i);
      }
    }
  }
  else
  {
    // while we still need more mixins
    while (indices.size() < count)
    {
      // if we've gone through every possible output, we've gotten all we can
      if (seen_indices.size() == num_outs)
      {
        break;
      }

      // get a random output index from the DB.  If we've already seen it,
      // return to the top of the loop and try again, otherwise add it to the
      // list of output indices we've seen.

      // triangular distribution over [a,b) with a=0, mode c=b=up_index_limit
      uint64_t r = crypto::rand<uint64_t>() % ((uint64_t)1 << 53);
      double frac = std::sqrt((double)r / ((uint64_t)1 << 53));
      uint64_t i = (uint64_t)(frac*num_outs);
      // just in case rounding up to 1 occurs after sqrt
      if (i == num_outs)
        --i;

      if (seen_indices.count(i))
      {
        continue;
      }
      seen_indices.emplace(i);

      // get tx_hash, tx_out_index from DB
      tx_out_index toi = m_db->get_output_tx_and_index(amount, i);

      // if the output's transaction is unlocked, add the output's index to
      // our list.
      if (is_tx_spendtime_unlocked(m_db->get_tx_unlock_time(toi.first)))
      {
        indices.push_back(i);
      }
    }
  }

  return indices;
}

crypto::public_key Blockchain::get_output_key(uint64_t amount, uint64_t global_index) const
{
  output_data_t data = m_db->get_output_key(amount, global_index);
  return data.pubkey;
}

//------------------------------------------------------------------
// This function takes an RPC request for mixins and creates an RPC response
// with the requested mixins.
// TODO: figure out why this returns boolean / if we should be returning false
// in some cases
bool Blockchain::get_random_outs_for_amounts(const COMMAND_RPC_GET_RANDOM_OUTPUTS_FOR_AMOUNTS::request& req, COMMAND_RPC_GET_RANDOM_OUTPUTS_FOR_AMOUNTS::response& res) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);

  // for each amount that we need to get mixins for, get <n> random outputs
  // from BlockchainDB where <n> is req.outs_count (number of mixins).
  for (uint64_t amount : req.amounts)
  {
    // create outs_for_amount struct and populate amount field
    COMMAND_RPC_GET_RANDOM_OUTPUTS_FOR_AMOUNTS::outs_for_amount& result_outs = *res.outs.insert(res.outs.end(), COMMAND_RPC_GET_RANDOM_OUTPUTS_FOR_AMOUNTS::outs_for_amount());
    result_outs.amount = amount;

    std::vector<uint64_t> indices = get_random_outputs(amount, req.outs_count);

    for (auto i : indices)
    {
      COMMAND_RPC_GET_RANDOM_OUTPUTS_FOR_AMOUNTS::out_entry& oe = *result_outs.outs.insert(result_outs.outs.end(), COMMAND_RPC_GET_RANDOM_OUTPUTS_FOR_AMOUNTS::out_entry());

      oe.global_amount_index = i;
      oe.out_key = get_output_key(amount, i);
    }
  }
  return true;
}
//------------------------------------------------------------------
// This function adds the ringct output at index i to the list
// unlocked and other such checks should be done by here.
void Blockchain::add_out_to_get_rct_random_outs(std::list<COMMAND_RPC_GET_RANDOM_RCT_OUTPUTS::out_entry>& outs, uint64_t amount, size_t i) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);

  COMMAND_RPC_GET_RANDOM_RCT_OUTPUTS::out_entry& oen = *outs.insert(outs.end(), COMMAND_RPC_GET_RANDOM_RCT_OUTPUTS::out_entry());
  oen.amount = amount;
  oen.global_amount_index = i;
  output_data_t data = m_db->get_output_key(amount, i);
  oen.out_key = data.pubkey;
  oen.commitment = data.commitment;
}
//------------------------------------------------------------------
// This function takes an RPC request for mixins and creates an RPC response
// with the requested mixins.
// TODO: figure out why this returns boolean / if we should be returning false
// in some cases
bool Blockchain::get_random_rct_outs(const COMMAND_RPC_GET_RANDOM_RCT_OUTPUTS::request& req, COMMAND_RPC_GET_RANDOM_RCT_OUTPUTS::response& res) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);

  // for each amount that we need to get mixins for, get <n> random outputs
  // from BlockchainDB where <n> is req.outs_count (number of mixins).
  auto num_outs = m_db->get_num_outputs(0);
  // ensure we don't include outputs that aren't yet eligible to be used
  // outpouts are sorted by height
  while (num_outs > 0)
  {
    const tx_out_index toi = m_db->get_output_tx_and_index(0, num_outs - 1);
    const uint64_t height = m_db->get_tx_block_height(toi.first);
    if (height + CRYPTONOTE_DEFAULT_TX_SPENDABLE_AGE <= m_db->height())
      break;
    --num_outs;
  }

  std::unordered_set<uint64_t> seen_indices;

  // if there aren't enough outputs to mix with (or just enough),
  // use all of them.  Eventually this should become impossible.
  if (num_outs <= req.outs_count)
  {
    for (uint64_t i = 0; i < num_outs; i++)
    {
      // get tx_hash, tx_out_index from DB
      tx_out_index toi = m_db->get_output_tx_and_index(0, i);

      // if tx is unlocked, add output to result_outs
      if (is_tx_spendtime_unlocked(m_db->get_tx_unlock_time(toi.first)))
      {
        add_out_to_get_rct_random_outs(res.outs, 0, i);
      }
    }
  }
  else
  {
    // while we still need more mixins
    while (res.outs.size() < req.outs_count)
    {
      // if we've gone through every possible output, we've gotten all we can
      if (seen_indices.size() == num_outs)
      {
        break;
      }

      // get a random output index from the DB.  If we've already seen it,
      // return to the top of the loop and try again, otherwise add it to the
      // list of output indices we've seen.

      // triangular distribution over [a,b) with a=0, mode c=b=up_index_limit
      uint64_t r = crypto::rand<uint64_t>() % ((uint64_t)1 << 53);
      double frac = std::sqrt((double)r / ((uint64_t)1 << 53));
      uint64_t i = (uint64_t)(frac*num_outs);
      // just in case rounding up to 1 occurs after sqrt
      if (i == num_outs)
        --i;

      if (seen_indices.count(i))
      {
        continue;
      }
      seen_indices.emplace(i);

      // get tx_hash, tx_out_index from DB
      tx_out_index toi = m_db->get_output_tx_and_index(0, i);

      // if the output's transaction is unlocked, add the output's index to
      // our list.
      if (is_tx_spendtime_unlocked(m_db->get_tx_unlock_time(toi.first)))
      {
        add_out_to_get_rct_random_outs(res.outs, 0, i);
      }
    }
  }

  if (res.outs.size() < req.outs_count)
    return false;
#if 0
  // if we do not have enough RCT inputs, we can pick from the non RCT ones
  // which will have a zero mask
  if (res.outs.size() < req.outs_count)
  {
    LOG_PRINT_L0("Out of RCT inputs (" << res.outs.size() << "/" << req.outs_count << "), using regular ones");

    // TODO: arbitrary selection, needs better
    COMMAND_RPC_GET_RANDOM_OUTPUTS_FOR_AMOUNTS::request req2 = AUTO_VAL_INIT(req2);
    COMMAND_RPC_GET_RANDOM_OUTPUTS_FOR_AMOUNTS::response res2 = AUTO_VAL_INIT(res2);
    req2.outs_count = req.outs_count - res.outs.size();
    static const uint64_t amounts[] = {1, 10, 20, 50, 100, 200, 500, 1000, 10000};
    for (uint64_t a: amounts)
      req2.amounts.push_back(a);
    if (!get_random_outs_for_amounts(req2, res2))
      return false;

    // pick random ones from there
    while (res.outs.size() < req.outs_count)
    {
      int list_idx = rand() % (sizeof(amounts)/sizeof(amounts[0]));
      if (!res2.outs[list_idx].outs.empty())
      {
        const COMMAND_RPC_GET_RANDOM_OUTPUTS_FOR_AMOUNTS::out_entry oe = res2.outs[list_idx].outs.back();
        res2.outs[list_idx].outs.pop_back();
        add_out_to_get_rct_random_outs(res.outs, res2.outs[list_idx].amount, oe.global_amount_index);
      }
    }
  }
#endif

  return true;
}
//------------------------------------------------------------------
bool Blockchain::get_outs(const COMMAND_RPC_GET_OUTPUTS_BIN::request& req, COMMAND_RPC_GET_OUTPUTS_BIN::response& res) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);

  res.outs.clear();
  res.outs.reserve(req.outputs.size());
  for (const auto &i: req.outputs)
  {
    // get tx_hash, tx_out_index from DB
    const output_data_t od = m_db->get_output_key(i.amount, i.index);
    tx_out_index toi = m_db->get_output_tx_and_index(i.amount, i.index);
    bool unlocked = is_tx_spendtime_unlocked(m_db->get_tx_unlock_time(toi.first));

    res.outs.push_back({od.pubkey, od.commitment, unlocked, od.height, toi.first});
  }
  return true;
}
//------------------------------------------------------------------
void Blockchain::get_output_key_mask_unlocked(const uint64_t& amount, const uint64_t& index, crypto::public_key& key, rct::key& mask, bool& unlocked) const
{
  const auto o_data = m_db->get_output_key(amount, index);
  key = o_data.pubkey;
  mask = o_data.commitment;
  tx_out_index toi = m_db->get_output_tx_and_index(amount, index);
  unlocked = is_tx_spendtime_unlocked(m_db->get_tx_unlock_time(toi.first));
}
//------------------------------------------------------------------
bool Blockchain::get_output_distribution(uint64_t amount, uint64_t from_height, uint64_t to_height, uint64_t &start_height, std::vector<uint64_t> &distribution, uint64_t &base) const
{
  // rct outputs don't exist before v3
  if (amount == 0)
  {
    switch (m_nettype)
    {
      case STAGENET: start_height = stagenet_hard_forks[2].height; break;
      case TESTNET: start_height = testnet_hard_forks[2].height; break;
      case MAINNET: start_height = mainnet_hard_forks[2].height; break;
      default: return false;
    }
  }
  else
    start_height = 0;
  base = 0;

  const uint64_t real_start_height = start_height;
  if (from_height > start_height)
    start_height = from_height;

  return m_db->get_output_distribution(amount, start_height, to_height, distribution, base);
}
//------------------------------------------------------------------
// This function takes a list of block hashes from another node
// on the network to find where the split point is between us and them.
// This is used to see what to send another node that needs to sync.
bool Blockchain::find_blockchain_supplement(const std::list<crypto::hash>& qblock_ids, uint64_t& starter_offset) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);

  // make sure the request includes at least the genesis block, otherwise
  // how can we expect to sync from the client that the block list came from?
  if(!qblock_ids.size() /*|| !req.m_total_height*/)
  {
    MCERROR("net.p2p", "Client sent wrong NOTIFY_REQUEST_CHAIN: m_block_ids.size()=" << qblock_ids.size() << /*", m_height=" << req.m_total_height <<*/ ", dropping connection");
    return false;
  }

  m_db->block_txn_start(true);
  // make sure that the last block in the request's block list matches
  // the genesis block
  auto gen_hash = m_db->get_block_hash_from_height(0);
  if(qblock_ids.back() != gen_hash)
  {
    MCERROR("net.p2p", "Client sent wrong NOTIFY_REQUEST_CHAIN: genesis block mismatch: " << std::endl << "id: " << qblock_ids.back() << ", " << std::endl << "expected: " << gen_hash << "," << std::endl << " dropping connection");
	m_db->block_txn_abort();
    return false;
  }

  // Find the first block the foreign chain has that we also have.
  // Assume qblock_ids is in reverse-chronological order.
  auto bl_it = qblock_ids.begin();
  uint64_t split_height = 0;
  for(; bl_it != qblock_ids.end(); bl_it++)
  {
    try
    {
      if (m_db->block_exists(*bl_it, &split_height))
        break;
    }
    catch (const std::exception& e)
    {
      MWARNING("Non-critical error trying to find block by hash in BlockchainDB, hash: " << *bl_it);
	  m_db->block_txn_abort();
      return false;
    }
  }
  m_db->block_txn_stop();

  // this should be impossible, as we checked that we share the genesis block,
  // but just in case...
  if(bl_it == qblock_ids.end())
  {
    MERROR("Internal error handling connection, can't find split point");
    return false;
  }

  //we start to put block ids INCLUDING last known id, just to make other side be sure
  starter_offset = split_height;
  return true;
}
//------------------------------------------------------------------
uint64_t Blockchain::block_difficulty(uint64_t i) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  // WARNING: this function does not take m_blockchain_lock, and thus should only call read only
  // m_db functions which do not depend on one another (ie, no getheight + gethash(height-1), as
  // well as not accessing class members, even read only (ie, m_invalid_blocks). The caller must
  // lock if it is otherwise needed.
  try
  {
    return m_db->get_block_difficulty(i);
  }
  catch (const BLOCK_DNE& e)
  {
    MERROR("Attempted to get block difficulty for height above blockchain height");
  }
  return 0;
}
//------------------------------------------------------------------
//TODO: return type should be void, throw on exception
//       alternatively, return true only if no blocks missed
template<class t_ids_container, class t_blocks_container, class t_missed_container>
bool Blockchain::get_blocks(const t_ids_container& block_ids, t_blocks_container& blocks, t_missed_container& missed_bs) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);

  for (const auto& block_hash : block_ids)
  {
    try
    {
      blocks.push_back(std::make_pair(m_db->get_block_blob(block_hash), block()));
      if (!parse_and_validate_block_from_blob(blocks.back().first, blocks.back().second))
      {
        LOG_ERROR("Invalid block");
        return false;
      }
    }
    catch (const BLOCK_DNE& e)
    {
      missed_bs.push_back(block_hash);
    }
    catch (const std::exception& e)
    {
      return false;
    }
  }
  return true;
}
//------------------------------------------------------------------
//TODO: return type should be void, throw on exception
//       alternatively, return true only if no transactions missed
template<class t_ids_container, class t_tx_container, class t_missed_container>
bool Blockchain::get_transactions_blobs(const t_ids_container& txs_ids, t_tx_container& txs, t_missed_container& missed_txs, bool pruned) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);

  for (const auto& tx_hash : txs_ids)
  {
    try
    {
      cryptonote::blobdata tx;
      if (pruned && m_db->get_pruned_tx_blob(tx_hash, tx))
        txs.push_back(std::move(tx));
      else if (!pruned && m_db->get_tx_blob(tx_hash, tx))
        txs.push_back(std::move(tx));
      else
        missed_txs.push_back(tx_hash);
    }
    catch (const std::exception& e)
    {
      return false;
    }
  }
  return true;
}
//------------------------------------------------------------------
template<class t_ids_container, class t_tx_container, class t_missed_container>
bool Blockchain::get_transactions(const t_ids_container& txs_ids, t_tx_container& txs, t_missed_container& missed_txs) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);

  for (const auto& tx_hash : txs_ids)
  {
    try
    {
      cryptonote::blobdata tx;
      if (m_db->get_tx_blob(tx_hash, tx))
      {
        txs.push_back(transaction());
        if (!parse_and_validate_tx_from_blob(tx, txs.back()))
        {
          LOG_ERROR("Invalid transaction");
          return false;
        }
      }
      else
        missed_txs.push_back(tx_hash);
    }
    catch (const std::exception& e)
    {
      return false;
    }
  }
  return true;
}
//------------------------------------------------------------------
// Find the split point between us and foreign blockchain and return
// (by reference) the most recent common block hash along with up to
// BLOCKS_IDS_SYNCHRONIZING_DEFAULT_COUNT additional (more recent) hashes.
bool Blockchain::find_blockchain_supplement(const std::list<crypto::hash>& qblock_ids, std::list<crypto::hash>& hashes, uint64_t& start_height, uint64_t& current_height) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);

  // if we can't find the split point, return false
  if(!find_blockchain_supplement(qblock_ids, start_height))
  {
    return false;
  }

  m_db->block_txn_start(true);
  current_height = get_current_blockchain_height();
  size_t count = 0;
  for(size_t i = start_height; i < current_height && count < BLOCKS_IDS_SYNCHRONIZING_DEFAULT_COUNT; i++, count++)
  {
    hashes.push_back(m_db->get_block_hash_from_height(i));
  }

  m_db->block_txn_stop();
  return true;
}

bool Blockchain::find_blockchain_supplement(const std::list<crypto::hash>& qblock_ids, NOTIFY_RESPONSE_CHAIN_ENTRY::request& resp) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);

  bool result = find_blockchain_supplement(qblock_ids, resp.m_block_ids, resp.start_height, resp.total_height);
  resp.cumulative_difficulty = m_db->get_block_cumulative_difficulty(m_db->height() - 1);

  return result;
}
//------------------------------------------------------------------
//FIXME: change argument to std::vector, low priority
// find split point between ours and foreign blockchain (or start at
// blockchain height <req_start_block>), and return up to max_count FULL
// blocks by reference.
bool Blockchain::find_blockchain_supplement(const uint64_t req_start_block, const std::list<crypto::hash>& qblock_ids, std::list<std::pair<cryptonote::blobdata, std::list<cryptonote::blobdata> > >& blocks, uint64_t& total_height, uint64_t& start_height, bool pruned, size_t max_count) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);

  // if a specific start height has been requested
  if(req_start_block > 0)
  {
    // if requested height is higher than our chain, return false -- we can't help
    if (req_start_block >= m_db->height())
    {
      return false;
    }
    start_height = req_start_block;
  }
  else
  {
    if(!find_blockchain_supplement(qblock_ids, start_height))
    {
      return false;
    }
  }

  m_db->block_txn_start(true);
  total_height = get_current_blockchain_height();
  size_t count = 0, size = 0;
  for(size_t i = start_height; i < total_height && count < max_count && (size < FIND_BLOCKCHAIN_SUPPLEMENT_MAX_SIZE || count < 3); i++, count++)
  {
    blocks.resize(blocks.size()+1);
    blocks.back().first = m_db->get_block_blob_from_height(i);
    block b;
    CHECK_AND_ASSERT_MES(parse_and_validate_block_from_blob(blocks.back().first, b), false, "internal error, invalid block");
    std::list<crypto::hash> mis;
    get_transactions_blobs(b.tx_hashes, blocks.back().second, mis, pruned);
    CHECK_AND_ASSERT_MES(!mis.size(), false, "internal error, transaction from block not found");
    size += blocks.back().first.size();
    for (const auto &t: blocks.back().second)
      size += t.size();
  }
  m_db->block_txn_stop();
  return true;
}
//------------------------------------------------------------------
bool Blockchain::add_block_as_invalid(const block& bl, const crypto::hash& h)
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  block_extended_info bei = AUTO_VAL_INIT(bei);
  bei.bl = bl;
  return add_block_as_invalid(bei, h);
}
//------------------------------------------------------------------
bool Blockchain::add_block_as_invalid(const block_extended_info& bei, const crypto::hash& h)
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);
  auto i_res = m_invalid_blocks.insert(std::map<crypto::hash, block_extended_info>::value_type(h, bei));
  CHECK_AND_ASSERT_MES(i_res.second, false, "at insertion invalid by tx returned status existed");
  MINFO("BLOCK ADDED AS INVALID: " << h << std::endl << ", prev_id=" << bei.bl.prev_id << ", m_invalid_blocks count=" << m_invalid_blocks.size());
  return true;
}
//------------------------------------------------------------------
bool Blockchain::have_block(const crypto::hash& id) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);

  if(m_db->block_exists(id))
  {
    LOG_PRINT_L3("block exists in main chain");
    return true;
  }

  if(m_alternative_chains.count(id))
  {
    LOG_PRINT_L3("block found in m_alternative_chains");
    return true;
  }

  if(m_invalid_blocks.count(id))
  {
    LOG_PRINT_L3("block found in m_invalid_blocks");
    return true;
  }

  return false;
}
//------------------------------------------------------------------
bool Blockchain::handle_block_to_main_chain(const block& bl, block_verification_context& bvc)
{
    LOG_PRINT_L3("Blockchain::" << __func__);
    crypto::hash id = get_block_hash(bl);
    return handle_block_to_main_chain(bl, id, bvc);
}
//------------------------------------------------------------------
size_t Blockchain::get_total_transactions() const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  // WARNING: this function does not take m_blockchain_lock, and thus should only call read only
  // m_db functions which do not depend on one another (ie, no getheight + gethash(height-1), as
  // well as not accessing class members, even read only (ie, m_invalid_blocks). The caller must
  // lock if it is otherwise needed.
  return m_db->get_tx_count();
}
//------------------------------------------------------------------
// This function checks each input in the transaction <tx> to make sure it
// has not been used already, and adds its key to the container <keys_this_block>.
//
// This container should be managed by the code that validates blocks so we don't
// have to store the used keys in a given block in the permanent storage only to
// remove them later if the block fails validation.
bool Blockchain::check_for_double_spend(const transaction& tx, key_images_container& keys_this_block) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);
  struct add_transaction_input_visitor: public boost::static_visitor<bool>
  {
    key_images_container& m_spent_keys;
    BlockchainDB* m_db;
    add_transaction_input_visitor(key_images_container& spent_keys, BlockchainDB* db) :
      m_spent_keys(spent_keys), m_db(db)
    {
    }
    bool operator()(const txin_to_key& in) const
    {
      const crypto::key_image& ki = in.k_image;

      // attempt to insert the newly-spent key into the container of
      // keys spent this block.  If this fails, the key was spent already
      // in this block, return false to flag that a double spend was detected.
      //
      // if the insert into the block-wide spent keys container succeeds,
      // check the blockchain-wide spent keys container and make sure the
      // key wasn't used in another block already.
      auto r = m_spent_keys.insert(ki);
      if(!r.second || m_db->has_key_image(ki))
      {
        //double spend detected
        return false;
      }

      // if no double-spend detected, return true
      return true;
    }

    bool operator()(const txin_gen& tx) const
    {
      return true;
    }
    bool operator()(const txin_to_script& tx) const
    {
      return false;
    }
    bool operator()(const txin_to_scripthash& tx) const
    {
      return false;
    }
  };

  for (const txin_v& in : tx.vin)
  {
    if(!boost::apply_visitor(add_transaction_input_visitor(keys_this_block, m_db), in))
    {
      LOG_ERROR("Double spend detected!");
      return false;
    }
  }

  return true;
}
//------------------------------------------------------------------
bool Blockchain::get_tx_outputs_gindexs(const crypto::hash& tx_id, std::vector<uint64_t>& indexs) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);
  uint64_t tx_index;
  if (!m_db->tx_exists(tx_id, tx_index))
  {
    MERROR_VER("get_tx_outputs_gindexs failed to find transaction with id = " << tx_id);
    return false;
  }

  // get amount output indexes, currently referred to in parts as "output global indices", but they are actually specific to amounts
  indexs = m_db->get_tx_amount_output_indices(tx_index);
  if (indexs.empty())
  {
    // empty indexs is only valid if the vout is empty, which is legal but rare
    cryptonote::transaction tx = m_db->get_tx(tx_id);
    CHECK_AND_ASSERT_MES(tx.vout.empty(), false, "internal error: global indexes for transaction " << tx_id << " is empty, and tx vout is not");
  }

  return true;
}
//------------------------------------------------------------------
void Blockchain::on_new_tx_from_block(const cryptonote::transaction &tx)
{
#if defined(PER_BLOCK_CHECKPOINT)
  // check if we're doing per-block checkpointing
  if (m_db->height() < m_blocks_hash_check.size())
  {
    TIME_MEASURE_START(a);
    m_blocks_txs_check.push_back(get_transaction_hash(tx));
    TIME_MEASURE_FINISH(a);
    if(m_show_time_stats)
    {
      size_t ring_size = !tx.vin.empty() && tx.vin[0].type() == typeid(txin_to_key) ? boost::get<txin_to_key>(tx.vin[0]).key_offsets.size() : 0;
      MINFO("HASH: " << "-" << " I/M/O: " << tx.vin.size() << "/" << ring_size << "/" << tx.vout.size() << " H: " << 0 << " chcktx: " << a);
    }
  }
#endif
}
//------------------------------------------------------------------
//FIXME: it seems this function is meant to be merely a wrapper around
//       another function of the same name, this one adding one bit of
//       functionality.  Should probably move anything more than that
//       (getting the hash of the block at height max_used_block_id)
//       to the other function to keep everything in one place.
// This function overloads its sister function with
// an extra value (hash of highest block that holds an output used as input)
// as a return-by-reference.
bool Blockchain::check_tx_inputs(transaction& tx, uint64_t& max_used_block_height, crypto::hash& max_used_block_id, tx_verification_context &tvc, bool kept_by_block)
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);

#if defined(PER_BLOCK_CHECKPOINT)
  // check if we're doing per-block checkpointing
  if (m_db->height() < m_blocks_hash_check.size() && kept_by_block)
  {
    max_used_block_id = null_hash;
    max_used_block_height = 0;
    return true;
  }
#endif

  TIME_MEASURE_START(a);
  bool res = check_tx_inputs(tx, tvc, &max_used_block_height);
  TIME_MEASURE_FINISH(a);
  if(m_show_time_stats)
  {
    size_t ring_size = !tx.vin.empty() && tx.vin[0].type() == typeid(txin_to_key) ? boost::get<txin_to_key>(tx.vin[0]).key_offsets.size() : 0;
    MINFO("HASH: " <<  get_transaction_hash(tx) << " I/M/O: " << tx.vin.size() << "/" << ring_size << "/" << tx.vout.size() << " H: " << max_used_block_height << " ms: " << a + m_fake_scan_time << " B: " << get_object_blobsize(tx));
  }
  if (!res)
    return false;
 if(get_current_hard_fork_version() >= 6){
  CHECK_AND_ASSERT_MES(max_used_block_height < m_db->height(), false,  "internal error: max used block index=" << max_used_block_height << " is not less then blockchain size = " << m_db->height());
  max_used_block_id = m_db->get_block_hash_from_height(max_used_block_height);
  }
  return true;
}
//------------------------------------------------------------------
bool Blockchain::check_tx_outputs(const transaction& tx, tx_verification_context &tvc)
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);

  const uint8_t hf_version = m_hardfork->get_current_version();

  // from hard fork 2, we forbid dust and compound outputs
  if (hf_version >= 2) {
    for (auto &o: tx.vout) {
      if (tx.version == 1)
      {
        if (!is_valid_decomposed_amount(o.amount)) {
          tvc.m_invalid_output = true;
          return false;
        }
      }
    }
  }

  // in a v2 tx, all outputs must have 0 amount
  if (hf_version >= 3) {
    if (tx.version >= 2) {
      for (auto &o: tx.vout) {
        if (o.amount != 0) {
          tvc.m_invalid_output = true;
          return false;
        }
      }
    }
  }

  // from v4, forbid invalid pubkeys
  if (hf_version >= 4) {
    for (const auto &o: tx.vout) {
      if (o.target.type() == typeid(txout_to_key)) {
        const txout_to_key& out_to_key = boost::get<txout_to_key>(o.target);
        if (!crypto::check_key(out_to_key.key)) {
          tvc.m_invalid_output = true;
          return false;
        }
      }
    }
  }

  // from v8, allow bulletproofs
  if (hf_version < 8) {
    const bool bulletproof = tx.rct_signatures.type == rct::RCTTypeFullBulletproof || tx.rct_signatures.type == rct::RCTTypeSimpleBulletproof;
    if (bulletproof || !tx.rct_signatures.p.bulletproofs.empty())
    {
      MERROR("Bulletproofs are not allowed before v8");
      tvc.m_invalid_output = true;
      return false;
    }
  }

  return true;
}
//------------------------------------------------------------------
bool Blockchain::have_tx_keyimges_as_spent(const transaction &tx) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  for (const txin_v& in: tx.vin)
  {
    CHECKED_GET_SPECIFIC_VARIANT(in, const txin_to_key, in_to_key, true);
    if(have_tx_keyimg_as_spent(in_to_key.k_image))
      return true;
  }
  return false;
}
bool Blockchain::expand_transaction_2(transaction &tx, const crypto::hash &tx_prefix_hash, const std::vector<std::vector<rct::ctkey>> &pubkeys)
{
  PERF_TIMER(expand_transaction_2);
  CHECK_AND_ASSERT_MES(tx.version == 2, false, "Transaction version is not 2");

  rct::rctSig &rv = tx.rct_signatures;

  // message - hash of the transaction prefix
  rv.message = rct::hash2rct(tx_prefix_hash);

  // mixRing - full and simple store it in opposite ways
  if (rv.type == rct::RCTTypeFull || rv.type == rct::RCTTypeFullBulletproof)
  {
    CHECK_AND_ASSERT_MES(!pubkeys.empty() && !pubkeys[0].empty(), false, "empty pubkeys");
    rv.mixRing.resize(pubkeys[0].size());
    for (size_t m = 0; m < pubkeys[0].size(); ++m)
      rv.mixRing[m].clear();
    for (size_t n = 0; n < pubkeys.size(); ++n)
    {
      CHECK_AND_ASSERT_MES(pubkeys[n].size() <= pubkeys[0].size(), false, "More inputs that first ring");
      for (size_t m = 0; m < pubkeys[n].size(); ++m)
      {
        rv.mixRing[m].push_back(pubkeys[n][m]);
      }
    }
  }
  else if (rv.type == rct::RCTTypeSimple || rv.type == rct::RCTTypeSimpleBulletproof)
  {
    CHECK_AND_ASSERT_MES(!pubkeys.empty() && !pubkeys[0].empty(), false, "empty pubkeys");
    rv.mixRing.resize(pubkeys.size());
    for (size_t n = 0; n < pubkeys.size(); ++n)
    {
      rv.mixRing[n].clear();
      for (size_t m = 0; m < pubkeys[n].size(); ++m)
      {
        rv.mixRing[n].push_back(pubkeys[n][m]);
      }
    }
  }
  else
  {
    CHECK_AND_ASSERT_MES(false, false, "Unsupported rct tx type: " + boost::lexical_cast<std::string>(rv.type));
  }

  // II
  if (rv.type == rct::RCTTypeFull || rv.type == rct::RCTTypeFullBulletproof)
  {
    rv.p.MGs.resize(1);
    rv.p.MGs[0].II.resize(tx.vin.size());
    for (size_t n = 0; n < tx.vin.size(); ++n)
      rv.p.MGs[0].II[n] = rct::ki2rct(boost::get<txin_to_key>(tx.vin[n]).k_image);
  }
  else if (rv.type == rct::RCTTypeSimple || rv.type == rct::RCTTypeSimpleBulletproof)
  {
    CHECK_AND_ASSERT_MES(rv.p.MGs.size() == tx.vin.size(), false, "Bad MGs size");
    for (size_t n = 0; n < tx.vin.size(); ++n)
    {
      rv.p.MGs[n].II.resize(1);
      rv.p.MGs[n].II[0] = rct::ki2rct(boost::get<txin_to_key>(tx.vin[n]).k_image);
    }
  }
  else
  {
    CHECK_AND_ASSERT_MES(false, false, "Unsupported rct tx type: " + boost::lexical_cast<std::string>(rv.type));
  }

  // outPk was already done by handle_incoming_tx

  return true;
}
//------------------------------------------------------------------
// This function validates transaction inputs and their keys.
// FIXME: consider moving functionality specific to one input into
//        check_tx_input() rather than here, and use this function simply
//        to iterate the inputs as necessary (splitting the task
//        using threads, etc.)
bool Blockchain::check_tx_inputs(transaction& tx, tx_verification_context &tvc, uint64_t* pmax_used_block_height)
{
  PERF_TIMER(check_tx_inputs);
  LOG_PRINT_L3("Blockchain::" << __func__);
  size_t sig_index = 0;
  if(pmax_used_block_height)
    *pmax_used_block_height = 0;

  crypto::hash tx_prefix_hash = get_transaction_prefix_hash(tx);

  const uint8_t hf_version = m_hardfork->get_current_version();

  // from hard fork 2, we require mixin at least 2 unless one output cannot mix with 2 others
  // if one output cannot mix with 2 others, we accept at most 1 output that can mix
  if (hf_version >= 7)
  {
    size_t n_unmixable = 0, n_mixable = 0;
    size_t mixin = std::numeric_limits<size_t>::max();
    const size_t min_mixin = hf_version >= HF_VERSION_MIN_MIXIN_6 ? 6 : hf_version >= HF_VERSION_MIN_MIXIN_4 ? 4 : 2;
    for (const auto& txin : tx.vin)
    {
      // non txin_to_key inputs will be rejected below
      if (txin.type() == typeid(txin_to_key))
      {
        const txin_to_key& in_to_key = boost::get<txin_to_key>(txin);
        if (in_to_key.amount == 0)
        {
          // always consider rct inputs mixable. Even if there's not enough rct
          // inputs on the chain to mix with, this is going to be the case for
          // just a few blocks right after the fork at most
          ++n_mixable;
        }
        else
        {
          uint64_t n_outputs = m_db->get_num_outputs(in_to_key.amount);
          MDEBUG("output size " << print_money(in_to_key.amount) << ": " << n_outputs << " available");
          // n_outputs includes the output we're considering
          if (n_outputs <= min_mixin)
            ++n_unmixable;
          else
            ++n_mixable;
        }
        if (in_to_key.key_offsets.size() - 1 < mixin)
          mixin = in_to_key.key_offsets.size() - 1;
      }
    }

    if (mixin < min_mixin)
    {
      if (n_unmixable == 0)
      {
        MERROR_VER("Tx " << get_transaction_hash(tx) << " has too low ring size (" << (mixin + 1) << "), and no unmixable inputs");
        tvc.m_low_mixin = true;
        return false;
      }
      if (n_mixable > 1)
      {
        MERROR_VER("Tx " << get_transaction_hash(tx) << " has too low ring size (" << (mixin + 1) << "), and more than one mixable input with unmixable inputs");
        tvc.m_low_mixin = true;
        return false;
      }
    }

    // min/max tx version based on HF, and we accept v1 txes if having a non mixable
    const size_t max_tx_version = (hf_version <= 3) ? 1 : 2;
    if (tx.version > max_tx_version)
    {
      MERROR_VER("transaction version " << (unsigned)tx.version << " is higher than max accepted version " << max_tx_version);
      tvc.m_verifivation_failed = true;
      return false;
    }
    const size_t min_tx_version = (n_unmixable > 0 ? 1 : (hf_version >= HF_VERSION_ENFORCE_RCT) ? 2 : 1);
    if (tx.version < min_tx_version)
    {
      MERROR_VER("transaction version " << (unsigned)tx.version << " is lower than min accepted version " << min_tx_version);
      tvc.m_verifivation_failed = true;
      return false;
    }
  }

  // from v7, sorted ins
  if (hf_version >= 7) {
    const crypto::key_image *last_key_image = NULL;
    for (size_t n = 0; n < tx.vin.size(); ++n)
    {
      const txin_v &txin = tx.vin[n];
      if (txin.type() == typeid(txin_to_key))
      {
        const txin_to_key& in_to_key = boost::get<txin_to_key>(txin);
        if (last_key_image && memcmp(&in_to_key.k_image, last_key_image, sizeof(*last_key_image)) >= 0)
        {
          MERROR_VER("transaction has unsorted inputs");
          tvc.m_verifivation_failed = true;
          return false;
        }
        last_key_image = &in_to_key.k_image;
      }
    }
  }
  auto it = m_check_txin_table.find(tx_prefix_hash);
  if(it == m_check_txin_table.end())
  {
    m_check_txin_table.emplace(tx_prefix_hash, std::unordered_map<crypto::key_image, bool>());
    it = m_check_txin_table.find(tx_prefix_hash);
    assert(it != m_check_txin_table.end());
  }

  std::vector<std::vector<rct::ctkey>> pubkeys(tx.vin.size());
  std::vector < uint64_t > results;
  results.resize(tx.vin.size(), 0);

  tools::threadpool& tpool = tools::threadpool::getInstance();
  tools::threadpool::waiter waiter;
  const auto waiter_guard = epee::misc_utils::create_scope_leave_handler([&]() { waiter.wait(); });
  int threads = tpool.get_max_concurrency();

  for (const auto& txin : tx.vin)
  {
    // make sure output being spent is of type txin_to_key, rather than
    // e.g. txin_gen, which is only used for miner transactions
    CHECK_AND_ASSERT_MES(txin.type() == typeid(txin_to_key), false, "wrong type id in tx input at Blockchain::check_tx_inputs");
    const txin_to_key& in_to_key = boost::get<txin_to_key>(txin);

    // make sure tx output has key offset(s) (is signed to be used)
    CHECK_AND_ASSERT_MES(in_to_key.key_offsets.size(), false, "empty in_to_key.key_offsets in transaction with id " << get_transaction_hash(tx));

    if(have_tx_keyimg_as_spent(in_to_key.k_image))
    {
      MERROR_VER("Key image already spent in blockchain: " << epee::string_tools::pod_to_hex(in_to_key.k_image));
      tvc.m_double_spend = true;
      return false;
    }

    if (tx.version == 1)
    {
      // basically, make sure number of inputs == number of signatures
      CHECK_AND_ASSERT_MES(sig_index < tx.signatures.size(), false, "wrong transaction: not signature entry for input with index= " << sig_index);

#if defined(CACHE_VIN_RESULTS)
      auto itk = it->second.find(in_to_key.k_image);
      if(itk != it->second.end())
      {
        if(!itk->second)
        {
          MERROR_VER("Failed ring signature for tx " << get_transaction_hash(tx) << "  vin key with k_image: " << in_to_key.k_image << "  sig_index: " << sig_index);
          return false;
        }

        // txin has been verified already, skip
        sig_index++;
        continue;
      }
#endif
    }

    // make sure that output being spent matches up correctly with the
    // signature spending it.
    if(hf_version >= 7){
    if (!check_tx_input(tx.version, in_to_key, tx_prefix_hash, tx.version == 1 ? tx.signatures[sig_index] : std::vector<crypto::signature>(), tx.rct_signatures, pubkeys[sig_index], pmax_used_block_height) && get_current_hard_fork_version() >= 6)

    {
      it->second[in_to_key.k_image] = false;
      MERROR_VER("Failed to check ring signature for tx " << get_transaction_hash(tx) << "  vin key with k_image: " << in_to_key.k_image << "  sig_index: " << sig_index);
      if (pmax_used_block_height) // a default value of NULL is used when called from Blockchain::handle_block_to_main_chain()
      {
        MERROR_VER("  *pmax_used_block_height: " << *pmax_used_block_height);
      }

      return false;
    }
    }
    if (tx.version == 1)
    {
      if (threads > 1)
      {
        // ND: Speedup
        // 1. Thread ring signature verification if possible.
        tpool.submit(&waiter, boost::bind(&Blockchain::check_ring_signature, this, std::cref(tx_prefix_hash), std::cref(in_to_key.k_image), std::cref(pubkeys[sig_index]), std::cref(tx.signatures[sig_index]), std::ref(results[sig_index])));
      }
      else
      {
        if(hf_version >= 7){

        check_ring_signature(tx_prefix_hash, in_to_key.k_image, pubkeys[sig_index], tx.signatures[sig_index], results[sig_index]);
        if (!results[sig_index])
        {
          it->second[in_to_key.k_image] = false;
          MERROR_VER("Failed to check ring signature for tx " << get_transaction_hash(tx) << "  vin key with k_image: " << in_to_key.k_image << "  sig_index: " << sig_index);

          if (pmax_used_block_height)  // a default value of NULL is used when called from Blockchain::handle_block_to_main_chain()
          {
            MERROR_VER("*pmax_used_block_height: " << *pmax_used_block_height);
          }

          return false;
        }
        it->second[in_to_key.k_image] = true;
      }
    }
    }

    sig_index++;
  }
  if (tx.version == 1 && threads > 1)
    waiter.wait();

  if (tx.version == 1)
  {
    if (threads > 1)
    {
      // save results to table, passed or otherwise
      bool failed = false;
      for (size_t i = 0; i < tx.vin.size(); i++)
      {
        const txin_to_key& in_to_key = boost::get<txin_to_key>(tx.vin[i]);
        it->second[in_to_key.k_image] = results[i];
        if(!failed && !results[i])
          failed = true;
      }

       if (failed && get_current_hard_fork_version() >= 6)
      {
        MERROR_VER("Failed to check ring signatures!");
        return false;
      }
    }
  }
  else
  {
    if (!expand_transaction_2(tx, tx_prefix_hash, pubkeys))
    {
      MERROR_VER("Failed to expand rct signatures!");
      return false;
    }

    // from version 2, check ringct signatures
    // obviously, the original and simple rct APIs use a mixRing that's indexes
    // in opposite orders, because it'd be too simple otherwise...
    const rct::rctSig &rv = tx.rct_signatures;
    switch (rv.type)
    {
    case rct::RCTTypeNull: {
      // we only accept no signatures for coinbase txes
      MERROR_VER("Null rct signature on non-coinbase tx");
      return false;
    }
    case rct::RCTTypeSimple:
    case rct::RCTTypeSimpleBulletproof:
    {
      // check all this, either reconstructed (so should really pass), or not
      {
        if (pubkeys.size() != rv.mixRing.size())
        {
          MERROR_VER("Failed to check ringct signatures: mismatched pubkeys/mixRing size");
          return false;
        }
        for (size_t i = 0; i < pubkeys.size(); ++i)
        {
          if (pubkeys[i].size() != rv.mixRing[i].size())
          {
            MERROR_VER("Failed to check ringct signatures: mismatched pubkeys/mixRing size");
            return false;
          }
        }

        for (size_t n = 0; n < pubkeys.size(); ++n)
        {
          for (size_t m = 0; m < pubkeys[n].size(); ++m)
          {
            if (pubkeys[n][m].dest != rct::rct2pk(rv.mixRing[n][m].dest))
            {
              MERROR_VER("Failed to check ringct signatures: mismatched pubkey at vin " << n << ", index " << m);
              return false;
            }
            if (pubkeys[n][m].mask != rct::rct2pk(rv.mixRing[n][m].mask))
            {
              MERROR_VER("Failed to check ringct signatures: mismatched commitment at vin " << n << ", index " << m);
              return false;
            }
          }
        }
      }

      if (rv.p.MGs.size() != tx.vin.size())
      {
        MERROR_VER("Failed to check ringct signatures: mismatched MGs/vin sizes");
        return false;
      }
      for (size_t n = 0; n < tx.vin.size(); ++n)
      {
        if (rv.p.MGs[n].II.empty() || memcmp(&boost::get<txin_to_key>(tx.vin[n]).k_image, &rv.p.MGs[n].II[0], 32))
        {
          MERROR_VER("Failed to check ringct signatures: mismatched key image");
          return false;
        }
      }

      if (!rct::verRctSimple(rv, false))
      {
        MERROR_VER("Failed to check ringct signatures!");
        return false;
      }
      break;
    }
    case rct::RCTTypeFull:
    case rct::RCTTypeFullBulletproof:
    {
      // check all this, either reconstructed (so should really pass), or not
      {
        bool size_matches = true;
        for (size_t i = 0; i < pubkeys.size(); ++i)
          size_matches &= pubkeys[i].size() == rv.mixRing.size();
        for (size_t i = 0; i < rv.mixRing.size(); ++i)
          size_matches &= pubkeys.size() == rv.mixRing[i].size();
        if (!size_matches)
        {
          MERROR_VER("Failed to check ringct signatures: mismatched pubkeys/mixRing size");
          return false;
        }

        for (size_t n = 0; n < pubkeys.size(); ++n)
        {
          for (size_t m = 0; m < pubkeys[n].size(); ++m)
          {
            if (pubkeys[n][m].dest != rct::rct2pk(rv.mixRing[m][n].dest))
            {
              MERROR_VER("Failed to check ringct signatures: mismatched pubkey at vin " << n << ", index " << m);
              return false;
            }
            if (pubkeys[n][m].mask != rct::rct2pk(rv.mixRing[m][n].mask))
            {
              MERROR_VER("Failed to check ringct signatures: mismatched commitment at vin " << n << ", index " << m);
              return false;
            }
          }
        }
      }

      if (rv.p.MGs.size() != 1)
      {
        MERROR_VER("Failed to check ringct signatures: Bad MGs size");
        return false;
      }
      if (rv.p.MGs.empty() || rv.p.MGs[0].II.size() != tx.vin.size())
      {
        MERROR_VER("Failed to check ringct signatures: mismatched II/vin sizes");
        return false;
      }
      for (size_t n = 0; n < tx.vin.size(); ++n)
      {
        if (memcmp(&boost::get<txin_to_key>(tx.vin[n]).k_image, &rv.p.MGs[0].II[n], 32))
        {
          MERROR_VER("Failed to check ringct signatures: mismatched II/vin sizes");
          return false;
        }
      }

      if (!rct::verRct(rv, false))
      {
        MERROR_VER("Failed to check ringct signatures!");
        return false;
      }
      break;
    }
    default:
      MERROR_VER("Unsupported rct type: " << rv.type);
      return false;
    }
  }
  return true;
}

//------------------------------------------------------------------
void Blockchain::check_ring_signature(const crypto::hash &tx_prefix_hash, const crypto::key_image &key_image, const std::vector<rct::ctkey> &pubkeys, const std::vector<crypto::signature>& sig, uint64_t &result)
{
  std::vector<const crypto::public_key *> p_output_keys;
  for (auto &key : pubkeys)
  {
    // rct::key and crypto::public_key have the same structure, avoid object ctor/memcpy
    p_output_keys.push_back(&(const crypto::public_key&)key.dest);
  }

  result = crypto::check_ring_signature(tx_prefix_hash, key_image, p_output_keys, sig.data()) ? 1 : 0;
}

//------------------------------------------------------------------
static uint64_t get_fee_quantization_mask()
{
  static uint64_t mask = 0;
  if (mask == 0)
  {
    mask = 1;
    for (size_t n = PER_KB_FEE_QUANTIZATION_DECIMALS; n < CRYPTONOTE_DISPLAY_DECIMAL_POINT; ++n)
      mask *= 10;
  }
  return mask;
}

//------------------------------------------------------------------
uint64_t Blockchain::get_dynamic_per_kb_fee(uint64_t block_reward, size_t median_block_size, uint8_t version)
{
  const uint64_t min_block_size = get_min_block_size(version);
  const uint64_t fee_per_kb_base = version >= 5 ? DYNAMIC_FEE_PER_KB_BASE_FEE_V5 : DYNAMIC_FEE_PER_KB_BASE_FEE;

  if (median_block_size < min_block_size)
    median_block_size = min_block_size;

  uint64_t unscaled_fee_per_kb = (fee_per_kb_base * min_block_size / median_block_size);
  uint64_t hi, lo = mul128(unscaled_fee_per_kb, block_reward, &hi);
  static_assert(DYNAMIC_FEE_PER_KB_BASE_BLOCK_REWARD % 1000000 == 0, "DYNAMIC_FEE_PER_KB_BASE_BLOCK_REWARD must be divisible by 1000000");
  static_assert(DYNAMIC_FEE_PER_KB_BASE_BLOCK_REWARD / 1000000 <= std::numeric_limits<uint32_t>::max(), "DYNAMIC_FEE_PER_KB_BASE_BLOCK_REWARD is too large");

  // divide in two steps, since the divisor must be 32 bits, but DYNAMIC_FEE_PER_KB_BASE_BLOCK_REWARD isn't
  div128_32(hi, lo, DYNAMIC_FEE_PER_KB_BASE_BLOCK_REWARD / 1000000, &hi, &lo);
  div128_32(hi, lo, 1000000, &hi, &lo);
  assert(hi == 0);

  // quantize fee up to 8 decimals
  uint64_t mask = get_fee_quantization_mask();
  uint64_t qlo = (lo + mask - 1) / mask * mask;
  MDEBUG("lo " << print_money(lo) << ", qlo " << print_money(qlo) << ", mask " << mask);

  return qlo;
}

//------------------------------------------------------------------
bool Blockchain::check_fee(size_t blob_size, uint64_t fee) const
{
  const uint8_t version = get_current_hard_fork_version();

  uint64_t fee_per_kb;
  if (version < 7)
  {
	  return fee >= LEGACY_MINIMUM_FEE;
  }
  else
  {
    uint64_t median = m_current_block_cumul_sz_limit / 2;
    uint64_t already_generated_coins = m_db->height() ? m_db->get_block_already_generated_coins(m_db->height() - 1) : 0;
    uint64_t base_reward;
    if (!get_block_reward(median, 1, already_generated_coins, 0,base_reward, version,m_db->height()))
      return false;
    fee_per_kb = get_dynamic_per_kb_fee(base_reward, median, version);
  }
  MDEBUG("Using " << print_money(fee_per_kb) << "/kB fee");

  uint64_t needed_fee = blob_size / 1024;
  needed_fee += (blob_size % 1024) ? 1 : 0;
  needed_fee *= fee_per_kb;

  if (fee < needed_fee - needed_fee / 50) // keep a little 2% buffer on acceptance - no integer overflow
  {
    MERROR_VER("transaction fee is not enough: " << print_money(fee) << ", minimum fee: " << print_money(needed_fee));
    return false;
  }
  return true;
}

//------------------------------------------------------------------
uint64_t Blockchain::get_dynamic_per_kb_fee_estimate(uint64_t grace_blocks) const
{
  const uint8_t version = get_current_hard_fork_version();

  if (version < HF_VERSION_DYNAMIC_FEE)
    return FEE_PER_KB;

  if (grace_blocks >= CRYPTONOTE_REWARD_BLOCKS_WINDOW)
    grace_blocks = CRYPTONOTE_REWARD_BLOCKS_WINDOW - 1;

  const uint64_t min_block_size = get_min_block_size(version);
  std::vector<size_t> sz;
  get_last_n_blocks_sizes(sz, CRYPTONOTE_REWARD_BLOCKS_WINDOW - grace_blocks);
  for (size_t i = 0; i < grace_blocks; ++i)
    sz.push_back(min_block_size);

  uint64_t median = epee::misc_utils::median(sz);
  if(median <= min_block_size)
    median = min_block_size;

  uint64_t already_generated_coins = m_db->height() ? m_db->get_block_already_generated_coins(m_db->height() - 1) : 0;
  uint64_t base_reward;
  uint64_t fee = get_dynamic_per_kb_fee(base_reward, median, version);
  MDEBUG("Estimating " << grace_blocks << "-block fee at " << print_money(fee) << "/kB");
  if (!get_block_reward(median, 1, already_generated_coins,fee, base_reward, version,m_db->height()))
  {
    MERROR("Failed to determine block reward, using placeholder " << print_money(BLOCK_REWARD_OVERESTIMATE) << " as a high bound");
    base_reward = BLOCK_REWARD_OVERESTIMATE;
  }


  return fee;
}

//------------------------------------------------------------------
// This function checks to see if a tx is unlocked.  unlock_time is either
// a block index or a unix time.
bool Blockchain::is_tx_spendtime_unlocked(uint64_t unlock_time) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  if(unlock_time < CRYPTONOTE_MAX_BLOCK_NUMBER)
  {
    // ND: Instead of calling get_current_blockchain_height(), call m_db->height()
    //    directly as get_current_blockchain_height() locks the recursive mutex.
    if(m_db->height()-1 + CRYPTONOTE_LOCKED_TX_ALLOWED_DELTA_BLOCKS >= unlock_time)
      return true;
    else
      return false;
  }
  else
  {
    //interpret as time
    uint64_t current_time = static_cast<uint64_t>(time(NULL));
    if(current_time + (get_current_hard_fork_version() < 2 ? CRYPTONOTE_LOCKED_TX_ALLOWED_DELTA_SECONDS_V1 : CRYPTONOTE_LOCKED_TX_ALLOWED_DELTA_SECONDS_V2) >= unlock_time)
      return true;
    else
      return false;
  }
  return false;
}
//------------------------------------------------------------------
// This function locates all outputs associated with a given input (mixins)
// and validates that they exist and are usable.  It also checks the ring
// signature for each input.
bool Blockchain::check_tx_input(size_t tx_version, const txin_to_key& txin, const crypto::hash& tx_prefix_hash, const std::vector<crypto::signature>& sig, const rct::rctSig &rct_signatures, std::vector<rct::ctkey> &output_keys, uint64_t* pmax_related_block_height)
{
  LOG_PRINT_L3("Blockchain::" << __func__);

  // ND:
  // 1. Disable locking and make method private.
  //CRITICAL_REGION_LOCAL(m_blockchain_lock);

  struct outputs_visitor
  {
    std::vector<rct::ctkey >& m_output_keys;
    const Blockchain& m_bch;
    outputs_visitor(std::vector<rct::ctkey>& output_keys, const Blockchain& bch) :
      m_output_keys(output_keys), m_bch(bch)
    {
    }
    bool handle_output(uint64_t unlock_time, const crypto::public_key &pubkey, const rct::key &commitment)
    {
      //check tx unlock time
      if (!m_bch.is_tx_spendtime_unlocked(unlock_time))
      {
        MERROR_VER("One of outputs for one of inputs has wrong tx.unlock_time = " << unlock_time);
        return false;
      }

      // The original code includes a check for the output corresponding to this input
      // to be a txout_to_key. This is removed, as the database does not store this info,
      // but only txout_to_key outputs are stored in the DB in the first place, done in
      // Blockchain*::add_output

      m_output_keys.push_back(rct::ctkey({rct::pk2rct(pubkey), commitment}));
      return true;
    }
  };

  output_keys.clear();

  // collect output keys
  outputs_visitor vi(output_keys, *this);
  if (!scan_outputkeys_for_indexes(tx_version, txin, vi, tx_prefix_hash, pmax_related_block_height) && get_current_hard_fork_version() >= 7)

  {
    MERROR_VER("Failed to get output keys for tx with amount = " << print_money(txin.amount) << " and count indexes " << txin.key_offsets.size());
    return false;
  }

  if(txin.key_offsets.size() != output_keys.size() && get_current_hard_fork_version() >= 7)
  {
    MERROR_VER("Output keys for tx with amount = " << txin.amount << " and count indexes " << txin.key_offsets.size() << " returned wrong keys count " << output_keys.size());
    return false;
  }
  if (tx_version == 1 && get_current_hard_fork_version() >= 7) {
    CHECK_AND_ASSERT_MES(sig.size() == output_keys.size(), false, "internal error: tx signatures count=" << sig.size() << " mismatch with outputs keys count for inputs=" << output_keys.size());
  }
  // rct_signatures will be expanded after this
  return true;
}
//------------------------------------------------------------------
//TODO: Is this intended to do something else?  Need to look into the todo there.
uint64_t Blockchain::get_adjusted_time() const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  //TODO: add collecting median time
  return time(NULL);
}
//------------------------------------------------------------------
//TODO: revisit, has changed a bit on upstream
bool Blockchain::check_block_timestamp(std::vector<uint64_t>& timestamps, const block& b, uint64_t& median_ts) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  median_ts = epee::misc_utils::median(timestamps);

  if(b.timestamp < median_ts)
  {
    MERROR_VER("Timestamp of block with id: " << get_block_hash(b) << ", " << b.timestamp << ", less than median of last " << BLOCKCHAIN_TIMESTAMP_CHECK_WINDOW << " blocks, " << median_ts);
    return false;
  }

  return true;
}
//------------------------------------------------------------------
// This function grabs the timestamps from the most recent <n> blocks,
// where n = BLOCKCHAIN_TIMESTAMP_CHECK_WINDOW.  If there are not those many
// blocks in the blockchain, the timestap is assumed to be valid.  If there
// are, this function returns:
//   true if the block's timestamp is not less than the timestamp of the
//       median of the selected blocks
//   false otherwise
bool Blockchain::check_block_timestamp(const block& b, uint64_t& median_ts) const
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  if(m_db->height() < 24861){
    if(b.timestamp > get_adjusted_time() + (60 * 60 * 2))
    {
      MERROR_VER("Timestamp of block with id: " << get_block_hash(b) << ", " << b.timestamp << ", bigger than adjusted time + 2 hours");
      return false;
    }
  }else if(m_db->height() >= 24861){
  if(b.timestamp > get_adjusted_time() + CRYPTONOTE_BLOCK_FUTURE_TIME_LIMIT)
  {
      MERROR_VER("Timestamp of block with id: " << get_block_hash(b) << ", " << b.timestamp << ", bigger than adjusted time + 2 hours");
      return false;
  }
}else if(m_db->height() >= 70000){
  if(b.timestamp > get_adjusted_time() + CRYPTONOTE_BLOCK_FUTURE_TIME_LIMIT)
  {
      MERROR_VER("Timestamp of block with id: " << get_block_hash(b) << ", " << b.timestamp << ", bigger than adjusted time + 2 hours");
      return false;
  }
}


  // if not enough blocks, no proper median yet, return true
  if(m_db->height() < BLOCKCHAIN_TIMESTAMP_CHECK_WINDOW)
  {
    return true;
  }

  std::vector<uint64_t> timestamps;
  auto h = m_db->height();

  // need most recent 60 blocks, get index of first of those
  size_t offset = h - BLOCKCHAIN_TIMESTAMP_CHECK_WINDOW;
  for(;offset < h; ++offset)
  {
    timestamps.push_back(m_db->get_block_timestamp(offset));
  }

  return check_block_timestamp(timestamps, b, median_ts);
}
//------------------------------------------------------------------
void Blockchain::return_tx_to_pool(std::vector<transaction> &txs)
{
  uint8_t version = get_current_hard_fork_version();
  for (auto& tx : txs)
  {
    cryptonote::tx_verification_context tvc = AUTO_VAL_INIT(tvc);
    // We assume that if they were in a block, the transactions are already
    // known to the network as a whole. However, if we had mined that block,
    // that might not be always true. Unlikely though, and always relaying
    // these again might cause a spike of traffic as many nodes re-relay
    // all the transactions in a popped block when a reorg happens.
    if (!m_tx_pool.add_tx(tx, tvc, true, true, false, version) && version >= 7
  )
    {
      MERROR("Failed to return taken transaction with hash: " << get_transaction_hash(tx) << " to tx_pool");
    }
  }
}
//------------------------------------------------------------------
bool Blockchain::flush_txes_from_pool(const std::list<crypto::hash> &txids)
{
  CRITICAL_REGION_LOCAL(m_tx_pool);

  bool res = true;
  for (const auto &txid: txids)
  {
    cryptonote::transaction tx;
    size_t blob_size;
    uint64_t fee;
    bool relayed, do_not_relay, double_spend_seen;
    MINFO("Removing txid " << txid << " from the pool");
    if(m_tx_pool.have_tx(txid) && !m_tx_pool.take_tx(txid, tx, blob_size, fee, relayed, do_not_relay, double_spend_seen))
    {
      MERROR("Failed to remove txid " << txid << " from the pool");
      res = false;
    }
  }
  return res;
}
//------------------------------------------------------------------
//      Needs to validate the block and acquire each transaction from the
//      transaction mem_pool, then pass the block and transactions to
//      m_db->add_block()
bool Blockchain::handle_block_to_main_chain(const block& bl, const crypto::hash& id, block_verification_context& bvc)
{
  LOG_PRINT_L3("Blockchain::" << __func__);

  TIME_MEASURE_START(block_processing_time);
  CRITICAL_REGION_LOCAL(m_blockchain_lock);
  TIME_MEASURE_START(t1);

  static bool seen_future_version = false;

  m_db->block_txn_start(true);
  if(bl.prev_id != get_tail_id())
  {
    MERROR_VER("Block with id: " << id << std::endl << "has wrong prev_id: " << bl.prev_id << std::endl << "expected: " << get_tail_id());
leave:
    m_db->block_txn_stop();
    return false;
  }

  // warn users if they're running an old version
  if (!seen_future_version && bl.major_version > m_hardfork->get_ideal_version())
  {
    seen_future_version = true;
    const el::Level level = el::Level::Warning;
    MCLOG_RED(level, "global", "**********************************************************************");
    MCLOG_RED(level, "global", "A block was seen on the network with a version higher than the last");
    MCLOG_RED(level, "global", "known one. This may be an old version of the daemon, and a software");
    MCLOG_RED(level, "global", "update may be required to sync further. Try running: update check");
    MCLOG_RED(level, "global", "**********************************************************************");
  }


  if (!m_hardfork->check(bl))
  {
    MERROR_VER("Block with id: " << id << std::endl << "has old version: " << (unsigned)bl.major_version << std::endl << "current: " << (unsigned)m_hardfork->get_current_version());
    bvc.m_verifivation_failed = true;
    goto leave;
  }



  TIME_MEASURE_FINISH(t1);
  TIME_MEASURE_START(t2);

  // make sure block timestamp is not less than the median timestamp
  // of a set number of the most recent blocks.
  if(!check_block_timestamp(bl))
  {
    MERROR_VER("Block with id: " << id << std::endl << "has invalid timestamp: " << bl.timestamp);
    bvc.m_verifivation_failed = true;
    goto leave;
  }

  TIME_MEASURE_FINISH(t2);
  //check proof of work
  TIME_MEASURE_START(target_calculating_time);

  // get the target difficulty for the block.
  // the calculation can overflow, among other failure cases,
  // so we need to check the return type.
  // FIXME: get_difficulty_for_next_block can also assert, look into
  // changing this to throwing exceptions instead so we can clean up.
  difficulty_type current_diffic = get_difficulty_for_next_block();
  CHECK_AND_ASSERT_MES(current_diffic, false, "!!!!!!!!! difficulty overhead !!!!!!!!!");

  TIME_MEASURE_FINISH(target_calculating_time);

  TIME_MEASURE_START(longhash_calculating_time);

  crypto::hash proof_of_work = null_hash;

  // Formerly the code below contained an if loop with the following condition
  // !m_checkpoints.is_in_checkpoint_zone(get_current_blockchain_height())
  // however, this caused the daemon to not bother checking PoW for blocks
  // before checkpoints, which is very dangerous behaviour. We moved the PoW
  // validation out of the next chunk of code to make sure that we correctly
  // check PoW now.
  // FIXME: height parameter is not used...should it be used or should it not
  // be a parameter?
  // validate proof_of_work versus difficulty target
  bool precomputed = false;
  bool fast_check = false;
#if defined(PER_BLOCK_CHECKPOINT)
  if (m_db->height() < m_blocks_hash_check.size())
  {
    auto hash = get_block_hash(bl);
    const auto &expected_hash = m_blocks_hash_check[m_db->height()];
    if (expected_hash != crypto::null_hash)
    {
      if (memcmp(&hash, &expected_hash, sizeof(hash)) != 0)
      {
        MERROR_VER("Block with id is INVALID: " << id);
        bvc.m_verifivation_failed = true;
        goto leave;
      }
      fast_check = true;
    }
    else
    {
      MCINFO("verify", "No pre-validated hash at height " << m_db->height() << ", verifying fully");
    }
  }
  else
#endif
  {
    auto it = m_blocks_longhash_table.find(id);
    if (it != m_blocks_longhash_table.end())
    {
      precomputed = true;
      proof_of_work = it->second;
    } else{
		if (!check_proof_of_work(bl, current_diffic, proof_of_work) && get_current_hard_fork_version() >= 6)
		{
			MERROR_VER("Block with id: " << id << std::endl << "does not have enough proof of work: " << proof_of_work << std::endl << "unexpected difficulty: " << current_diffic);
			bvc.m_verifivation_failed = true;
			goto leave;
		}
	}

    // validate proof_of_work versus difficulty target
    /*if(!check_hash(proof_of_work, current_diffic))
    {
      MERROR_VER("Block with id: " << id << std::endl << "does not have enough proof of work: " << proof_of_work << std::endl << "unexpected difficulty: " << current_diffic);
      bvc.m_verifivation_failed = true;
      goto leave;
    }
  }*/
}
  // If we're at a checkpoint, ensure that our hardcoded checkpoint hash
  // is correct.
  if(m_checkpoints.is_in_checkpoint_zone(get_current_blockchain_height()))
  {
    if(!m_checkpoints.check_block(get_current_blockchain_height(), id))
    {
      LOG_ERROR("CHECKPOINT VALIDATION FAILED");
      bvc.m_verifivation_failed = true;
      goto leave;
    }
  }

  TIME_MEASURE_FINISH(longhash_calculating_time);
  if (precomputed)
    longhash_calculating_time += m_fake_pow_calc_time;

  TIME_MEASURE_START(t3);

  // sanity check basic miner tx properties;
  if(!prevalidate_miner_transaction(bl, m_db->height()))
  {
    MERROR_VER("Block with id: " << id << " failed to pass prevalidation");
    bvc.m_verifivation_failed = true;
    goto leave;
  }

  size_t coinbase_blob_size = get_object_blobsize(bl.miner_tx);
  size_t cumulative_block_size = coinbase_blob_size;

  std::vector<transaction> txs;
  key_images_container keys;

  uint64_t fee_summary = 0;
  uint64_t t_checktx = 0;
  uint64_t t_exists = 0;
  uint64_t t_pool = 0;
  uint64_t t_dblspnd = 0;
  TIME_MEASURE_FINISH(t3);

// XXX old code adds miner tx here

  size_t tx_index = 0;
  // Iterate over the block's transaction hashes, grabbing each
  // from the tx_pool and validating them.  Each is then added
  // to txs.  Keys spent in each are added to <keys> by the double spend check.
  for (const crypto::hash& tx_id : bl.tx_hashes)
  {
    transaction tx;
    size_t blob_size = 0;
    uint64_t fee = 0;
    bool relayed = false, do_not_relay = false, double_spend_seen = false;
    TIME_MEASURE_START(aa);

// XXX old code does not check whether tx exists
    if (m_db->tx_exists(tx_id))
    {
      MERROR("Block with id: " << id << " attempting to add transaction already in blockchain with id: " << tx_id);
      bvc.m_verifivation_failed = true;
      return_tx_to_pool(txs);
      goto leave;
    }

    TIME_MEASURE_FINISH(aa);
    t_exists += aa;
    TIME_MEASURE_START(bb);

    // get transaction with hash <tx_id> from tx_pool
    if(!m_tx_pool.take_tx(tx_id, tx, blob_size, fee, relayed, do_not_relay, double_spend_seen) && get_current_hard_fork_version() >= 6)

    {
      MERROR_VER("Block with id: " << id  << " has at least one unknown transaction with id: " << tx_id);
      bvc.m_verifivation_failed = true;
      return_tx_to_pool(txs);
      goto leave;
    }

    TIME_MEASURE_FINISH(bb);
    t_pool += bb;
    // add the transaction to the temp list of transactions, so we can either
    // store the list of transactions all at once or return the ones we've
    // taken from the tx_pool back to it if the block fails verification.
    txs.push_back(tx);
    TIME_MEASURE_START(dd);

    // FIXME: the storage should not be responsible for validation.
    //        If it does any, it is merely a sanity check.
    //        Validation is the purview of the Blockchain class
    //        - TW
    //
    // ND: this is not needed, db->add_block() checks for duplicate k_images and fails accordingly.
    // if (!check_for_double_spend(tx, keys))
    // {
    //     LOG_PRINT_L0("Double spend detected in transaction (id: " << tx_id);
    //     bvc.m_verifivation_failed = true;
    //     break;
    // }

    TIME_MEASURE_FINISH(dd);
    t_dblspnd += dd;
    TIME_MEASURE_START(cc);

#if defined(PER_BLOCK_CHECKPOINT)
    if (!fast_check)
#endif
    {
      // validate that transaction inputs and the keys spending them are correct.
      tx_verification_context tvc;
      if(!check_tx_inputs(tx, tvc) && get_current_hard_fork_version() >= 7)
      {
        MERROR_VER("Block with id: " << id  << " has at least one transaction (id: " << tx_id << ") with wrong inputs.");

        //TODO: why is this done?  make sure that keeping invalid blocks makes sense.
        add_block_as_invalid(bl, id);
        MERROR_VER("Block with id " << id << " added as invalid because of wrong inputs in transactions");
        bvc.m_verifivation_failed = true;
        return_tx_to_pool(txs);
        goto leave;
      }
    }
#if defined(PER_BLOCK_CHECKPOINT)
    else
    {
      // ND: if fast_check is enabled for blocks, there is no need to check
      // the transaction inputs, but do some sanity checks anyway.
      if (tx_index >= m_blocks_txs_check.size() || memcmp(&m_blocks_txs_check[tx_index++], &tx_id, sizeof(tx_id)) != 0)
      {
        MERROR_VER("Block with id: " << id << " has at least one transaction (id: " << tx_id << ") with wrong inputs.");
        //TODO: why is this done?  make sure that keeping invalid blocks makes sense.
        add_block_as_invalid(bl, id);
        MERROR_VER("Block with id " << id << " added as invalid because of wrong inputs in transactions");
        bvc.m_verifivation_failed = true;
        return_tx_to_pool(txs);
        goto leave;
      }
    }
#endif

    TIME_MEASURE_FINISH(cc);
    t_checktx += cc;
    if(m_db->height()  == 1158){
      MERROR("Transaction(" << tx_id << ") Fee: " << print_money(fee));

    }
    fee_summary += fee;
    cumulative_block_size += blob_size;
  }

  m_blocks_txs_check.clear();

  TIME_MEASURE_START(vmt);
  uint64_t base_reward = 0;
  uint64_t already_generated_coins = 0;

  if(m_db->height() > 1){
   already_generated_coins = m_db->get_block_already_generated_coins(m_db->height() - 1);
} else{
  already_generated_coins = 0;
}
  MERROR(fee_summary);
  if(!validate_miner_transaction(bl, cumulative_block_size, fee_summary, base_reward, already_generated_coins, bvc.m_partial_block_reward, m_hardfork->get_current_version() >= 6))
  {
    MERROR_VER("Block with id: " << id << " has incorrect miner transaction");
    bvc.m_verifivation_failed = true;
    return_tx_to_pool(txs);
    goto leave;
  }

  TIME_MEASURE_FINISH(vmt);
  size_t block_size;
  difficulty_type cumulative_difficulty;

  // populate various metadata about the block to be stored alongside it.
  block_size = cumulative_block_size;
  cumulative_difficulty = current_diffic;
  // In the "tail" state when the minimum subsidy (implemented in get_block_reward) is in effect, the number of
  // coins will eventually exceed MONEY_SUPPLY and overflow a uint64. To prevent overflow, cap already_generated_coins
  // at MONEY_SUPPLY. already_generated_coins is only used to compute the block subsidy and MONEY_SUPPLY yields a
  // subsidy of 0 under the base formula and therefore the minimum subsidy >0 in the tail state.
  already_generated_coins = already_generated_coins + base_reward;
  if(m_db->height())
    cumulative_difficulty += m_db->get_block_cumulative_difficulty(m_db->height() - 1);

  TIME_MEASURE_FINISH(block_processing_time);
  if(precomputed)
    block_processing_time += m_fake_pow_calc_time;

  m_db->block_txn_stop();
  TIME_MEASURE_START(addblock);
  uint64_t new_height = 0;
  if (!bvc.m_verifivation_failed)
  {
    try
    {
      new_height = m_db->add_block(bl, block_size, cumulative_difficulty, already_generated_coins, txs);
    }
    catch (const KEY_IMAGE_EXISTS& e)
    {
      LOG_ERROR("Error adding block with hash: " << id << " to blockchain, what = " << e.what());
      bvc.m_verifivation_failed = true;
      return_tx_to_pool(txs);
      return false;
    }
    catch (const std::exception& e)
    {
      //TODO: figure out the best way to deal with this failure
      LOG_ERROR("Error adding block with hash: " << id << " to blockchain, what = " << e.what());
      return_tx_to_pool(txs);
      return false;
    }
  }
  else
  {
    LOG_ERROR("Blocks that failed verification should not reach here");
  }

  TIME_MEASURE_FINISH(addblock);

  // do this after updating the hard fork state since the size limit may change due to fork
  update_next_cumulative_size_limit();

  MINFO("+++++ BLOCK SUCCESSFULLY ADDED" << std::endl << "id:\t" << id << std::endl << "PoW:\t" << proof_of_work << std::endl << "HEIGHT " << new_height-1 << ", difficulty:\t" << current_diffic << std::endl << "block reward: " << print_money(fee_summary + base_reward) << "(" << print_money(base_reward) << " + " << print_money(fee_summary) << "), coinbase_blob_size: " << coinbase_blob_size << ", cumulative size: " << cumulative_block_size << ", " << block_processing_time << "(" << target_calculating_time << "/" << longhash_calculating_time << ")ms");
  if(m_show_time_stats)
  {
    MINFO("Height: " << new_height << " blob: " << coinbase_blob_size << " cumm: "
        << cumulative_block_size << " p/t: " << block_processing_time << " ("
        << target_calculating_time << "/" << longhash_calculating_time << "/"
        << t1 << "/" << t2 << "/" << t3 << "/" << t_exists << "/" << t_pool
        << "/" << t_checktx << "/" << t_dblspnd << "/" << vmt << "/" << addblock << ")ms");
  }

  bvc.m_added_to_main_chain = true;
  ++m_sync_counter;

  // appears to be a NOP *and* is called elsewhere.  wat?
  m_tx_pool.on_blockchain_inc(new_height, id);

  return true;
}
//------------------------------------------------------------------
bool Blockchain::update_next_cumulative_size_limit()
{
  uint64_t full_reward_zone = get_min_block_size(get_current_hard_fork_version());

  LOG_PRINT_L3("Blockchain::" << __func__);
  std::vector<size_t> sz;
  get_last_n_blocks_sizes(sz, CRYPTONOTE_REWARD_BLOCKS_WINDOW);

  uint64_t median = epee::misc_utils::median(sz);
  m_current_block_cumul_sz_median = median;
  if(median <= full_reward_zone)
    median = full_reward_zone;

  m_current_block_cumul_sz_limit = median*2;
  return true;
}
//------------------------------------------------------------------
bool Blockchain::add_new_block(const block& bl_, block_verification_context& bvc)
{
  LOG_PRINT_L3("Blockchain::" << __func__);
  //copy block here to let modify block.target
  block bl = bl_;
  crypto::hash id = get_block_hash(bl);
  CRITICAL_REGION_LOCAL(m_tx_pool);//to avoid deadlock lets lock tx_pool for whole add/reorganize process
  CRITICAL_REGION_LOCAL1(m_blockchain_lock);
  m_db->block_txn_start(true);
  if(have_block(id))
  {
    LOG_PRINT_L3("block with id = " << id << " already exists");
    bvc.m_already_exists = true;
    m_db->block_txn_stop();
    m_blocks_txs_check.clear();
    return false;
  }

  //check that block refers to chain tail
  if(!(bl.prev_id == get_tail_id()))
  {
    //chain switching or wrong block
    bvc.m_added_to_main_chain = false;
    m_db->block_txn_stop();
    bool r = handle_alternative_block(bl, id, bvc);
    m_blocks_txs_check.clear();
    return r;
    //never relay alternative blocks
  }

  m_db->block_txn_stop();
  return handle_block_to_main_chain(bl, id, bvc);
}
//------------------------------------------------------------------
//TODO: Refactor, consider returning a failure height and letting
//      caller decide course of action.
void Blockchain::check_against_checkpoints(const checkpoints& points, bool enforce)
{
  const auto& pts = points.get_points();
  bool stop_batch;

  CRITICAL_REGION_LOCAL(m_blockchain_lock);
  stop_batch = m_db->batch_start();
  for (const auto& pt : pts)
  {
    // if the checkpoint is for a block we don't have yet, move on
    if (pt.first >= m_db->height())
    {
      continue;
    }

    if (!points.check_block(pt.first, m_db->get_block_hash_from_height(pt.first)))
    {
      // if asked to enforce checkpoints, roll back to a couple of blocks before the checkpoint
      if (enforce)
      {
        LOG_ERROR("Local blockchain failed to pass a checkpoint, rolling back!");
        std::list<block> empty;
        rollback_blockchain_switching(empty, pt.first - 2);
      }
      else
      {
        LOG_ERROR("WARNING: local blockchain failed to pass a MoneroPulse checkpoint, and you could be on a fork. You should either sync up from scratch, OR download a fresh blockchain bootstrap, OR enable checkpoint enforcing with the --enforce-dns-checkpointing command-line option");
      }
    }
  }
  if (stop_batch)
    m_db->batch_stop();
}
//------------------------------------------------------------------
// returns false if any of the checkpoints loading returns false.
// That should happen only if a checkpoint is added that conflicts
// with an existing checkpoint.
bool Blockchain::update_checkpoints(const std::string& file_path, bool check_dns)
{
  if (!m_checkpoints.load_checkpoints_from_json(file_path))
  {
      return false;
  }

  // if we're checking both dns and json, load checkpoints from dns.
  // if we're not hard-enforcing dns checkpoints, handle accordingly
  if (m_enforce_dns_checkpoints && check_dns && !m_offline)
  {
    if (!m_checkpoints.load_checkpoints_from_dns())
    {
      return false;
    }
  }
  else if (check_dns && !m_offline)
  {
    checkpoints dns_points;
    dns_points.load_checkpoints_from_dns();
    if (m_checkpoints.check_for_conflicts(dns_points))
    {
      check_against_checkpoints(dns_points, false);
    }
    else
    {
      MERROR("One or more checkpoints fetched from DNS conflicted with existing checkpoints!");
    }
  }

  check_against_checkpoints(m_checkpoints, true);

  return true;
}
//------------------------------------------------------------------
void Blockchain::set_enforce_dns_checkpoints(bool enforce_checkpoints)
{
  m_enforce_dns_checkpoints = enforce_checkpoints;
}

//------------------------------------------------------------------
void Blockchain::block_longhash_worker(uint64_t height, const std::vector<block> &blocks, std::unordered_map<crypto::hash, crypto::hash> &map) const
{
  TIME_MEASURE_START(t);

  for (const auto & block : blocks)
 {
   if (m_cancel)
      break;
   crypto::hash id = get_block_hash(block);
   crypto::hash pow;
   if (block.major_version == BLOCK_MAJOR_VERSION_1 || block.major_version >= BLOCK_MAJOR_VERSION_7) {
     if (!get_block_longhash(block, pow, 0)) {
       MERROR("Block longhash worker: failed to get block longhash");
     } else {
       map.emplace(id, pow);
     }
   } else {
     if (!get_bytecoin_block_longhash(block, pow)) {
       MERROR("Block longhash worker: failed to get bytecoin block longhash");
     } else {
       map.emplace(id, pow);
     }
   }
 }

  TIME_MEASURE_FINISH(t);
}

//------------------------------------------------------------------
bool Blockchain::cleanup_handle_incoming_blocks(bool force_sync)
{
  bool success = false;

  MTRACE("Blockchain::" << __func__);
  CRITICAL_REGION_BEGIN(m_blockchain_lock);
  TIME_MEASURE_START(t1);

  try
  {
    m_db->batch_stop();
    success = true;
  }
  catch (const std::exception &e)
  {
    MERROR("Exception in cleanup_handle_incoming_blocks: " << e.what());
  }

  if (success && m_sync_counter > 0)
  {
    if (force_sync)
    {
      if(m_db_sync_mode != db_nosync)
        store_blockchain();
      m_sync_counter = 0;
    }
    else if (m_db_blocks_per_sync && m_sync_counter >= m_db_blocks_per_sync)
    {
      if(m_db_sync_mode == db_async)
      {
        m_sync_counter = 0;
        m_async_service.dispatch(boost::bind(&Blockchain::store_blockchain, this));
      }
      else if(m_db_sync_mode == db_sync)
      {
        store_blockchain();
      }
      else // db_nosync
      {
        // DO NOTHING, not required to call sync.
      }
    }
  }

  TIME_MEASURE_FINISH(t1);
  m_blocks_longhash_table.clear();
  m_scan_table.clear();
  m_blocks_txs_check.clear();
  m_check_txin_table.clear();

  // when we're well clear of the precomputed hashes, free the memory
  if (!m_blocks_hash_check.empty() && m_db->height() > m_blocks_hash_check.size() + 4096)
  {
    MINFO("Dumping block hashes, we're now 4k past " << m_blocks_hash_check.size());
    m_blocks_hash_check.clear();
    m_blocks_hash_check.shrink_to_fit();
  }

  CRITICAL_REGION_END();
  m_tx_pool.unlock();

  return success;
}

//------------------------------------------------------------------
//FIXME: unused parameter txs
void Blockchain::output_scan_worker(const uint64_t amount, const std::vector<uint64_t> &offsets, std::vector<output_data_t> &outputs, std::unordered_map<crypto::hash, cryptonote::transaction> &txs) const
{
  try
  {
    m_db->get_output_key(amount, offsets, outputs, true);
  }
  catch (const std::exception& e)
  {
    MERROR_VER("EXCEPTION: " << e.what());
  }
  catch (...)
  {

  }
}

uint64_t Blockchain::prevalidate_block_hashes(uint64_t height, const std::list<crypto::hash> &hashes)
{
  // new: . . . . . X X X X X . . . . . .
  // pre: A A A A B B B B C C C C D D D D

  // easy case: height >= hashes
  if (height >= m_blocks_hash_of_hashes.size() * HASH_OF_HASHES_STEP)
    return hashes.size();

  // if we're getting old blocks, we might have jettisoned the hashes already
  if (m_blocks_hash_check.empty())
    return hashes.size();

  // find hashes encompassing those block
  size_t first_index = height / HASH_OF_HASHES_STEP;
  size_t last_index = (height + hashes.size() - 1) / HASH_OF_HASHES_STEP;
  MDEBUG("Blocks " << height << " - " << (height + hashes.size() - 1) << " start at " << first_index << " and end at " << last_index);

  // case of not enough to calculate even a single hash
  if (first_index == last_index && hashes.size() < HASH_OF_HASHES_STEP && (height + hashes.size()) % HASH_OF_HASHES_STEP)
    return hashes.size();

  // build hashes vector to hash hashes together
  std::vector<crypto::hash> data;
  data.reserve(hashes.size() + HASH_OF_HASHES_STEP - 1); // may be a bit too much

  // we expect height to be either equal or a bit below db height
  bool disconnected = (height > m_db->height());
  size_t pop;
  if (disconnected && height % HASH_OF_HASHES_STEP)
  {
    ++first_index;
    pop = HASH_OF_HASHES_STEP - height % HASH_OF_HASHES_STEP;
  }
  else
  {
    // we might need some already in the chain for the first part of the first hash
    for (uint64_t h = first_index * HASH_OF_HASHES_STEP; h < height; ++h)
    {
      data.push_back(m_db->get_block_hash_from_height(h));
    }
    pop = 0;
  }

  // push the data to check
  for (const auto &h: hashes)
  {
    if (pop)
      --pop;
    else
      data.push_back(h);
  }

  // hash and check
  uint64_t usable = first_index * HASH_OF_HASHES_STEP - height; // may start negative, but unsigned under/overflow is not UB
  for (size_t n = first_index; n <= last_index; ++n)
  {
    if (n < m_blocks_hash_of_hashes.size())
    {
      // if the last index isn't fully filled, we can't tell if valid
      if (data.size() < (n - first_index) * HASH_OF_HASHES_STEP + HASH_OF_HASHES_STEP)
        break;

      crypto::hash hash;
      cn_fast_hash(data.data() + (n - first_index) * HASH_OF_HASHES_STEP, HASH_OF_HASHES_STEP * sizeof(crypto::hash), hash);
      bool valid = hash == m_blocks_hash_of_hashes[n];

      // add to the known hashes array
      if (!valid)
      {

        MWARNING(hash);
        MWARNING("invalid hash for blocks " << n * HASH_OF_HASHES_STEP << " - " << (n * HASH_OF_HASHES_STEP + HASH_OF_HASHES_STEP - 1));
        break;
      }

      size_t end = n * HASH_OF_HASHES_STEP + HASH_OF_HASHES_STEP;
      for (size_t i = n * HASH_OF_HASHES_STEP; i < end; ++i)
      {
        CHECK_AND_ASSERT_MES(m_blocks_hash_check[i] == crypto::null_hash || m_blocks_hash_check[i] == data[i - first_index * HASH_OF_HASHES_STEP],
            0, "Consistency failure in m_blocks_hash_check construction");
        m_blocks_hash_check[i] = data[i - first_index * HASH_OF_HASHES_STEP];
      }
      usable += HASH_OF_HASHES_STEP;
    }
    else
    {
      // if after the end of the precomputed blocks, accept anything
      usable += HASH_OF_HASHES_STEP;
      if (usable > hashes.size())
        usable = hashes.size();
    }
  }
  MDEBUG("usable: " << usable << " / " << hashes.size());
  CHECK_AND_ASSERT_MES(usable < std::numeric_limits<uint64_t>::max() / 2, 0, "usable is negative");
  return usable;
}

//------------------------------------------------------------------
// ND: Speedups:
// 1. Thread long_hash computations if possible (m_max_prepare_blocks_threads = nthreads, default = 4)
// 2. Group all amounts (from txs) and related absolute offsets and form a table of tx_prefix_hash
//    vs [k_image, output_keys] (m_scan_table). This is faster because it takes advantage of bulk queries
//    and is threaded if possible. The table (m_scan_table) will be used later when querying output
//    keys.
bool Blockchain::prepare_handle_incoming_blocks(const std::list<block_complete_entry> &blocks_entry)
{
  MTRACE("Blockchain::" << __func__);
  TIME_MEASURE_START(prepare);
  bool stop_batch;
  uint64_t bytes = 0;

  // Order of locking must be:
  //  m_incoming_tx_lock (optional)
  //  m_tx_pool lock
  //  blockchain lock
  //
  //  Something which takes the blockchain lock may never take the txpool lock
  //  if it has not provably taken the txpool lock earlier
  //
  //  The txpool lock is now taken in prepare_handle_incoming_blocks
  //  and released in cleanup_handle_incoming_blocks. This avoids issues
  //  when something uses the pool, which now uses the blockchain and
  //  needs a batch, since a batch could otherwise be active while the
  //  txpool and blockchain locks were not held

  m_tx_pool.lock();
  CRITICAL_REGION_LOCAL1(m_blockchain_lock);

  if(blocks_entry.size() == 0)
    return false;

  for (const auto &entry : blocks_entry)
  {
    bytes += entry.block.size();
    for (const auto &tx_blob : entry.txs)
    {
      bytes += tx_blob.size();
    }
  }
  while (!(stop_batch = m_db->batch_start(blocks_entry.size(), bytes))) {
    m_blockchain_lock.unlock();
    m_tx_pool.unlock();
    epee::misc_utils::sleep_no_w(1000);
    m_tx_pool.lock();
    m_blockchain_lock.lock();
  }

  if ((m_db->height() + blocks_entry.size()) < m_blocks_hash_check.size())
    return true;

  bool blocks_exist = false;
  tools::threadpool& tpool = tools::threadpool::getInstance();
  uint64_t threads = tpool.get_max_concurrency();

  if (blocks_entry.size() > 1 && threads > 1 && m_max_prepare_blocks_threads > 1)
  {
    // limit threads, default limit = 4
    if(threads > m_max_prepare_blocks_threads)
      threads = m_max_prepare_blocks_threads;

    uint64_t height = m_db->height() + 1;
    int batches = blocks_entry.size() / threads;
    int extra = blocks_entry.size() % threads;
    MDEBUG("block_batches: " << batches);
    std::vector<std::unordered_map<crypto::hash, crypto::hash>> maps(threads);
    std::vector < std::vector < block >> blocks(threads);
    auto it = blocks_entry.begin();

    for (uint64_t i = 0; i < threads; i++)
    {
      for (int j = 0; j < batches; j++)
      {
        block block;

        if (!parse_and_validate_block_from_blob(it->block, block))
        {
          std::advance(it, 1);
          continue;
        }

        // check first block and skip all blocks if its not chained properly
        if (i == 0 && j == 0)
        {
          crypto::hash tophash = m_db->top_block_hash();
          if (block.prev_id != tophash)
          {
            MDEBUG("Skipping prepare blocks. New blocks don't belong to chain. Prev id: " << block.prev_id << " top hash: " << tophash);
             return true;
          }
        }
        if (have_block(get_block_hash(block)))
        {
          blocks_exist = true;
          break;
        }

        blocks[i].push_back(block);
        std::advance(it, 1);
      }
    }

    for (int i = 0; i < extra && !blocks_exist; i++)
    {
      block block;

      if (!parse_and_validate_block_from_blob(it->block, block))
      {
        std::advance(it, 1);
        continue;
      }

      if (have_block(get_block_hash(block)))
      {
        blocks_exist = true;
        break;
      }

      blocks[i].push_back(block);
      std::advance(it, 1);
    }

    if (!blocks_exist)
    {
      m_blocks_longhash_table.clear();
      uint64_t thread_height = height;
      tools::threadpool::waiter waiter;
      for (uint64_t i = 0; i < threads; i++)
      {
        tpool.submit(&waiter, boost::bind(&Blockchain::block_longhash_worker, this, thread_height, std::cref(blocks[i]), std::ref(maps[i])));
        thread_height += blocks[i].size();
      }

      waiter.wait();

      if (m_cancel)
         return false;

      for (const auto & map : maps)
      {
        m_blocks_longhash_table.insert(map.begin(), map.end());
      }
    }
  }

  if (m_cancel)
    return false;

  if (blocks_exist)
  {
    MDEBUG("Skipping prepare blocks. Blocks exist.");
    return true;
  }

  m_fake_scan_time = 0;
  m_fake_pow_calc_time = 0;

  m_scan_table.clear();
  m_check_txin_table.clear();

  TIME_MEASURE_FINISH(prepare);
  m_fake_pow_calc_time = prepare / blocks_entry.size();

  if (blocks_entry.size() > 1 && threads > 1 && m_show_time_stats)
    MDEBUG("Prepare blocks took: " << prepare << " ms");

  TIME_MEASURE_START(scantable);

  // [input] stores all unique amounts found
  std::vector < uint64_t > amounts;
  // [input] stores all absolute_offsets for each amount
  std::map<uint64_t, std::vector<uint64_t>> offset_map;
  // [output] stores all output_data_t for each absolute_offset
  std::map<uint64_t, std::vector<output_data_t>> tx_map;

#define SCAN_TABLE_QUIT(m) \
        do { \
            MERROR_VER(m) ;\
            m_scan_table.clear(); \
            return false; \
        } while(0); \

  // generate sorted tables for all amounts and absolute offsets
  for (const auto &entry : blocks_entry)
  {
    if (m_cancel)
      return false;

    for (const auto &tx_blob : entry.txs)
    {
      crypto::hash tx_hash = null_hash;
      crypto::hash tx_prefix_hash = null_hash;
      transaction tx;

      if (!parse_and_validate_tx_from_blob(tx_blob, tx, tx_hash, tx_prefix_hash))
        SCAN_TABLE_QUIT("Could not parse tx from incoming blocks.");

      auto its = m_scan_table.find(tx_prefix_hash);
      if (its != m_scan_table.end())
        SCAN_TABLE_QUIT("Duplicate tx found from incoming blocks.");

      m_scan_table.emplace(tx_prefix_hash, std::unordered_map<crypto::key_image, std::vector<output_data_t>>());
      its = m_scan_table.find(tx_prefix_hash);
      assert(its != m_scan_table.end());

      // get all amounts from tx.vin(s)
      for (const auto &txin : tx.vin)
      {
        const txin_to_key &in_to_key = boost::get < txin_to_key > (txin);

        // check for duplicate
        auto it = its->second.find(in_to_key.k_image);
        if (it != its->second.end())
          SCAN_TABLE_QUIT("Duplicate key_image found from incoming blocks.");

        amounts.push_back(in_to_key.amount);
      }

      // sort and remove duplicate amounts from amounts list
      std::sort(amounts.begin(), amounts.end());
      auto last = std::unique(amounts.begin(), amounts.end());
      amounts.erase(last, amounts.end());

      // add amount to the offset_map and tx_map
      for (const uint64_t &amount : amounts)
      {
        if (offset_map.find(amount) == offset_map.end())
          offset_map.emplace(amount, std::vector<uint64_t>());

        if (tx_map.find(amount) == tx_map.end())
          tx_map.emplace(amount, std::vector<output_data_t>());
      }

      // add new absolute_offsets to offset_map
      for (const auto &txin : tx.vin)
      {
        const txin_to_key &in_to_key = boost::get < txin_to_key > (txin);
        // no need to check for duplicate here.
        auto absolute_offsets = relative_output_offsets_to_absolute(in_to_key.key_offsets);
        for (const auto & offset : absolute_offsets)
          offset_map[in_to_key.amount].push_back(offset);

      }
    }
  }

  // sort and remove duplicate absolute_offsets in offset_map
  for (auto &offsets : offset_map)
  {
    std::sort(offsets.second.begin(), offsets.second.end());
    auto last = std::unique(offsets.second.begin(), offsets.second.end());
    offsets.second.erase(last, offsets.second.end());
  }

  // [output] stores all transactions for each tx_out_index::hash found
  std::vector<std::unordered_map<crypto::hash, cryptonote::transaction>> transactions(amounts.size());

  threads = tpool.get_max_concurrency();
  if (!m_db->can_thread_bulk_indices())
    threads = 1;

  if (threads > 1)
  {
    tools::threadpool::waiter waiter;

    for (size_t i = 0; i < amounts.size(); i++)
    {
      uint64_t amount = amounts[i];
      tpool.submit(&waiter, boost::bind(&Blockchain::output_scan_worker, this, amount, std::cref(offset_map[amount]), std::ref(tx_map[amount]), std::ref(transactions[i])));
    }
    waiter.wait();
  }
  else
  {
    for (size_t i = 0; i < amounts.size(); i++)
    {
      uint64_t amount = amounts[i];
      output_scan_worker(amount, offset_map[amount], tx_map[amount], transactions[i]);
    }
  }

  int total_txs = 0;

  // now generate a table for each tx_prefix and k_image hashes
  for (const auto &entry : blocks_entry)
  {
    if (m_cancel)
      return false;

    for (const auto &tx_blob : entry.txs)
    {
      crypto::hash tx_hash = null_hash;
      crypto::hash tx_prefix_hash = null_hash;
      transaction tx;

      if (!parse_and_validate_tx_from_blob(tx_blob, tx, tx_hash, tx_prefix_hash))
        SCAN_TABLE_QUIT("Could not parse tx from incoming blocks.");

      ++total_txs;
      auto its = m_scan_table.find(tx_prefix_hash);
      if (its == m_scan_table.end())
        SCAN_TABLE_QUIT("Tx not found on scan table from incoming blocks.");

      for (const auto &txin : tx.vin)
      {
        const txin_to_key &in_to_key = boost::get < txin_to_key > (txin);
        auto needed_offsets = relative_output_offsets_to_absolute(in_to_key.key_offsets);

        std::vector<output_data_t> outputs;
        for (const uint64_t & offset_needed : needed_offsets)
        {
          size_t pos = 0;
          bool found = false;

          for (const uint64_t &offset_found : offset_map[in_to_key.amount])
          {
            if (offset_needed == offset_found)
            {
              found = true;
              break;
            }

            ++pos;
          }

          if (found && pos < tx_map[in_to_key.amount].size())
            outputs.push_back(tx_map[in_to_key.amount].at(pos));
          else
            break;
        }

        its->second.emplace(in_to_key.k_image, outputs);
      }
    }
  }

  TIME_MEASURE_FINISH(scantable);
  if (total_txs > 0)
  {
    m_fake_scan_time = scantable / total_txs;
    if(m_show_time_stats)
      MDEBUG("Prepare scantable took: " << scantable << " ms");
  }

  return true;
}

void Blockchain::add_txpool_tx(transaction &tx, const txpool_tx_meta_t &meta)
{
  m_db->add_txpool_tx(tx, meta);
}

void Blockchain::update_txpool_tx(const crypto::hash &txid, const txpool_tx_meta_t &meta)
{
  m_db->update_txpool_tx(txid, meta);
}

void Blockchain::remove_txpool_tx(const crypto::hash &txid)
{
  m_db->remove_txpool_tx(txid);
}

uint64_t Blockchain::get_txpool_tx_count(bool include_unrelayed_txes) const
{
  return m_db->get_txpool_tx_count(include_unrelayed_txes);
}

bool Blockchain::get_txpool_tx_meta(const crypto::hash& txid, txpool_tx_meta_t &meta) const
{
  return m_db->get_txpool_tx_meta(txid, meta);
}

bool Blockchain::get_txpool_tx_blob(const crypto::hash& txid, cryptonote::blobdata &bd) const
{
  return m_db->get_txpool_tx_blob(txid, bd);
}

cryptonote::blobdata Blockchain::get_txpool_tx_blob(const crypto::hash& txid) const
{
  return m_db->get_txpool_tx_blob(txid);
}

bool Blockchain::for_all_txpool_txes(std::function<bool(const crypto::hash&, const txpool_tx_meta_t&, const cryptonote::blobdata*)> f, bool include_blob, bool include_unrelayed_txes) const
{
  return m_db->for_all_txpool_txes(f, include_blob, include_unrelayed_txes);
}

void Blockchain::set_user_options(uint64_t maxthreads, uint64_t blocks_per_sync, blockchain_db_sync_mode sync_mode, bool fast_sync)
{
  if (sync_mode == db_defaultsync)
  {
    m_db_default_sync = true;
    sync_mode = db_async;
  }
  m_db_sync_mode = sync_mode;
  m_fast_sync = fast_sync;
  m_db_blocks_per_sync = blocks_per_sync;
  m_max_prepare_blocks_threads = maxthreads;
}

void Blockchain::safesyncmode(const bool onoff)
{
  /* all of this is no-op'd if the user set a specific
   * --db-sync-mode at startup.
   */
  if (m_db_default_sync)
  {
    m_db->safesyncmode(onoff);
    m_db_sync_mode = onoff ? db_nosync : db_async;
  }
}

HardFork::State Blockchain::get_hard_fork_state() const
{
  return m_hardfork->get_state();
}

bool Blockchain::get_hard_fork_voting_info(uint8_t version, uint32_t &window, uint32_t &votes, uint32_t &threshold, uint64_t &earliest_height, uint8_t &voting) const
{
  return m_hardfork->get_voting_info(version, window, votes, threshold, earliest_height, voting);
}

uint64_t Blockchain::get_difficulty_target() const
{
  return get_current_hard_fork_version() < 2 ? DIFFICULTY_TARGET_V1 : DIFFICULTY_TARGET_V2;
}

std::map<uint64_t, std::tuple<uint64_t, uint64_t, uint64_t>> Blockchain:: get_output_histogram(const std::vector<uint64_t> &amounts, bool unlocked, uint64_t recent_cutoff, uint64_t min_count) const
{
  return m_db->get_output_histogram(amounts, unlocked, recent_cutoff, min_count);
}

std::list<std::pair<Blockchain::block_extended_info,uint64_t>> Blockchain::get_alternative_chains() const
{
  std::list<std::pair<Blockchain::block_extended_info,uint64_t>> chains;

  for (const auto &i: m_alternative_chains)
  {
    const crypto::hash &top = i.first;
    bool found = false;
    for (const auto &j: m_alternative_chains)
    {
      if (j.second.bl.prev_id == top)
      {
        found = true;
        break;
      }
    }
    if (!found)
    {
      uint64_t length = 1;
      auto h = i.second.bl.prev_id;
      blocks_ext_by_hash::const_iterator prev;
      while ((prev = m_alternative_chains.find(h)) != m_alternative_chains.end())
      {
        h = prev->second.bl.prev_id;
        ++length;
      }
      chains.push_back(std::make_pair(i.second, length));
    }
  }
  return chains;
}

void Blockchain::cancel()
{
  m_cancel = true;
}

#if defined(PER_BLOCK_CHECKPOINT)
static const char expected_block_hashes_hash[] = "67fb2db1b7559696c03e9afc12c1c688adaf0c3c6c35a1a49ef9a53bfdacd065";
void Blockchain::load_compiled_in_block_hashes()
{
  const bool testnet = m_nettype == TESTNET;
  const bool stagenet = m_nettype == STAGENET;
  if (m_fast_sync && get_blocks_dat_start(testnet, stagenet) != nullptr && get_blocks_dat_size(testnet, stagenet) > 0)
  {
    MINFO("Loading precomputed blocks (" << get_blocks_dat_size(testnet, stagenet) << " bytes)");

    if (m_nettype == MAINNET)
    {
      // first check hash
      crypto::hash hash;
      if (!tools::sha256sum(get_blocks_dat_start(testnet, stagenet), get_blocks_dat_size(testnet, stagenet), hash))
      {
        MERROR("Failed to hash precomputed blocks data");
        return;
      }
      MINFO("precomputed blocks hash: " << hash << ", expected " << expected_block_hashes_hash);
      cryptonote::blobdata expected_hash_data;
      if (!epee::string_tools::parse_hexstr_to_binbuff(std::string(expected_block_hashes_hash), expected_hash_data) || expected_hash_data.size() != sizeof(crypto::hash))
      {
        MERROR("Failed to parse expected block hashes hash");
        return;
      }
      const crypto::hash expected_hash = *reinterpret_cast<const crypto::hash*>(expected_hash_data.data());
      if (hash != expected_hash)
      {
        MERROR("Block hash data does not match expected hash");
        return;
      }
    }

    if (get_blocks_dat_size(testnet, stagenet) > 4)
    {
      const unsigned char *p = get_blocks_dat_start(testnet, stagenet);
      const uint32_t nblocks = *p | ((*(p+1))<<8) | ((*(p+2))<<16) | ((*(p+3))<<24);
      if (nblocks > (std::numeric_limits<uint32_t>::max() - 4) / sizeof(hash))
      {
        MERROR("Block hash data is too large");
        return;
      }
      const size_t size_needed = 4 + nblocks * sizeof(crypto::hash);
      if(nblocks > 0 && nblocks > (m_db->height() + HASH_OF_HASHES_STEP - 1) / HASH_OF_HASHES_STEP && get_blocks_dat_size(testnet, stagenet) >= size_needed)
      {
        p += sizeof(uint32_t);
        m_blocks_hash_of_hashes.reserve(nblocks);
        for (uint32_t i = 0; i < nblocks; i++)
        {
          crypto::hash hash;
          memcpy(hash.data, p, sizeof(hash.data));
          p += sizeof(hash.data);
          m_blocks_hash_of_hashes.push_back(hash);
        }
        m_blocks_hash_check.resize(m_blocks_hash_of_hashes.size() * HASH_OF_HASHES_STEP, crypto::null_hash);
        MINFO(nblocks << " block hashes loaded");

        // FIXME: clear tx_pool because the process might have been
        // terminated and caused it to store txs kept by blocks.
        // The core will not call check_tx_inputs(..) for these
        // transactions in this case. Consequently, the sanity check
        // for tx hashes will fail in handle_block_to_main_chain(..)
        CRITICAL_REGION_LOCAL(m_tx_pool);

        std::list<transaction> txs;
        m_tx_pool.get_transactions(txs);

        size_t blob_size;
        uint64_t fee;
        bool relayed, do_not_relay, double_spend_seen;
        transaction pool_tx;
        for(const transaction &tx : txs)
        {
          crypto::hash tx_hash = get_transaction_hash(tx);
          m_tx_pool.take_tx(tx_hash, pool_tx, blob_size, fee, relayed, do_not_relay, double_spend_seen);
        }
      }
    }
  }
}
#endif

bool Blockchain::is_within_compiled_block_hash_area(uint64_t height) const
{
#if defined(PER_BLOCK_CHECKPOINT)
  return height < m_blocks_hash_of_hashes.size() * HASH_OF_HASHES_STEP;
#else
  return false;
#endif
}

void Blockchain::lock()
{
  m_blockchain_lock.lock();
}

void Blockchain::unlock()
{
  m_blockchain_lock.unlock();
}

bool Blockchain::for_all_key_images(std::function<bool(const crypto::key_image&)> f) const
{
  return m_db->for_all_key_images(f);
}

bool Blockchain::for_blocks_range(const uint64_t& h1, const uint64_t& h2, std::function<bool(uint64_t, const crypto::hash&, const block&)> f) const
{
  return m_db->for_blocks_range(h1, h2, f);
}

bool Blockchain::for_all_transactions(std::function<bool(const crypto::hash&, const cryptonote::transaction&)> f, bool pruned) const
{
  return m_db->for_all_transactions(f, pruned);
}

bool Blockchain::for_all_outputs(std::function<bool(uint64_t amount, const crypto::hash &tx_hash, uint64_t height, size_t tx_idx)> f) const
{
  return m_db->for_all_outputs(f);;
}

bool Blockchain::for_all_outputs(uint64_t amount, std::function<bool(uint64_t height)> f) const
{
  return m_db->for_all_outputs(amount, f);;
}

namespace cryptonote {
template bool Blockchain::get_transactions(const std::vector<crypto::hash>&, std::list<transaction>&, std::list<crypto::hash>&) const;
}
