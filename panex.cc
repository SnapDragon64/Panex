#include <algorithm>
#include <cassert>
#include <iostream>
#include <queue>
#include <set>
#include <string>
#include <vector>
using namespace std;

#define INFINITY 1000000000

/******************************************************************************
 *                              INTRODUCTION                                  *
 ******************************************************************************/

// This is a program which computes the number of moves required to solve a
// Panex puzzle.  As the solution space is very large, a form of dynamic
// programming is used in order to store only the information from the upper
// levels of the towers that is useful for moving around lower blocks.
//
// First, note that it is never useful to place a block at the very top of the
// middle channel.  It will have to move from there in the next move anyway.
//
// Now, consider the top N >= 2 levels of the Panex tower.  Pretend (for now)
// that the silver/gold blocks are indistinguishable.  The key observation is
// that there are exactly two states which allow you to move a lower-level block
// out of or into the left/right channels.  One has the N-block to the 1-block
// stacked normally in the middle and the right/left channels; the other is the
// same but with the middle 1-block moved on top of the right/left tower.
// States that look like this are chokepoints for the search space.  We will
// call states "N-useful" if they are of this form.
//
// For convenience's sake, we will also call the state with the middle channel
// empty and properly stacked towers in the left and right channels "N-useful"
// as well, even though it's not actually a chokepoint.  It's the starting and
// ending state of the puzzle, so it makes the search simpler to include it.
// This makes for a total of 5 canonical "N-useful" states.
//
// Now we divide up the entire solution of the puzzle into transitions between
// "N-useful" states on the top N levels.  And here's why: between "N-useful"
// states, only 4 blocks below the Nth level can possibly be moved!  Since a
// move from the left or right must start or end on an "N-useful" state, we can
// only reach one lower block on either end.  And even using the easier middle
// channel, there simply isn't room in the puzzle to store more than two blocks
// in the upper N levels without dropping at least one to the left or the
// right.
//
// Also, there is nothing to be gained by moving blocks out of the lower levels
// but then back into exactly the same state.
//
// Thus, there are a finite (and small) number of possible sequences of moves
// that can be made on the lower blocks between "N-useful" states.  These sets
// might still be a little complicated: for instance, you might pull a block
// out of the right, then take one out of the middle, then put the first block
// in the middle, then the second block down the left channel.  But because
// they're finite (irrespective of N), we can precompute all the important
// work with these sequences, leaving the main search fast and memory-efficient.
// I'll call these sequences "permutations" from now on.
// 
// To sum up, all we need at the Nth level of the tower is the cost of moving
// from "N-useful" state X to "N-useful" state Y whilst doing permutation Z on
// the lower blocks, for all X, Y, and Z.  Once we've precomputed that, we
// have all the information we need out of the top N levels and can move on to
// N+1.  For solving N+1 (and beyond) we just pretend the top N levels are a
// unit that transitions between one of the 5 canonical "N-useful" states,
// with certain specific costs for sequences of operations on lower levels.
//
// Now, up above I pretended the silver/gold blocks were indistinguishable.  Of
// course, it's important that they aren't.  So alongside permutation info
// we will also keep a "swap" bit vector that tracks whether the gold is to the
// left of the silver for levels 1 to N.  This expands the graph by 2^N states,
// but since silver and gold blocks behave the same (a very exploitable
// symmetry), we still only need to compute and store the transitions from 5
// canonical "N-useful" states (instead of all 5*2^N possible "N-useful"
// states).  Searching from a non-canonical "N-useful" state simply requires
// XORing the current "swap" bit vector with the resulting states.
//
// The implementation is a bit tricky, since these "N-useful" states and
// permutations are very abstract.  Going from the Nth level to the N+1th level
// requires applying "N-useful" permutation moves to the N+1-blocks as well as
// "virtual" blocks that lie below the N+1th level.  Even so, sometimes a
// permutation simply won't work (because there isn't room to drop a block
// into the N+1st level or below).  Similarly, a block might temporarily fall
// to the N+1st level (so out of consideration of the precomputed N-level
// transitions) but not be required to fall to the N+2nd level (which might
// not be possible); we need to allow for this to happen.
//
// Because of the complexity, and since correctness is important, I've tried to
// make the part of the code dealing with permutations as clear and general
// as possible, letting the topology of the puzzle itself determine the
// finiteness of the permutations rather than any hardcoded limits.  I've also
// added redundant sanity checks.  The code doesn't need to be efficient, since
// it's all part of a precomputation.
//
// The resources required by the program are approximately O(2^N) memory and
// O(4^N) time.  And there turn out to be 1172 nodes in the precomputed
// permutation graph.  I suspect that, once this (very complex) graph is
// computed, the expansion of this graph using swap vectors is actually fairly
// regular.  There might be a computer-assisted proof of optimality for the
// known strategy for all N in here somewhere. :)


/******************************************************************************
 *                             PARTIALSTATE CLASS                             *
 ******************************************************************************/

class PartialState {
// A PartialState represents all the required information for precomputing the
// N+1th-level graph, based on the already-computed Nth-level graph.  The top
// N levels are always in one of the 5 "N-useful" states.  Also, the current
// sequence of lower-level (N+2th level and below) moves is explicitly stored.
//
// In order to keep the number of PartialStates finite and independent of N,
// the swap bit vector of the first N blocks is stored elsewhere; thus, in a
// PartialState these blocks are considered indistinguishable.
//
// The state of the top N+1 levels is stored like this, as an example.  Note
// that the Panex puzzle is on its side:
//    ...Z....
//    ..-0..12
//    AA-z...3
// The '.'s represent blank parts of the puzzle.
// The 'A's represent the indistinguishable 1-blocks.
// The '-'s represent (in compressed form) the 2- through N-blocks, always
// stacked in a proper tower.  The 'A's and '-'s are always in one of the 5
// canonical "N-useful" positions.
// The 'Z' and 'z' represent the *distinguished* N+1-blocks.  We never see them
// leave their home row (it's all taken care of between "N-useful" states), so
// they are in 6 possible positions.
// The '0' through '3' are virtual blocks lying below the N+1th level (the
// only ones accessible between "N+1-useful" states).  In non-canonical states
// (with non-trivial permutations) they'll get dropped into different channels,
// and sometimes they're temporarily stored up on the N+1th level, too.
// They're somewhat redundant information alongside the permutation, but are
// useful for debug output, simplifying the code, and sanity checking.
//
// A permutation is also stored, giving the sequence of moves since the last
// "N+1-useful" state that pick up or put down virtual blocks '0'-'3' into one
// of the three channels.  Note that we can't just make do with the end state
// stored above; temporarily dropping a virtual block down a channel and then
// picking it up again might be an important move!  We need to store the
// complete sequence.

 public:
  string channel[3];

  struct Move {
    char block;  // '0'-'3', the block being moved.
    bool drop;  // Whether the block is being lifted or dropped.
    int channel;  // 0-2, the channel the block's being raised/dropped into.

    // Comparison operator so we can put this in a set.
    bool operator<(const Move& move) const {
      if (block != move.block) return block < move.block;
      if (drop != move.drop) return drop < move.drop;
      return channel < move.channel;
    }
    bool operator==(const Move& move) const {
      return block == move.block &&
             drop == move.drop &&
             channel == move.channel;
    }
  };
  // The full sequence of moves on blocks below the N+1th row since the last
  // "N+1-useful" state.  It should always have either the same number of lifts
  // and drops, or one more lift than drop (if a virtual block is being
  // temporarily stored on the N+1th row).
  // 
  // We have very few restrictions on the sequence; the fact that there are
  // manageably few possibilities arises naturally out of the puzzle.  The only
  // restrictions are:
  // - Following the sequence, we should never run into a repeat configuration
  //   with the virtual blocks below the N+1th row.  Obviously if we do, we've
  //   done more work than necessary, since we could have just left them as-is
  //   and made all the same moves with the top N+1 blocks.  So we treat such
  //   sequences as invalid.
  // - We should also never pull block 'x' out of a channel and then put it
  //   back into the same channel, even if we're holding another block
  //   temporarily up above.  Obviously this is useless since we could just
  //   leave it there.  (Note that the converse - temporarily dropping 'x'
  //   into a channel - might NOT be useless.)
  // - There is one "deadly pattern" we delete on sight: where virtual block
  //   'x' is temporarily on row N+1, and we lift block 'y' up and put block
  //   'x' down the middle channel, then lift block 'x' up and put block 'y'
  //   down the middle channel.  This is not naturally prevented by the above
  //   restrictions, and could be repeated indefinitely.  However, from the
  //   perspective of the lower blocks, it is a null operation; neither drop
  //   can fail since they're into channels that a block was just lifted out of.
  //   And the lifts can't fail since even if 'y' doesn't exist - the channel's
  //   empty - we could just pretend it does (and then there would be some
  //   other permutation that does the same thing with fewer moves).  So with
  //   respect to the DP induction it is safe to collapse this subsequence into
  //   nothing.
  vector<Move> perm;

  // Acts on the given "channel" state with the given Move from the same
  // N+1th-level PartialState, which should NOT be storing a virtual block at
  // row N+1.  (In other words, the top N+1 rows will remain unchanged.)
  // "tmp" is temporary storage for lifted blocks before they're dropped.
  // Throws an assertion if the given move is invalid.
  static void ApplyMove(const Move& move,
                        string channel[3],
                        string* tmp) {
    assert(move.block >= '0' && move.block <= '3');
    assert(move.channel >= 0 && move.channel <= 2);
    if (move.drop) {
      int i = tmp->find(move.block);
      assert(i != -1);
      tmp->erase(i, 1);
      for (i = 4; i < 8; i++) {
        if (channel[move.channel][i] != '.') break;
      }
      --i;
      // 2 rows of '.' should be enough for any reachable configuration.
      assert(i >= 4);
      channel[move.channel][i] = move.block;
    } else {
      // The puzzle needs room for these lifts to happen.
      if (move.channel == 1) assert(tmp->size() < 2);
      if (move.channel != 1) assert(tmp->size() < 1);
      int i;
      for (i = 4; i < 8; i++) {
        if (channel[move.channel][i] != '.') break;
      }
      assert(i < 8 && channel[move.channel][i] == move.block);
      channel[move.channel][i] = '.';
      *tmp += move.block;
    }
  }

  // Checks whether the given sequence of lower-block moves ever "loops".  As
  // specified above, this requires all virtual blocks to be below the N+1th
  // row and in the exact same configuration (or the simple case of picking
  // 'x' out of a channel and then dropping it back in).  In this case, we know
  // that we've done more work than necessary.
  static bool ConfigurationRepeats(const vector<Move>& perm) {
    // Check for picking up and dropping the same block into the same channel.
    for (int i = 0; i+1 < perm.size(); i++)
      if (perm[i].channel == perm[i+1].channel &&
          perm[i].block == perm[i+1].block &&
          !perm[i].drop && perm[i+1].drop) {
        return true;
      }

    // Run through the sequence of moves.  It doesn't matter what the top
    // N+1 rows look like; they won't move.
    string channel[3], tmp;
    for (int i = 0; i < 3; i++) channel[i] = CanonicalStates[0][i];
    vector<string> configurations;
    for (int i = 0; ; i++) {
      if (tmp == "") {
        // All virtual blocks are below row N+1; store this configuration.
        configurations.push_back(channel[0] + channel[1] + channel[2]);
      }
      if (i == perm.size()) break;
      ApplyMove(perm[i], channel, &tmp);
    }
    // Make sure configurations has no repeats.
    sort(configurations.begin(), configurations.end());
    return unique(configurations.begin(), configurations.end()) !=
        configurations.end();
  }

  // Checks for the "deadly pattern" mentioned above at index "i" of "perm".
  static inline bool IsDeadlyPattern(const vector<Move>& perm, int i) {
    return i+3 < perm.size() &&
           perm[i].channel == 1 && !perm[i].drop &&
           perm[i+1].channel == 1 && perm[i+1].drop &&
           perm[i+2].channel == 1 && !perm[i+2].drop &&
           perm[i+3].channel == 1 && perm[i+3].drop &&
           perm[i].block == perm[i+3].block &&
           perm[i+1].block == perm[i+2].block &&
           perm[i].block != perm[i+1].block;
  }

  // Deletes any deadly pattern that occurs in "perm".
  static void DeleteDeadlyPattern(vector<Move>* perm) {
    for (int i = 0; i < perm->size(); i++) {
      while (IsDeadlyPattern(*perm, i)) {
        perm->erase(perm->begin()+i, perm->begin()+i+4);
      }
    }
  }

  // The 5 canonical "N+1-useful" states from which all searches start.
  //    0 - Middle channel clear
  //    1 - Left channel clear, 'A's both in row 1
  //    2 - Left channel clear, 'A's stacked on right
  //    3 - Left channel clear, 'A's both in row 1
  //    4 - Left channel clear, 'A's stacked on left
  static const string CanonicalStates[5][3];

  PartialState(int canonical_state = 0) {
    channel[0] = CanonicalStates[canonical_state][0];
    channel[1] = CanonicalStates[canonical_state][1];
    channel[2] = CanonicalStates[canonical_state][2];
  }
  PartialState(const PartialState& state) {
    for (int i = 0; i < 3; i++) channel[i] = state.channel[i];
    perm = state.perm;
  }

  bool operator==(const PartialState& state) const {
    return channel[0] == state.channel[0] &&
           channel[1] == state.channel[1] &&
           channel[2] == state.channel[2] &&
           perm == state.perm;
  }

  // Outputs a 3-line representation of the PartialState.  The moves are
  // written to the side of channel 1.
  void Output(ostream& out) const {
    out << channel[0] << '\n';
    out << channel[1];
    for (int i = 0; i < perm.size(); i++)
      out << "  '" << perm[i].block << "'" << (perm[i].drop ? "->" : "<-")
          << "C" << perm[i].channel;
    out << '\n';
    out << channel[2] << endl;
  }

  // Returns which of the 5 canonical states above shares its first N rows with
  // this PartialState.  (ie, the index of the "N-useful" state this
  // PartialState contains).
  // Fails an assertion if it can't find one.
  int NRowState() const {
    for (int i = 0; i < 5; i++) {
      bool match = true;
      for (int j = 0; j < 3; j++)
      for (int k = 0; k < 3; k++)
        if (CanonicalStates[i][j][k] != channel[j][k]) {
          match = false;
        }
      if (match) return i;
    }
    assert(false);  // Badly-formed PartialState!
  }

  // Runs a sanity check that this PartialState has the expected form.
  void AssertValid() const {
    // Each channel should have be exactly 8 high.
    for (int i = 0; i < 3; i++) assert(channel[i].size() == 8);

    // Check that the top three rows are an "N-useful" state.
    int nrowstate = NRowState();
    assert(nrowstate >= 0 && nrowstate <= 4);

    // 'Z' and 'z' should be in row 4.
    assert(channel[0][3] == 'Z' ||
           channel[1][3] == 'Z' ||
           channel[2][3] == 'Z');
    assert(channel[0][3] == 'z' ||
           channel[1][3] == 'z' ||
           channel[2][3] == 'z');

    // Following the stored permutation should lead to exactly our current
    // state of '0'-'3' blocks.
    // Start with the basic '0'-'3' setup.
    string tmp_channel[3], tmp;
    for (int i = 0; i < 3; i++) tmp_channel[i] = channel[i];
    for (int i = 0; i < 3; i++)
    for (int j = 0; j < 8; j++)
      if (tmp_channel[i][j] >= '0' && tmp_channel[i][j] <= '3') {
        tmp_channel[i][j] = '.';
      }
    tmp_channel[0][7] = '0';
    tmp_channel[1][6] = '1';
    tmp_channel[1][7] = '2';
    tmp_channel[2][7] = '3';
    for (int i = 0; i < perm.size(); i++) {
      ApplyMove(perm[i], tmp_channel, &tmp);
    }
    // We shouldn't be storing more than 1 block temporarily.
    assert(tmp.size() <= 1);
    if (tmp.size() == 1) {
      // Store this block at row N+1.
      for (int i = 0; i < 3; i++)
        if (tmp_channel[i][3] == '.') {
          tmp_channel[i][3] = tmp[0];
        }
    }
    // We should have reached our current state.
    for (int i = 0; i < 3; i++) assert(channel[i] == tmp_channel[i]);

    // perm should satisfy the conditions in its description.
    assert(!ConfigurationRepeats(perm));
    for (int i = 0; i < perm.size(); i++) assert(!IsDeadlyPattern(perm, i));
  }

  // Returns whether this is an "N+1-useful" state.  This requires the 'Z' and
  // 'z' to be underneath the N-row towers.
  bool IsUseful() const {
    return channel[0][2] == '.' && channel[0][3] == '.' ||
           channel[1][2] == '.' && channel[1][3] == '.' ||
           channel[2][2] == '.' && channel[2][3] == '.';
  }

  // Returns whether there is any lower-block permutation at all in this state.
  bool IsPermuted() const {
    return perm.size() > 0;
  }

  // Returns whether 'Z' and 'z' have been swapped in this PartialState, ie,
  // 'z' comes before 'Z'.
  bool IsXSwapped() const {
    return channel[0][3] == 'z' || channel[0][3] == '.' && channel[1][3] == 'z';
  }

  // Returns whether this is one of the 5 canonical "N+1-useful" start states.
  bool IsCanonical() const {
    return IsUseful() && !IsPermuted() && !IsXSwapped();
  }

  // Applies the permutation of the N-level PartialState, "nstate", to this
  // N+1-level PartialState.  This involves applying the sequence of lifts and
  // drops in "nstate" to the blocks (either virtual or 'Z'/'z') in this
  // PartialState, as well as changing the "N-useful" configuration of the top
  // N rows to match "nstate".
  //
  // "fall_through" determines whether we allow a virtual block to remain in
  // the N+1th row on the final move.  (Basically, one choice will often lead
  // to an "N+1-useful" state, the other is used for intermediate states.)
  // Note that for intermediate moves we still put temporaries in the N+1th
  // row, as much as possible; it is only beneficial to do so.  (If a
  // permutation is allowed without using temporary storage it will be
  // allowed using temporary storage.)
  //
  // It is a fatal error if "nstate" is not an "N-useful" state, since this
  // application would make no sense (the N-blocks would end up out of
  // position, so we would no longer have an valid N+1-level PartialState).
  //
  // Also, it is fatal if this PartialState is a non-canonical "N+1-useful"
  // state, ie, with 'Z' and 'z' swapped or a nontrivial permutation.  This is
  // because we always stop our N+1-level search at "N+1-useful" states; if we
  // didn't enforce this, it would be possible to reach virtual blocks other
  // than '0'-'3', which would be bad.
  //
  // Finally, it is fatal if "nstate" is not reachable from the canonical
  // "N-useful" state of the top N rows.  (This would also allow us to reach
  // virtual blocks other than '0'-'3' in the precomputation stage.)
  //
  // There are various ways applying "nstate" can fail:
  // - A block gets dropped on top of a block in the N+1th row ('Z', 'z',
  //   or a virtual block temporarily held from a prior permutation with
  //   "fall_through" == false).
  // - The resultant permutation contains a repeat configuration, thus being
  //   provably not useful.
  // The function returns false and the PartialState is considered corrupted
  // if the operation fails.
  bool ApplyPermutation(const PartialState& nstate, bool fall_through) {
    if (!nstate.IsUseful()) {
      cerr << "ERROR: ApplyPermutation with a non-Useful PartialState:\n";
      Output(cerr);
      cerr << "  perm:\n";
      nstate.Output(cerr);
      assert(false);
    }

    if (IsUseful() && !IsCanonical()) {
      cerr << "ERROR: ApplyPermutation on an N+1-Useful but non-canonical "
           << "PartialState:\n";
      Output(cerr);
      cerr << "  perm:\n";
      nstate.Output(cerr);
      assert(false);
    }
PartialState old = *this;

    // Compute what "nstate"'s virtual '0'-'3' blocks map to in this
    // PartialState.  (Two of these blocks are always 'Z' and 'z'.)  It is
    // possible for these to map to nothing ('.'), but in that case they should
    // never be involved in a Move.
    char virtual_map[4];
    int c, i, j;
    for (i = 3; i < 8 && channel[0][i] == '.'; i++)
      ;
    virtual_map[0] = (i < 8 ? channel[0][i] : '.');
    for (i = 3; i < 8 && channel[1][i] == '.'; i++)
      ;
    virtual_map[1] = (i < 8 ? channel[1][i] : '.');
    for (i++; i < 8 && channel[1][i] == '.'; i++)
      ;
    virtual_map[2] = (i < 8 ? channel[1][i] : '.');
    for (i = 3; i < 8 && channel[2][i] == '.'; i++)
      ;
    virtual_map[3] = (i < 8 ? channel[2][i] : '.');

    // Apply each of "nstate"'s Moves.
    string tmp;  // Temporary storage for lifted blocks.
    for (int i = 0; i < nstate.perm.size(); i++) {
      const Move& nmove = nstate.perm[i];
      char bl = virtual_map[nmove.block - '0'];
      assert(bl != '.');  // Shouldn't happen due to reachability constraint.
      if (nmove.drop) {
        // Make sure we have the correct block to drop.
        j = tmp.find(bl);
        assert(j != -1);
        tmp.erase(j, 1);

        // If we're trying to drop on a piece held in the N+1th row, this
        // permutation fails.
        if (channel[nmove.channel][3] != '.') return false;

        bool use_row_n_plus_one = true;
        if (bl >= '0' && bl <= '3') {
          // Predict whether we need to drop this virtual block through, or we
          // can store it on row N+1.
          use_row_n_plus_one = !fall_through;
          for (j = i+1; j < nstate.perm.size(); j++) {
            if (nstate.perm[j].channel == nmove.channel) {
              if (nstate.perm[j].drop) {
                // We'll drop something else down this channel.  We can't store
                // a temporary here.
                use_row_n_plus_one = false;
              } else {
                // We'll lift out of this channel soon.  Store temporarily.
                use_row_n_plus_one = true;
              }
              break;
            }
          }
        }

        if (use_row_n_plus_one) {
          // Store this block on row N+1.
          channel[nmove.channel][3] = bl;
        } else {
          // Drop this block into the lower rows.
          Move new_move;
          new_move.channel = nmove.channel;
          new_move.drop = true;
          new_move.block = bl;
          perm.push_back(new_move);

          int j;
          for (j = 4; j < 8; j++) {
            if (channel[nmove.channel][j] != '.') break;
          }
          j--;
          assert(j > 3);  // There must be room.
          channel[nmove.channel][j] = bl;
        }
      } else {
        // Make sure we're lifting the correct block.
        for (j = 3; j < 8; j++) {
          if (channel[nmove.channel][j] != '.') break;
        }
        assert(j < 8 && bl == channel[nmove.channel][j]);
        channel[nmove.channel][j] = '.';
        tmp += bl;

        // If this happens below the N+1th row, it needs to be saved as a Move.
        if (j > 3) {
          Move new_move;
          new_move.channel = nmove.channel;
          new_move.drop = false;
          new_move.block = bl;
          perm.push_back(new_move);
        }
      }
    }

    // Check for the "deadly pattern" and eliminate it.
    DeleteDeadlyPattern(&perm);

    // If we've formed a repeat configuration, this permutation is suboptimal
    // and we can disallow it.
    if (ConfigurationRepeats(perm)) return false;

    // The top N rows are now in the "N-useful" configuration from "nstate".
    for (int i = 0; i < 3; i++)
    for (int j = 0; j < 3; j++) {
      channel[i][j] = nstate.channel[i][j];
    }
 
    // Since this is a strange and complicated operation, run a final
    // validation check.
    AssertValid();
    return true;
  }
};

const string PartialState::CanonicalStates[5][3] =
    {{".A-Z...0",
      "......12",
      ".A-z...3"},
     {".......0",
      ".A-Z..12",
      ".A-z...3"},
     {".......0",
      "..-Z..12",
      "AA-z...3"},
     {".A-Z...0",
      ".A-z..12",
      ".......3"},
     {"AA-Z...0",
      "..-z..12",
      ".......3"}};

// The PartialState format is designed to ensure correctness rather than for
// efficiency.  So since there are a small finite number of them, we just
// precompute them all (and all operations on them) and refer to them only by
// index.
vector<PartialState> States;
// 5 booleans indicating which canonical states this permutation can be reached
// from (without passing through an "N+1-useful" state); used only to restrict
// which states we precompute ApplyPermutation for to ones we'll actually
// search.  (If we were to miss any, it'd throw an assertion, so this is quite
// safe.)
vector<vector<bool> > StateReachableFrom;

// All operations are done via the following lookup tables.
vector<bool> StateIsUseful;
vector<bool> StateIsPermuted;
vector<bool> StateIsXSwapped;
vector<bool> StateIsCanonical;
vector<int> StateNRowState;
// -2 indicates an invalid call; -1 indicates ApplyPermutation returned false.
vector<vector<vector<int> > > StateApplyPermutation;


/******************************************************************************
 *                          DYNAMIC PROGRAMMING STORAGE                       *
 ******************************************************************************/

struct FullState {
// A full state reached in the graph computed by the dynamic programming
// algorithm.
  int perm;  // Index of the N-level PartialState.
  int swaps;  // N+1-bit vector giving the swap state of the N+1 highest blocks.
  int cost;  // Cost of reaching this state.

  FullState(int perm = 0, int swaps = 0, int cost = 0)
    : perm(perm), swaps(swaps), cost(cost) {}

  // Comparison operator for storing this in a priority_queue.
  bool operator<(const FullState& state) const {
    return cost > state.cost;
  }
};

// This stores each level of the dynamic programming algorithm as it is
// computed.  LevelPerms[N][start], with N >= 2 and 0 <= start <= 4, is a vector
// containing all the "N-useful" FullState permutations reachable from the
// given canonical "N-useful" start state.
vector<vector<vector<FullState> > > LevelPerms;


/******************************************************************************
 *                        BASE CASE: NORMAL SEARCH ON N=2                     *
 ******************************************************************************/

class Level2State {
// A Level2State looks similar to a PartialState.  It has distinguished 'a'/'A'
// and 'z'/'Z' blocks, and the same virtual blocks '0'-'3'.  It also stores a
// move sequence (for operations involving rows below 2) in the same format.
// But it's actually just manipulated like a Panex puzzle.  It's used for the
// base case search at N=2.

 public:
  string channel[3];
  vector<PartialState::Move> perm;

  // The 5 canonical "2-useful" states from which all searches start.
  static const string CanonicalStates[5][3];

  Level2State(int canonical_state = 0) {
    channel[0] = CanonicalStates[canonical_state][0];
    channel[1] = CanonicalStates[canonical_state][1];
    channel[2] = CanonicalStates[canonical_state][2];
  }
  Level2State(const Level2State& state) {
    for (int i = 0; i < 3; i++) channel[i] = state.channel[i];
    perm = state.perm;
  }

  // Comparison operator so we can put this in a set.
  bool operator<(const Level2State& state) const {
    for (int c = 0; c < 3; c++) {
      if (channel[c] != state.channel[c]) return channel[c] < state.channel[c];
    }
    return perm < state.perm;
  }

  // Outputs a 3-line representation of the Level2State.  The moves are
  // written to the side of channel 1.
  void Output(ostream& out) const {
    out << channel[0] << '\n';
    out << channel[1];
    for (int i = 0; i < perm.size(); i++)
      out << "  '" << perm[i].block << "'" << (perm[i].drop ? "->" : "<-")
          << "C" << perm[i].channel;
    out << '\n';
    out << channel[2] << endl;
  }

  // Returns true if this is a "2-useful" state.
  bool Is2Useful() const {
    assert(channel[1][0] == '.');
    // Check for an empty channel.
    int c;
    for (c = 0; c < 3; c++) {
      if (channel[c][0] == '.' && channel[c][1] == '.' && channel[c][2] == '.')
        break;
    }
    // Middle channel and top row empty.
    if (c == 1) return channel[0][0] == '.' && channel[2][0] == '.';
    // Left channel and another space empty.
    if (c == 0) return channel[1][1] == '.' || channel[2][0] == '.';
    // Right channel and another space empty.
    if (c == 2) return channel[1][1] == '.' || channel[0][0] == '.';
    return false;
  }

  // Returns the Level-2 PartialState corresponding to this.  Is2Useful() must
  // be true; we don't bother with non-"2-Useful" conversions.
  PartialState ToPartialState() const {
    assert(Is2Useful());
    PartialState state;
    for (int c = 0; c < 3; c++) {
      // Copy and add the '-' row (which is of height 0 right now).
      state.channel[c] = channel[c].substr(0, 2) + '.' +
                         channel[c].substr(2);
      if (channel[c][2] != '.') state.channel[c][2] = '-';
      // Convert our 'a' to the PartialState's 'A'.
      for (int i = 0; i < 2; i++) {
        if (state.channel[c][i] == 'a') state.channel[c][i] = 'A';
      }
    }
    state.perm = perm;
    state.AssertValid();  // Better safe than sorry...
    return state;
  }

  // Returns the 2-bit swap vector corresponding to this state.  (ie, bit 0
  // is whether 'a' appears before 'A', and bit 1 is whether 'z' appears
  // before 'Z'.)
  int Swaps() const {
    int ret = 0;
    for (int c = 0; c < 3; c++)
    for (int i = 0; i < 2; i++) {
      if (channel[c][i] == 'A' || channel[c][i] == 'a') {
        if (channel[c][i] == 'a') ret |= 1;
        goto a_found;
      }
    }
a_found:
    for (int c = 0; c < 3; c++)
    for (int i = 0; i < 3; i++) {
      if (channel[c][i] == 'Z' || channel[c][i] == 'z') {
        if (channel[c][i] == 'z') ret |= 2;
        goto z_found;
      }
    }
z_found:
    return ret;
  }

  // Returns true if a move is possible from channel c1 to channel c2.
  bool CanMove(int c1, int c2) const {
    if (c1 == c2) return false;
    if (channel[c2][0] != '.') return false;
    // Don't allow a useless move into the top of the middle channel.
    if (c2 == 1 && channel[c2][1] != '.') return false;
    return true;
  }

  // Makes a move from c1 to c2.  CanMove(c1, c2) must be true.
  // "fall_past_2" is the equivalent of ApplyPermutation's "fall_through".
  // If true, we allow the piece to fall beyond row 2; otherwise we stop it
  // there.  Trying both is necessary because there may be an as-yet-unknown
  // piece in row 3 which holds this virtual piece up.
  // Any moves involving rows below 2 are added to "perm".
  void MakeMove(int c1, int c2, bool fall_past_2) {
    assert(CanMove(c1, c2));

    // Find the block to lift.
    char block = 0;
    for (int i = 0; i < 7; i++) {
      if (channel[c1][i] != '.') {
        block = channel[c1][i];
        channel[c1][i] = '.';
        if (i > 2) {
          PartialState::Move new_move;
          new_move.channel = c1;
          new_move.drop = false;
          new_move.block = block;
          perm.push_back(new_move);
        }
        break;
      }
    }
    assert(block);  // Oops!  We somehow went beyond the virtual blocks.

    // As are restricted to rows 0-1 and Zs to rows 0-2.
    int max_depth = fall_past_2 ? 7 : 2, depth;
    if (block == 'a' || block == 'A') max_depth = 1;
    if (block == 'z' || block == 'Z') max_depth = 2;

    // Drop the block as deep as possible.
    for (depth = 0; depth <= max_depth; depth++) {
      if (channel[c2][depth] != '.') break;
    }
    depth--;
    channel[c2][depth] = block;
    if (depth > 2) {
      PartialState::Move new_move;
      new_move.channel = c2;
      new_move.drop = true;
      new_move.block = block;
      perm.push_back(new_move);
    }
  }
};

const string Level2State::CanonicalStates[5][3] =
  {{".AZ...0",
    ".....12",
    ".az...3"},
   {"......0",
    ".AZ..12",
    ".az...3"},
   {"......0",
    "..Z..12",
    "Aaz...3"},
   {".AZ...0",
    ".az..12",
    "......3"},
   {"AaZ...0",
    "..z..12",
    "......3"}};

// Begins the dynamic programming with the base case at N=2.  (We cannot
// start at N=1, as the basic virtual block restriction breaks down: you can
// put both blocks to one side and then manipulate virtual blocks in the other
// two channels as deep as you want.)  Done with a basic BFS.  Any
// "2-useful" PartialStates found are added to the States vector.
void PrecomputeLevel2Perms() {
  LevelPerms.clear();
  LevelPerms.resize(3);
  LevelPerms[2].resize(5);

  for (int start = 0; start < 5; start++) {
    cout << "Precomputing Level-2 States from canonical state " << start
         << "..." << endl;
    set<Level2State> seen;
    vector<Level2State> cur_states;
    int distance = 0;
    cur_states.push_back(Level2State(start));
    seen.insert(Level2State(start));

    while (!cur_states.empty()) {
      vector<Level2State> next_states;
      while (!cur_states.empty()) {
        Level2State state = cur_states.back();
        cur_states.pop_back();

        if (state.Is2Useful()) {
          // It's "2-useful", so we should remember this state in LevelPerms.
          PartialState partial = state.ToPartialState();
          int index;
          // Find this PartialState in the known States, or else add it.
          for (index = 0; index < States.size(); index++) {
            if (States[index] == partial) break;
          }
          if (index == States.size()) {
            States.push_back(partial);
            StateReachableFrom.push_back(vector<bool>(5, false));
          }
          StateReachableFrom[index][start] = true;
          LevelPerms[2][start].push_back(
              FullState(index, state.Swaps(), distance));
          // Non-canonical "2-useful" states are endpoints.
          if (distance > 0) continue;
        }

        // Add all successors of this state, if we haven't already seen them.
        for (int c1 = 0; c1 < 3; c1++)
        for (int c2 = 0; c2 < 3; c2++)
        for (int fall_past_2 = 0; fall_past_2 <= 1; fall_past_2++)
        if (state.CanMove(c1, c2)) {
          Level2State state2 = state;
          state2.MakeMove(c1, c2, fall_past_2);

          // Don't allow loopy permutations or deadly patterns.
          if (PartialState::ConfigurationRepeats(state2.perm)) continue;
          PartialState::DeleteDeadlyPattern(&state2.perm);

          if (!seen.count(state2)) {
            next_states.push_back(state2);
            seen.insert(state2);
          }
        }
      }
      swap(cur_states, next_states);
      distance++;
    }
    cout << "...Done!" << endl;
  }
}


/******************************************************************************
 *                               MAIN ALGORITHM                               *
 ******************************************************************************/

// Finds a PartialState or adds it if it doesn't already exist, returning its
// index.  "source" is the index of the PartialState we computed "state" from,
// for ReachableFrom calculation.
int AddPartialState(const PartialState& state, int source) {
  int idx = find(States.begin(), States.end(), state) - States.begin();
  if (idx == States.size()) {
    States.push_back(state);
    StateReachableFrom.push_back(vector<bool>(5, false));
  }
  if (States[source].IsCanonical()) {
    // Don't go through "N+1-useful" states.
    assert(source < 5);
    StateReachableFrom[idx][source] = true;
  } else {
    for (int x = 0; x < 5; x++) {
      if (StateReachableFrom[source][x]) StateReachableFrom[idx][x] = true;
    }
  }
  return idx;
}

// Precomputes all the reachable PartialStates.
// Indices 0-4 are reserved for the 5 canonical "N+1-useful" states from which
// each level of the search runs.
// Then the reachable "N+1-useful" remaining reachable states are computed,
// first using PrecomputeLevel2States (which adds all the remaining
// "N+1-useful" permutations), and then the induced permutations that are
// merely "N-useful" are also added.
void PrecomputePartialStates() {
  States.clear();
  StateReachableFrom.clear();

  // Initialize canonical states.
  for (int i = 0; i < 5; i++) AddPartialState(PartialState(i), i);
  // Sanity check.
  for (int i = 0; i < 5; i++) {
    assert(States[i].IsCanonical());
    assert(States[i].NRowState() == i);
    assert(StateReachableFrom[i][i]);
  }

  // Add the rest of the "N+1-useful" PartialStates.
  PrecomputeLevel2Perms();

  // Precompute ApplyPermutation() and add all remaining induced PartialStates.
  // Not a very efficient way to do this, but it doesn't really matter.
  cout << "Precomputing ApplyPermutation..." << endl;
  for(;;) {
    int cur_size = States.size();

    StateApplyPermutation =
        vector<vector<vector<int> > >(cur_size,
            vector<vector<int> >(cur_size, vector<int>(2, -2)));
    for (int i = 0; i < cur_size; i++)
    for (int j = 0; j < cur_size; j++)
    for (int fall_through = 0; fall_through < 2; fall_through++) {
      // Check the prerequisites of ApplyPermutation: An "N-useful" perm
      // applied to a canonical or non-"N+1-useful" PartialState.  Also,
      // the applied permutation must be reachable from the search.
      if ((!States[i].IsUseful() || States[i].IsCanonical()) &&
          States[j].IsUseful() &&
          StateReachableFrom[j][States[i].NRowState()]) {
        PartialState state = States[i];
        if (state.ApplyPermutation(States[j], fall_through)) {
          StateApplyPermutation[i][j][fall_through] = AddPartialState(state, i);
        } else {
          StateApplyPermutation[i][j][fall_through] = -1;
        }
      }
    }
    if (cur_size == States.size()) break;
  }
  cout << "...Done!  (" << States.size() << " induced PartialStates)" << endl;

  // Precompute IsUseful().
  StateIsUseful.resize(States.size());
  for (int i = 0; i < States.size(); i++) {
    StateIsUseful[i] = States[i].IsUseful();
  }

  // Precompute IsPermuted().
  StateIsPermuted.resize(States.size());
  for (int i = 0; i < States.size(); i++) {
    StateIsPermuted[i] = States[i].IsPermuted();
  }

  // Precompute IsXSwapped().
  StateIsXSwapped.resize(States.size());
  for (int i = 0; i < States.size(); i++) {
    StateIsXSwapped[i] = States[i].IsXSwapped();
  }

  // Precompute IsCanonical().
  StateIsCanonical.resize(States.size());
  for (int i = 0; i < States.size(); i++) {
    StateIsCanonical[i] = States[i].IsCanonical();
  }

  // Precompute NRowState().
  StateNRowState.resize(States.size());
  for (int i = 0; i < States.size(); i++) {
    StateNRowState[i] = States[i].NRowState();
  }
}

// The main dynamic programming call.  Computes the N-level permutation graph
// based on the already computed N-1-level graph.
void ComputeLevelNPerms(int N) {
  assert(LevelPerms.size() == N);
  LevelPerms.resize(N+1);
  LevelPerms[N].resize(5);

  // Run 5 distinct searches: one for each canonical "N-useful" start state.
  for (int start = 0; start < 5; start++) {
    cout << "Searching on level " << N << " from canonical state " << start
         << "..." << endl;

    // The best known distance to a given perm and swap vector.
    vector<vector<int> > distance(States.size(), vector<int>(1<<N, INFINITY));

    priority_queue<FullState> q;
    q.push(FullState(start, 0, 0));
    distance[start][0] = 0;

    while (!q.empty()) {
      FullState state = q.top();
      q.pop();
      if (state.cost > distance[state.perm][state.swaps]) continue;

      // If this is an "N-useful" state, we should add it to LevelPerms.
      if (StateIsUseful[state.perm]) {
        LevelPerms[N][start].push_back(state);
        // Don't search on from here (unless we just started).
        if (state.cost > 0) continue;
      }

      // Now apply all possible "N-1-useful" permutations reachable from
      // our current state's NRowState.
      const vector<FullState>& permutations =
          LevelPerms[N-1][StateNRowState[state.perm]];
      for (int i = 0; i < permutations.size(); i++)
      for (int fall_through = 0; fall_through < 2; fall_through++) {
        int perm2 = StateApplyPermutation[state.perm]
                                         [permutations[i].perm]
                                         [fall_through];
        // Make sure our precomputation didn't miss important states.
        assert(perm2 != -2);
        if (perm2 == -1) continue;
        int swaps2 = (state.swaps ^ permutations[i].swaps);
        if (StateIsXSwapped[perm2]) swaps2 |= 1<<(N-1);
        FullState state2(perm2, swaps2, state.cost + permutations[i].cost);
        if (state2.cost < distance[state2.perm][state2.swaps]) {
          distance[state2.perm][state2.swaps] = state2.cost;
          q.push(state2);
        }
      }
    }

    cout << "...Done!  (" << LevelPerms[N][start].size()
         << " N-useful states reached)" << endl;
  }
}

// Does a simple search on the computed graph of "N-useful" states to find the
// shortest path from the start state to the start state with all blocks
// swapped.  We don't need to consider any non-trivial permutations, since the
// virtual blocks don't exist or matter.
int LevelNSolutionLength(int N) {
  // The best known distance to a given NRowState (0-4) and swap vector.
  vector<vector<int> > distance(5, vector<int>(1<<N, INFINITY));

  priority_queue<FullState> q;
  q.push(FullState(0, 0, 0));
  distance[0][0] = 0;

  while (!q.empty()) {
    FullState state = q.top();
    int nrowstate = StateNRowState[state.perm];
    q.pop();
    if (state.cost > distance[nrowstate][state.swaps]) continue;
    
    // Are we done?
    if (nrowstate == 0 && state.swaps == (1<<N)-1) return state.cost;

    const vector<FullState>& reachable = LevelPerms[N][nrowstate];
    for (int i = 0; i < reachable.size(); i++) {
      // We don't need to permute any lower blocks.
      if (!StateIsPermuted[reachable[i].perm]) {
        FullState state2(reachable[i].perm,
                         state.swaps ^ reachable[i].swaps,
                         state.cost + reachable[i].cost);
        int nrowstate2 = StateNRowState[state2.perm];
        if (state2.cost < distance[nrowstate2][state2.swaps]) {
          distance[nrowstate2][state2.swaps] = state2.cost;
          q.push(state2);
        }
      }
    }
  }
  assert(false);  // Oops!  Unreachable...?
}

main() {
  PrecomputePartialStates();
  for (int N = 2; ; N++) {
    int length = LevelNSolutionLength(N);
    cout << "  " << N << "-BLOCK PANEX SOLUTION LENGTH: " << length << endl;

    // Compute the next level of the graph.
    ComputeLevelNPerms(N+1);
  }
}
