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
// So, we will divide up the solution of the puzzle into transitions between
// "N-useful" states.  And here's why: between "N-useful" states, only 4 blocks
// below the Nth level can possibly be touched!  One in the left which we'll
// call A, two in the middle which we'll call B and C, and one on the right
// which we'll call D.  Since a move from the left or right requires an
// "N-useful" state, we can only reach one lower block that way.  And even
// using the middle channel, there simply isn't room in the puzzle to store
// more than B or C in the upper N levels without dropping at least one to the
// left or the right.
//
// Thus there are a very limited number of permutations that can be done on the
// lower level blocks between "N-useful" states.  So for the dynamic programming
// step, we just store the cost of doing each ABCD permutation with each
// "N-useful" state transition.  When we solve lower levels we never need to
// bother with moving anything in the upper N levels (except for tracking which
// of the 5 "N-useful" states we're in).  We pretend they're a unit and we
// simply have a set of ABCD permutations to apply to our blocks, with specific
// costs.
//
// Now, up above I pretended the silver/gold blocks were indistinguishable.  Of
// course, it's important that they aren't.  So alongside permutation info
// we will also keep a "swap" bit vector that tracks whether the gold is to the
// left of the silver for levels 1 to N.  This expands the graph by 2^N states,
// but since silver and gold blocks behave the same (a very exploitable
// symmetry), we still only need to compute and store the transitions from 5
// canonical "N-useful" states (instead of all 5*2^N possible "N-useful"
// states).  Applying two permutations in a row simply XORs the "swap" bit
// vector for the two.
//
// The implementation is a bit tricky, since these "N-useful" states and ABCD
// permutations are very abstract.  Going from the Nth level to the N+1th level
// requires applying "N-useful" permutation transitions to the N+1th-level
// blocks as well as the virtual ABCD blocks that lie below the N+1th level.
// I've done my best to represent these partial states as intuitively as
// possible.


/******************************************************************************
 *                             PARTIALSTATE CLASS                             *
 ******************************************************************************/

class PartialState {
// A PartialState represents all the required information for taking the
// already-computed Nth-level graph and traversing the N+1th-level graph.  The
// top N levels are always "N-useful", but extra information is stored about
// the two N+1-blocks.
//
// In order to keep the number of PartialStates finite, the swap bit vector of
// the first N blocks is stored elsewhere; thus, in a PartialState these blocks
// are indistinguishable.
//
// It looks roughly like this (albeit transposed):
//    ...
//    .TT
//    .Xx
//    ...
//    ...
//    .B.
//    ACD
// The '.'s represent blank parts of the puzzle.
// The 'T's represent the top-level blocks.  They are always in one of the 5
// possible positions for "N-useful" states.
// Rows 2-N are elided from the state; they are empty in one channel and in the
// other two contain equivalent N-block-to-2-block towers.  Since this is an
// "N-useful" state, their position is uniquely determined by the position of
// the 'T's.
// The 'X' and 'x' represent the *distinguished* N+1-blocks.  We never see them
// leave their home row (it's all taken care of between "N-useful" states), so
// they are in 6 possible positions.
// Finally, the ABCD blocks are the virtual blocks that lie below the N+1th
// level.  We track the various ways of permuting these between "N+1-useful"
// states.  Note that the '.' rows above them are also virtual; they're useful
// since a permutation can drop blocks into a different channels.

 public:
  string channel[3];

  // Defaults to the canonical "N+1-useful" start state.
  PartialState() {
    channel[0] = ".TX...A";
    channel[1] = ".....BC";
    channel[2] = ".Tx...D";
  }
  PartialState(const char* channel0,
               const char* channel1,
               const char* channel2) {
    channel[0] = channel0;
    channel[1] = channel1;
    channel[2] = channel2;
    AssertValid();
  }
  PartialState(const PartialState& state) {
    for (int i = 0; i < 3; i++) channel[i] = state.channel[i];
  }

  bool operator==(const PartialState& state) const {
    return channel[0] == state.channel[0] &&
           channel[1] == state.channel[1] &&
           channel[2] == state.channel[2];
  }

  // Outputs a 3-line representation of the PartialState.
  void Output(ostream& out) const {
    for (int i = 0; i < 3; i++) out << channel[i] << '\n';
  }

  // Runs a sanity check that this PartialState has the expected form.
  bool IsValid() const {
    // Each channel should have be exactly 7 high.
    for (int i = 0; i < 3; i++) if (channel[i].size() != 7) return false;

    // The top middle should always be '.'.
    if (channel[1][0] != '.') return false;

    // The first two rows should contain exactly two 'T's.
    string s;
    for (int i = 0; i < 3; i++) s += channel[i][0];
    for (int i = 0; i < 3; i++) s += channel[i][1];
    sort(s.begin(), s.end());
    if (s != "....TT") return false;

    // If a 'T' lies in the top row the other one should be just below it.
    if (channel[0][0] == 'T' && channel[0][1] != 'T') return false;
    if (channel[2][0] == 'T' && channel[2][1] != 'T') return false;

    // The third row should contain a 'X' and an 'x'.
    s.clear();
    for (int i = 0; i < 3; i++) s += channel[i][2];
    sort(s.begin(), s.end());
    if (s != ".Xx") return false;

    // The 4th-7th rows should contain ABCD in some order, but always
    // bottom-justified.
    s.clear();
    for (int i = 0; i < 3; i++)
    for (int j = 3; j < 7; j++) {
      s += channel[i][j];
      if (j > 3 && channel[i][j] == '.' && channel[i][j-1] != '.') return false;
    }
    sort(s.begin(), s.end());
    if (s != "........ABCD") return false;
    return true;
  }

  void AssertValid() const {
    if (!IsValid()) {
      cerr << "PartialState validation failed:\n";
      Output(cerr);
      assert(false);
    }
  }

  // Returns whether this is an "N+1-useful" state.
  bool IsUseful() const {
    // If the 'T's are stacked, the other side must be free of 'X'/'x'.
    if (channel[0][0] == 'T') return channel[2][2] == '.';
    if (channel[2][0] == 'T') return channel[0][2] == '.';
    // Otherwise, if a channel is empty we know it's "N+1-useful".
    return channel[0][1] == '.' && channel[0][2] == '.' ||
           channel[1][1] == '.' && channel[1][2] == '.' ||
           channel[2][1] == '.' && channel[2][2] == '.';
  }

  // Returns whether ABCD are moved at all in this state.
  bool IsPermuted() const {
    return channel[0][6] != 'A' || channel[1][5] != 'B' ||
           channel[1][6] != 'C' || channel[2][6] != 'D';
  }

  // Returns whether 'X' and 'x' have been swapped in this PartialState, ie,
  // 'x' comes before 'X'.
  bool IsXSwapped() const {
    return channel[0][2] == 'x' || channel[0][2] == '.' && channel[1][2] == 'x';
  }

  // Returns whether this is one of the 5 canonical start states.
  bool IsCanonical() const {
    return !IsPermuted() && !IsXSwapped();
  }

  // Returns which of the 5 canonical start states shares its 'T' configuration
  // with this PartialState:
  //   0 - Middle channel clear
  //   1 - Left channel clear, 'T's both in row 2
  //   2 - Left channel clear, 'T's stacked on right
  //   3 - Right channel clear, 'T's both in row 2
  //   4 - Right channel clear, 'T's stacked on left
  int TState() const {
    if (channel[2][0] == 'T') return 2;
    if (channel[0][0] == 'T') return 4;
    if (channel[0][1] == '.') return 1;
    if (channel[2][1] == '.') return 3;
    return 0;
  }

  // Applies the permutation from an N-level PartialState, "perm", to this
  // N+1-level PartialState.  In recursive terms, it is as if we start with the
  // canonical "N-useful" PartialState matching the current positions of our
  // T blocks and then apply an already-computed sequence of moves that end in
  // the PartialState "perm".  This affects our PartialState in a unique,
  // well-defined way.  To determine how, this requires determining which of
  // the blocks in this PartialState (x, X, or ABCD) are the virtual ABCD
  // blocks in "perm", and then applying "perm"'s permutation to it.  Also, the
  // position of the 'T' blocks is shifted to match with "perm".
  //
  // It is a fatal error if "perm" is not an "N-useful" state, since this
  // application would make no sense (the N-blocks would end up out of
  // position, so we would no longer have an valid PartialState).
  //
  // Also, it is fatal if this PartialState is a non-canonical "N+1-useful"
  // state, ie, with 'X' and 'x' swapped or ABCD out of their starting
  // positions.  This is because "N+1-useful" states are always endpoints of 
  // the N+1-level search; if we didn't enforce this, it would be possible to
  // reach virtual blocks below ABCD, which would be bad.
  //
  // Note that even among "N-useful" permutations, some cannot be applied for
  // various reasons:
  // - 'X' and 'x' get stacked in the same channel (unlike virtual blocks,
  //   they must stay in their row!)
  // - A virtual block is stacked over 'X' or 'x'.
  bool ApplyPermutation(const PartialState& perm) {
    if (!perm.IsUseful()) {
      cerr << "ERROR: ApplyPermutation with a non-Useful PartialState:\n";
      Output(cerr);
      cerr << "  perm:\n";
      perm.Output(cerr);
      assert(false);
    }

    if (IsUseful() && !IsCanonical()) {
      cerr << "ERROR: ApplyPermutation on an N+1-Useful but non-canonical "
           << "PartialState:\n";
      Output(cerr);
      cerr << "  perm:\n";
      perm.Output(cerr);
      assert(false);
    }

    // Compute what "perm"'s virtual ABCD blocks map to in this PartialState.
    // Temporarily clear those blocks out.  (Two of these blocks are always
    // 'x' and 'X'.)
    // It is possible for some of these to map to nothing (ie, '.'); however, in
    // the actual search we should never see this '.' actually move, since this
    // would violate our "4 reachable block" condition.
    char abcd_map[4];
    int c, i, j;
    for (i = 2; i < 6 && channel[0][i] == '.'; i++)
      ;
    abcd_map[0] = channel[0][i];
    channel[0][i] = '.';
    for (i = 2; i < 6 && channel[1][i] == '.'; i++)
      ;
    abcd_map[1] = channel[1][i];
    channel[1][i] = '.';
    for (i = 2; i < 6 && channel[1][i] == '.'; i++)
      ;
    abcd_map[2] = channel[1][i];
    channel[1][i] = '.';
    for (i = 2; i < 6 && channel[2][i] == '.'; i++)
      ;
    abcd_map[3] = channel[2][i];
    channel[2][i] = '.';

    // Fill the channels, from the bottom up, with the newly permuted blocks.
    for (c = 0; c < 3; c++) {
      for (i = 6; channel[c][i] != '.'; i--)
        ;
      for (j = 6; j >= 3 && perm.channel[c][j] != '.'; j--) {
        if (abcd_map[perm.channel[c][j]-'A'] != '.') {
          if (i < 2) return false;  // Only possible with .XxABCD or similar.
          channel[c][i--] = abcd_map[perm.channel[c][j]-'A'];
        }
      }
    }

    // Float 'x' and 'X' up to their home row.  If it's not possible, the
    // PartialState is invalid; return false.
    for (c = 0; c < 3; c++)
    for (i = 6; i >= 3; i--) {
      if (channel[c][i] == 'x' || channel[c][i] == 'X') {
        if (channel[c][i-1] != '.') return false;
        swap(channel[c][i], channel[c][i-1]);
      }
    }

    // Match the state of "perm"'s top blocks.
    for (c = 0; c < 3; c++)
    for (i = 0; i < 2; i++)
      channel[c][i] = perm.channel[c][i];
 
    // Since this is a strange and complicated operation, run a final
    // validation check.
    AssertValid();
    return true;
  }
};

// The PartialState format may be intuitive, but it's not very efficient to work
// with.  So since there are a small finite number of them, we just precompute
// them all (and all operations on them) and refer to them only by index.  All
// operations are done via lookup table.
vector<PartialState> States;
vector<bool> StateIsUseful;
vector<bool> StateIsPermuted;
vector<bool> StateIsXSwapped;
vector<bool> StateIsCanonical;
vector<int> StateTState;
vector<vector<int> > StateApplyPermutation;  // -1 is used for invalid states.


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
// A Level2State looks a lot like a PartialState (with one 'T' converted to a
// 't' to distinguish it), but it's actually just manipulated like a Panex
// puzzle.  It's used for the base case search at N=2.

 private:

 public:
  string channel[3];
  Level2State() {
    channel[0] = ".TX...A";
    channel[1] = ".....BC";
    channel[2] = ".tx...D";
  }
  Level2State(const char* channel0,
              const char* channel1,
              const char* channel2) {
    channel[0] = channel0;
    channel[1] = channel1;
    channel[2] = channel2;
  }
  Level2State(const Level2State& state) {
    for (int i = 0; i < 3; i++) channel[i] = state.channel[i];
  }

  // Comparison operator so we can put this in a set.
  bool operator<(const Level2State& state) const {
    for (int c = 0; c < 3; c++) {
      if (channel[c] != state.channel[c]) return channel[c] < state.channel[c];
    }
    return false;
  }

  // Outputs a 3-line representation of the Level2State.
  void Output(ostream& out) const {
    for (int i = 0; i < 3; i++) out << channel[i] << '\n';
  }

  // Returns true if this is a "2-useful" state.
  bool Is2Useful() const {
    if (channel[1][0] != '.') return false;  // Shouldn't happen anyway.
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
  // be true, or else there is no such PartialState.
  PartialState ToPartialState() const {
    PartialState state;
    for (int c = 0; c < 3; c++) {
      state.channel[c] = channel[c];
      // Convert our 't' to the PartialState's 'T'.
      for (int i = 0; i < 2; i++) {
        if (state.channel[c][i] == 't') state.channel[c][i] = 'T';
      }
    }
    state.AssertValid();  // Better safe than sorry...
    return state;
  }

  // Returns the 2-bit swap vector corresponding to this state.  (ie, bit 0
  // is whether 't' appears before 'T', and bit 1 is whether 'x' appears
  // before 'X'.)
  int Swaps() const {
    int ret = 0;
    for (int c = 0; c < 3; c++)
    for (int i = 0; i < 2; i++) {
      if (channel[c][i] == 'T' || channel[c][i] == 't') {
        if (channel[c][i] == 't') ret |= 1;
        goto t_found;
      }
    }
t_found:
    for (int c = 0; c < 3; c++)
    for (int i = 0; i < 3; i++) {
      if (channel[c][i] == 'X' || channel[c][i] == 'x') {
        if (channel[c][i] == 'x') ret |= 2;
        goto x_found;
      }
    }
x_found:
    return ret;
  }

  // Returns true if a move is possible from channel c1 to channel c2.
  bool CanMove(int c1, int c2) const {
    if (c1 == c2) return false;
    if (channel[c2][0] != '.') return false;
    // Don't allow a useless move into the top of the middle channel.
    if (c2 == 1 && channel[c2][1] != '.') return false;
    // Make sure channel c1 isn't empty.
    for (int i = 0; i < 7; i++) if (channel[c1][i] != '.') return true;
    return false;
  }

  // Makes a move from c1 to c2.  CanMove(c1, c2) must be true.
  // if fall_past_2 is true, we allow the piece to fall beyond row 2; otherwise
  // we stop it there.  Trying both is necessary because there may be an
  // as-yet-unknown piece in row 3 which holds this virtual piece up.
  void MakeMove(int c1, int c2, bool fall_past_2) {
    char block;
    for (int i = 0; i < 7; i++) {
      if (channel[c1][i] != '.') {
        block = channel[c1][i];
        channel[c1][i] = '.';
        break;
      }
    }

    // Ts are restricted to rows 0-1 and Xs to rows 0-2.
    int max_depth = fall_past_2 ? 6 : 2, depth;
    if (block == 't' || block == 'T') max_depth = 1;
    if (block == 'x' || block == 'X') max_depth = 2;

    // Drop the block as deep as possible.
    for (depth = 0; depth <= max_depth; depth++) {
      if (channel[c2][depth] != '.') break;
    }
    channel[c2][depth-1] = block;
  }
};

// Begins the dynamic programming with the base case at N=2.  (We cannot
// start at N=1, as the basic virtual block restriction breaks down: you can
// put both blocks to one side and then manipulate virtual blocks in the other
// two channels as deep as you want.)  Done with a basic BFS.  Any
// "2-useful" PartialStates found are added to the States vector.
void PrecomputeLevel2Perms() {
  LevelPerms.clear();
  LevelPerms.resize(3);
  LevelPerms[2].resize(5);
  vector<Level2State> canonical;
  canonical.push_back(Level2State(".TX...A", ".....BC", ".tx...D"));
  canonical.push_back(Level2State("......A", ".TX..BC", ".tx...D"));
  canonical.push_back(Level2State("......A", "..X..BC", "Ttx...D"));
  canonical.push_back(Level2State(".TX...A", ".tx..BC", "......D"));
  canonical.push_back(Level2State("TtX...A", "..x..BC", "......D"));

  for (int start = 0; start < 5; start++) {
    cout << "Precomputing Level-2 States from canonical state " << start
         << "..." << endl;
    set<Level2State> seen;
    vector<Level2State> cur_states;
    int distance = 0;
    cur_states.push_back(canonical[start]);
    seen.insert(canonical[start]);

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
          if (index == States.size()) States.push_back(partial);
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

// Precomputes all the reachable PartialStates.
// Indices 0-4 are reserved for the 5 canonical "N+1-useful" states from which
// each level of the search runs.
// Then the reachable "N+1-useful" remaining reachable states are computed,
// first using PrecomputeLevel2States (which adds all the remaining
// "N+1-useful" permutations), and then the induced permutations that are
// merely "N-useful" are also added.
void PrecomputePartialStates() {
  States.clear();

  // Initialize canonical states 0-4.
  States.push_back(PartialState(".TX...A", ".....BC", ".Tx...D"));
  States.push_back(PartialState("......A", ".TX..BC", ".Tx...D"));
  States.push_back(PartialState("......A", "..X..BC", "TTx...D"));
  States.push_back(PartialState(".TX...A", ".Tx..BC", "......D"));
  States.push_back(PartialState("TTX...A", "..x..BC", "......D"));
  // Sanity check.
  for (int i = 0; i < 5; i++) {
    assert(States[i].IsCanonical());
    assert(States[i].TState() == i);
  }

  // Add the rest of the "N+1-useful" PartialStates.
  PrecomputeLevel2Perms();

  // Precompute ApplyPermutation() and add all remaining induced PartialStates.
  // Not a very efficient way to do this, but it doesn't really matter.
  cout << "Precomputing ApplyPermutation..." << endl;
  for(;;) {
    int cur_size = States.size();
    StateApplyPermutation =
        vector<vector<int> >(cur_size, vector<int>(cur_size, -1));
    for (int i = 0; i < cur_size; i++)
    for (int j = 0; j < cur_size; j++) {
      // Check the prerequisites of ApplyPermutation: An "N-useful" perm
      // applied to a canonical or non-"N+1-useful" PartialState.
      if ((!States[i].IsUseful() || States[i].IsCanonical()) &&
          States[j].IsUseful()) {
        PartialState state = States[i];
        if (state.ApplyPermutation(States[j])) {
          // Determine whether we've already seen this state; if not, add it.
          int k;
          for (k = 0; k < States.size(); k++) {
            if (States[k] == state) break;
          }
          if (k == States.size()) States.push_back(state);
          StateApplyPermutation[i][j] = k;
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

  // Precompute TState().
  StateTState.resize(States.size());
  for (int i = 0; i < States.size(); i++) {
    StateTState[i] = States[i].TState();
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
if (N == 3 && start == 1) {
cout << "  swaps " << state.swaps << "  cost " << state.cost << endl;
States[state.perm].Output(cout);
cout << endl;
}

      // If this is an "N-useful" state, we should add it to LevelPerms.
      if (StateIsUseful[state.perm]) {
        LevelPerms[N][start].push_back(state);
        // Don't search on from here (unless we just started).
        if (state.cost > 0) continue;
      }

      // Now apply all possible "N-1-useful" permutations reachable from
      // our current state's TState.
      const vector<FullState>& permutations =
          LevelPerms[N-1][StateTState[state.perm]];
      for (int i = 0; i < permutations.size(); i++) {
        int perm2 = StateApplyPermutation[state.perm][permutations[i].perm];
        if (perm2 == -1) continue;
        int swaps2 = (state.swaps ^ permutations[i].swaps);
        if (StateIsXSwapped[perm2]) swaps2 |= 1<<(N-1);
        FullState state2(perm2, swaps2, state.cost + permutations[i].cost);
if (N == 4 && start == 0 && state2.cost == 26) {
cerr << "  from swaps " << state.swaps << "  cost " << state.cost << endl;
States[state.perm].Output(cerr);
cerr << "  to swaps " << state2.swaps << "  cost " << state2.cost << endl;
States[state2.perm].Output(cerr);
cerr << endl;
}
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
// swapped.  We don't need to consider any permuted states, since the virtual
// blocks don't exist or matter.
int LevelNSolutionLength(int N) {
  // The best known distance to a given TState (0-4) and swap vector.
  vector<vector<int> > distance(5, vector<int>(1<<N, INFINITY));

  priority_queue<FullState> q;
  q.push(FullState(0, 0, 0));
  distance[0][0] = 0;

  while (!q.empty()) {
    FullState state = q.top();
    int tstate = StateTState[state.perm];
    q.pop();
    if (state.cost > distance[tstate][state.swaps]) continue;
    
    // Are we done?
    if (tstate == 0 && state.swaps == (1<<N)-1) return state.cost;

    const vector<FullState>& reachable = LevelPerms[N][tstate];
    for (int i = 0; i < reachable.size(); i++) {
      // We don't need to permute ABCD.
      if (!StateIsPermuted[reachable[i].perm]) {
        FullState state2(reachable[i].perm,
                         state.swaps ^ reachable[i].swaps,
                         state.cost + reachable[i].cost);
        int tstate2 = StateTState[state2.perm];
        if (state2.cost < distance[tstate2][state2.swaps]) {
          distance[tstate2][state2.swaps] = state2.cost;
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
