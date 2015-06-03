#include <algorithm>
#include <cstring>
#include <iostream>
#include <map>
#include <queue>
#include <string>
#include <vector>
using namespace std;

#define FORALL(s,i) for (typeof(s.begin()) i=s.begin(); i != s.end(); ++i)

// A state consists of three strings of appropriate length, with pieces
// represented by 'a','b','c'... and 'A','B','C' and gaps by '.'.  The start of
// the string is the top of each channel.
//
// Thus, the starting state for a puzzle of height 6 is
// {".ABCDE","......",".abcde"}.
//
// Intermediate states can also have "don't-care" pieces represented by '0'-'9'.
// These pieces are large enough to go anywhere in the channels.
struct State {
  vector<string> channel;

  State() : channel(3) {}
  bool operator<(const State& st) const {return channel < st.channel;}

  // Returns true if there are no pieces in channel c.
  bool ChannelEmpty(int c) const {
    for (int i = 0; i < channel[c].size(); i++) {
      if (channel[c][i] != '.') return false;
    }
    return true;
  }

  // Returns true if moving the top piece of channel c1 to channel c2 is
  // possible.  Moves to the top of the middle channel are useless, so not
  // allowed.
  bool CanMove(int c1, int c2) const {
    if (c1 == c2) return false;
    if (channel[c2][0] != '.') return false;
    if (c2 == 1 && channel[c2][1] != '.') return false;
    return !ChannelEmpty(c1);
  }

  // Returns a neighbour state created by moving the top piece of channel
  // c1 to channel c2.  CanMove(c1,c2) must be true.
  State Neighbour(int c1, int c2) const {
    int c1i, c2i;
    for (c1i = 0; channel[c1][c1i] == '.'; c1i++)
      ;
    char ch = channel[c1][c1i];
    int max_depth = channel[c2].size()-1;
    if (ch >= 'A' && ch <= 'Z') max_depth = min(max_depth, (int)(ch-'A'+1));
    if (ch >= 'a' && ch <= 'z') max_depth = min(max_depth, (int)(ch-'a'+1));
    for (c2i = 0; c2i <= max_depth && channel[c2][c2i] == '.'; c2i++)
      ;
    State ret = *this;
    swap(ret.channel[c1][c1i], ret.channel[c2][c2i-1]);
    return ret;
  }

  // Returns true if this state is "useful" as a partial state: in other words,
  // if more layers are added to the puzzle a new move will be immediately
  // possible.  This requires a clear channel, and some more restrictions:
  // - If the clear channel is on one side, the top of the other side must be
  //   '.' or a digit.  (A clear channel on one side is very restrictive.)
  // - If the clear channel is in the middle, at least one of the side's tops
  //   must be '.' or a digit.
  bool Useful() const {
    if (ChannelEmpty(0)) {
      return channel[2][0] == '.' ||
             channel[2][0] >= '0' && channel[2][0] <= '9';
    } else if (ChannelEmpty(2)) {
      return channel[0][0] == '.' ||
             channel[0][0] >= '0' && channel[0][0] <= '9';
    } else if (ChannelEmpty(1)) {
      return channel[0][0] == '.' ||
             channel[0][0] >= '0' && channel[0][0] <= '9' ||
             channel[2][0] == '.' ||
             channel[2][0] >= '0' && channel[2][0] <= '9';
    }
    return false;
  }
};

// The canonical form of a state exploits all the reversible forms of symmetry
// in the puzzle so that the dynamic programming portion of the algorithm only
// needs to store small portions of the graph.
//
// Transformations applied:
// 'X' < 'x' (for each letters x).
// All letters large enough to go anywhere are converted to digits.
// '0' < '1' < '2' < ...
// Channel 0 < Channel 2 (after applying the above transforms).
//
// A StateCanonicalizer stores the canonicalizing transformation so it can be
// easily applied forwards and backwards multiple times.
class StateCanonicalizer {
 public:
  StateCanonicalizer(const State& state) {
    memset(translate, 0, sizeof(translate));
    translate['.'] = '.';

    int height = state.channel[0].size();
    int num_largest = 0;
    for (int c = 0; c < 3; c++)
    for (int i = 0; i < state.channel[c].size(); i++) {
      char ch = state.channel[c][i];
      if (!translate[ch]) {
        if (ch >= '0' && ch <= '9' ||
            ch > 'A'+height-2 && ch <= 'Z' ||
            ch > 'a'+height-2 && ch <= 'z') {
          translate[ch] = '0' + num_largest++;
        } else if (ch >= 'A' && ch <= 'Z') {
          translate[ch] = ch;
          translate[ch+'a'-'A'] = ch+'a'-'A';
        } else {
          translate[ch] = ch+'A'-'a';
          translate[ch+'A'-'a'] = ch;
        }
      }
      untranslate[translate[ch]] = ch;
    }

    swap_channels = (TranslateString(state.channel[0]) >
                     TranslateString(state.channel[2]));
  }

  void Apply(State* state) const {
    for (int c = 0; c < 3; c++) {
      state->channel[c] = TranslateString(state->channel[c]);
    }
    if (swap_channels) swap(state->channel[0], state->channel[2]);
  }

  void Unapply(State* state) const {
    if (swap_channels) swap(state->channel[0], state->channel[2]);
    for (int c = 0; c < 3; c++) {
      state->channel[c] = UntranslateString(state->channel[c]);
    }
  }

 private:
  string TranslateString(const string& s) const {
    string ret;
    for (int i = 0; i < s.size(); i++) ret += translate[s[i]];
    return ret;
  }
  string UntranslateString(const string& s) const {
    string ret;
    for (int i = 0; i < s.size(); i++) ret += untranslate[s[i]];
    return ret;
  }

  char translate[128];
  char untranslate[128];
  bool swap_channels;
};

// Compares pair<State, int>s in order of decreasing distance.
struct StateDistanceComparator {
  bool operator()(const pair<State, int>& a, const pair<State, int>& b) const {
    return a.second > b.second;
  }
};

// Takes a starting state of any channel height, and finds all the "useful"
// reachable states, along with their distance.  "Useful" is defined as having
// one channel empty, as only these kinds of states can be used for moves of
// lower depth.  This function should itself only be called for "useful"
// states, to keep the cache size low (although it works fine for any state).
//
// Results are cached (in canonicalized form) to reduce runtime complexity.
map<State, map<State, int> > memoized_search_from;
map<State, int> SearchFrom(State start_state) {
  // The trivial state has only itself as a neighbour.
  if (start_state.channel[0].size() == 0) {
    map<State, int> result;
    result[start_state] = 0;
    return result;
  }

  int height = start_state.channel[0].size();
  StateCanonicalizer canonicalizer(start_state);
  canonicalizer.Apply(&start_state);
  map<State, int>& memo = memoized_search_from[start_state];
  if (!memo.size()) {
    // Maintain a heap to process reachable states in order by distance.
    // Only states with one channel empty (except possibly the lowest space)
    // are processed; a recursive call fills the gaps between these.
    priority_queue<pair<State, int>, vector<pair<State, int> >,
                   StateDistanceComparator> queue;
    queue.push(make_pair(start_state, 0));
    memo[start_state] = 0;
    while (!queue.empty()) {
      int cur_distance = queue.top().second;
      State cur_state = queue.top().first;
      queue.pop();
/*bool error = false;
for (int c = 0; c < 3; c++)
for (int i = 0; i < cur_state.channel[c].size(); i++) {
char ch = cur_state.channel[c][i];
if (ch == '.' || ch >= '0' && ch <= '9' || ch >= 'a' && ch <= 'z' || ch >= 'A' && ch <= 'Z') break;
error = true;
}
if (error) {
cerr << "ERROR:" << endl;
cerr << (int)cur_state.channel[0][0] << endl;
for (int c = 0; c < 3; c++) cerr << cur_state.channel[c] << endl;
cerr << endl;
exit(0);
}*/
      if (memo[cur_state] < cur_distance) {
        // We already processed this state at a lower distance; ignore.
        continue;
      }

/*if (height >= 4) {
cout << "Distance " << cur_distance << ":\n";
for (int i = 0; i < 3; i++) cout << " " << cur_state.channel[i] << '\n';
cout << '\n';
}*/
      // Try all moves (if any) that involve the lowest layer of the state.
      // These are the only ones the recursive call won't handle.
      for (int c1 = 0; c1 < 3; c1++)
      for (int c2 = 0; c2 < 3; c2++)
      if (cur_state.CanMove(c1, c2)) {
        pair<State, int> to_insert;
        to_insert.first = cur_state.Neighbour(c1, c2);
        if (to_insert.first.channel[c1][height-1] ==
                  cur_state.channel[c1][height-1] &&
            to_insert.first.channel[c2][height-1] ==
                  cur_state.channel[c2][height-1]) {
          // The transition did not involve the lowest layer.
          continue;
        }
        to_insert.second = cur_distance + 1;
        pair<map<State, int>::iterator, bool> insert_result =
            memo.insert(to_insert);
        if (!insert_result.second) {
          if (to_insert.second < insert_result.first->second) {
            // "memo" already has this state but at a higher distance.
            insert_result.first->second = to_insert.second;
          } else {
            // "memo" already has this state at a lower distance; ignore it.
            continue;
          }
        }
        queue.push(to_insert);
      }

      // Now recurse to search the graph of states reachable without moves that
      // involve the lowest layer.
      State clipped_state;
      for (int c = 0; c < 3; c++) {
        clipped_state.channel[c] = cur_state.channel[c].substr(0, height-1);
      }
      map<State, int> recursive_search = SearchFrom(clipped_state);
      FORALL(recursive_search, it) {
        pair<State, int> to_insert;
        for (int c = 0; c < 3; c++) {
          to_insert.first.channel[c] =
              it->first.channel[c] + cur_state.channel[c][height-1];
          // With the lower layer added we might be able to shift some pieces
          // further down.
          for (int i = height-1; i > 0; i--) {
            if (to_insert.first.channel[c][i] != '.') break;
            char ch = to_insert.first.channel[c][i-1];
            if (ch >= 'A' && ch <= 'A'+i-2 || ch >= 'a' && ch <= 'a'+i-2) {
              break;  // Piece won't fit.
            }
            swap(to_insert.first.channel[c][i],
                 to_insert.first.channel[c][i-1]);
          }
        }
        to_insert.second = cur_distance + it->second;
        pair<map<State, int>::iterator, bool> insert_result =
            memo.insert(to_insert);
        if (!insert_result.second) {
          if (to_insert.second < insert_result.first->second) {
            // "memo" already has this state but at a higher distance.
            insert_result.first->second = to_insert.second;
          } else {
            // "memo" already has this state at a lower distance; ignore it.
            continue;
          }
        }
        queue.push(to_insert);
      }
    }

    // Now remember only the "useful" states.  Everything else is discarded.
    FORALL(memo, it) {
      while (it != memo.end() && !it->first.Useful()) {
        memo.erase(it++);
      }
    }
static int counts[50];
cout << memo.size() << " results for:\n";
for (int i = 0; i < 3; i++) cout << " " << start_state.channel[i] << '\n';
counts[start_state.channel[0].size()]++;
for (int i = 0; i <= 11; i++) cout << counts[i] << ' ';
cout << "\n\n";
  }

  map<State, int> result;
  FORALL(memo, it) {
    State state = it->first;
    canonicalizer.Unapply(&state);
    result[state] = it->second;
  }
  return result;
}

main() {
  State st, st2;
  st.channel[0] =  ".......W";
  st.channel[1] =  ".ABC..XY";
  st.channel[2] =  ".abc...Z";
  st2.channel[0] = ".AB......";
  st2.channel[1] = "...C.WXY";
  st2.channel[2] = ".abc...Z";
  map<State, int> seen;
  map<State, State> prev;
  vector<State> cur;
  cur.push_back(st);
  seen[st] = 0;
  int d = 0;
  while (!seen.count(st2) && cur.size()) {
    vector<State> next;
    d++;
    for (int i = 0; i < cur.size(); i++) {
      int c;
      for (c = 0; c < 3; c++) {
        if (cur[i].channel[c].substr(0, 3) == "...") break;
      }
      if (c == 0 && cur[i].channel[1][1] == '.' ||
          c == 0 && cur[i].channel[2][0] == '.' ||
          c == 2 && cur[i].channel[1][1] == '.' ||
          c == 2 && cur[i].channel[0][0] == '.' ||
          c == 1 && cur[i].channel[0][0] == '.' && cur[i].channel[2][0] == '.') {
        cout << "  cost " << d-1 << endl;
        for (int c2 = 0; c2 < 3; c2++) cout << cur[i].channel[c2] << endl;
        cout << endl;
        //if (d > 1 && cur[i].channel[c].substr(0, 4) == "....") continue;
      }

      for (int c1 = 0; c1 < 3; c1++)
      for (int c2 = 0; c2 < 3; c2++)
      if (cur[i].CanMove(c1, c2)) {
        State newst = cur[i].Neighbour(c1, c2);
        if (seen.count(newst)) continue;
        seen[newst] = d;
        prev[newst] = cur[i];
        next.push_back(newst);
      }
    }
    cur = next;
  }
  cout << seen.size() << " states seen." << endl;
  cout << "Distance = " << seen[st2] << endl;
  for (State s = st2; s.channel != st.channel; s = prev[s]) {
    cout << endl;
    cout << s.channel[0] << endl;
    cout << s.channel[1] << endl;
    cout << s.channel[2] << endl;
  }
}
