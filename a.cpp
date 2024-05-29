#include <algorithm>
#include <cmath>
#include <iostream>
#include <queue>
#include <set>
#include <vector>

using namespace std;
using ld = long double;



struct PR {
    static const int inf = 1'000'000'000;
    int n;
    vector<vector<int>> capacity, flow;
    vector<int> height, excess, seen;
    queue<int> excess_vertices;
    PR(int n): n(n) {
        capacity.assign(n, vector<int>(n, 0));        
    }

    void add_cap(int a, int b, int c) {
        capacity[a][b] += c;
    }

    void push(int u, int v) {
        int d = min(excess[u], capacity[u][v] - flow[u][v]);
        flow[u][v] += d;
        flow[v][u] -= d;
        excess[u] -= d;
        excess[v] += d;
        if (d && excess[v] == d)
            excess_vertices.push(v);
    }

    void relabel(int u) {
        int d = inf;
        for (int i = 0; i < n; i++) {
            if (capacity[u][i] - flow[u][i] > 0)
                d = min(d, height[i]);
        }
        if (d < inf)
            height[u] = d + 1;
    }

    void discharge(int u) {
        while (excess[u] > 0) {
            if (seen[u] < n) {
                int v = seen[u];
                if (capacity[u][v] - flow[u][v] > 0 && height[u] > height[v])
                    push(u, v);
                else
                    seen[u]++;
            } else {
                relabel(u);
                seen[u] = 0;
            }
        }
    }
    
    int max_flow(int s, int t) {
        height.assign(n, 0);
        height[s] = n;
        flow.assign(n, vector<int>(n, 0));
        excess.assign(n, 0);
        excess[s] = inf;
        for (int i = 0; i < n; i++) {
            if (i != s)
                push(s, i);
        }
        seen.assign(n, 0);

        while (!excess_vertices.empty()) {
            int u = excess_vertices.front();
            excess_vertices.pop();
            if (u != s && u != t)
                discharge(u);
        }

        int max_flow = 0;
        for (int i = 0; i < n; i++)
            max_flow += flow[i][t];
        return max_flow;
    }
};


const int I = 3;
const int U = 3;



const int T = 2;
const int N = 1;

vector<int> Precs[U];

void GenRecs() {
    Precs[0] = {0, 1};
    Precs[1] = {0, 2};
    Precs[2] = {0, 2};
}



const int V = U + I + 2;
const int S = V - 2;
const int F = V - 1;

int G[V][V];

void BuildGraph() {
    for (int user = 0; user < U; ++user) {
        for (int item : Precs[user]) {
            G[user + I][item] = G[item][user + I] = 1;
        }
    }
}

set<int> banned;

void Remove(vector<int> sub) {
    for (int i = 0; i < V; ++i) {
        for (int v : sub) {
            G[v][i] = G[i][v] = 0;
        }
    }
    for (int v : sub) {
        banned.insert(v);
    }
}


ld ALPHA;

int ItemDegree(int item) {
    int degree = 0;
    for (int user = 0; user < U; ++user) {
        for (int i : Precs[user]) {
            if (i == item) {
                ++degree;
            }
        }
    }
    return degree;
}

int Rank(int user, int item) {
    int rank = 1;
    for (int i : Precs[user]) {
        if (item == i) {
            return rank;
        } 
        ++rank;
    }
    throw;
}

void ComputeWeights(PR &pr) {
    int CT = 0;
    for (int i = 0; i < I; ++i) {
        int deg = ItemDegree(i);
        for (int u = 0; u < U; ++u) {
            if (G[i][u + I]) {
                int rank = Rank(u, i);
                int w = ceil(ALPHA * deg + (1 - ALPHA) * rank);
                pr.add_cap(i, u + I, w);
                CT += w;
            }
        }
    }
    auto div_up = [](int a, int b) {
        return (a + b - 1) / b;
    };

    int CeqI = div_up(CT, I);
    int CeqU = div_up(CT, U);
    
    for (int i = 0; i < I; ++i) {
        if (banned.find(i) == banned.end()) {
            pr.add_cap(S, i, CeqI);
        }
    }
    for (int u = 0; u < U; ++u) {
        pr.add_cap(u + I, F, CeqU);
    }
}

void ConstructRec() {
    vector<vector<int>> Ic(U);
    for (int u = 0; u < U; ++u) {
        for (int i : Precs[u]) {
            if (banned.count(i)) {
                Ic[u].push_back(i);
            }
        }
    }
    vector<int> V(I, 0);
    for (int u = 0; u < U; ++u) {
        Precs[u].resize(N);
        for (int i : Precs[u]) {
            ++V[i];
        }
    }
    for (int u = 0; u < U; ++u) {
        sort(Precs[u].begin(), Precs[u].end(), [&](int lhs, int rhs){
            return V[lhs] < V[rhs];
        });
        if (Ic[u].size() > N) Ic[u].resize(N);
        Precs[u].resize(N - Ic[u].size());
        for (int x : Ic[u]) {
            Precs[u].push_back(x);
        }
    }
}

void print_recs() {
    set<int> dif = {};
    for (int u = 0; u < U; ++u) {
        cout << "for user " << u << " : ";
        for (int i = 0; i < N; ++i) {
            dif.insert(Precs[u][i]);
            cout << Precs[u][i] << ' ';
        }
        cout << "\n";
    }
    cout << "\nCoverage is " << dif.size() << '\n';
}

void Input() {
    cout << "Please enter ALPHA" << endl;
    cin >> ALPHA;
}

int32_t main() {
    Input();
    GenRecs();
    cout << "Initial Recommendations:\n";
    print_recs();

    BuildGraph();
    vector<vector<int>> subgraphs;
    while (banned.size() != I) {
        PR pr(V);
        ComputeWeights(pr);
        pr.max_flow(S, F);
        vector<int> subgraph = {};
        for (int i = 0; i < I; ++i) {
            if (banned.find(i) != banned.end()) continue;
            if (pr.height[i] >= U + I + 2)
            subgraph.push_back(i);
        }
        if (subgraph.empty()) {
            break;
        }
        subgraphs.push_back(subgraph);
        Remove(subgraph);
    }

    ConstructRec();
    cout << "\nFinal recommendations:\n";
    print_recs();
}