#include <stdio.h>
//#include <bits/stdc++.h>
#include <iostream>
#include <vector>
#include <set>
#include <map>
#include <string.h>
#include <algorithm>
#include <queue>
#include <stack>
#include <cmath>
#include <utility>
#include <iomanip>
#include <cassert>
//#include <atcoder/all>

using namespace std;
#define ll long long
#define ull unsigned long long
#define rep(ind,s,n) for(ll (ind)=(s);(ind)<n;(ind)++)
#define rrep(ind,s,n) for(ll (ind)=(s);(ind)>=n;(ind)--)
#define bit(n,k) ((n>>k)&1) /*nのk bit目*/
const vector<vector<ll>> neib4 = {{0,-1},{0,1},{-1,0},{1,0}};
const vector<vector<ll>> neib8 = {{-1,-1},{0,-1},{1,-1},{-1,0},{1,0},{1,0},{-1,1},{0,1},{1,1}};
struct str{
    ll min;
    ll max;
};
struct Edge{
    ll num;
    ll from;
    ll to;
    ll cost;
};
void chmin(ll& a,ll b){
    if(b < a)a = b;
}
void chmin2(ull& a,ull b){
    if(b < a)a = b;
}
void chmax(ll& a,ll b){
    if(b > a)a = b;
}
ll INF = 1e18;
ll mod = 998244353;
ll mod1e7 = 1e9+7;
ll euc(ll a,ll b){
    if(b>a)return euc(b,a);
    if(b==0){
        return a;
    }
    return euc(b,a%b);
}
ll lcm(ll a,ll b){
    return a*b/euc(a,b);
}
ll lcm(vector<ll> args){
    ll ret = args[0];
    for(int i = 1;i < args.size();i++){
        ret = lcm(ret,args[i]);
    }
    return ret;
}


ull power(ull a,ull b,ull MOD = mod){
    ull ans = 1;
    while(b){
        if(b%2){
            ans=ans*a;
            if(MOD)ans = ans%MOD;
        }
        a=a*a;
        if(MOD){
            a = a%MOD;
        }
        b/=2;
    }
    return ans;
}
vector<pair<char,ll>> lanlen(string S){
    char bef = S[0];
    bef--;
    vector<pair<char,ll>> ret;
    rep(i,0,S.size()){
        if(S[i]!=bef){
            ret.push_back({S[i],1});
        }else{
            ret[ret.size()-1].second++;
        }
        bef = S[i];
    }
    return ret;
}
// グラフ、頂点の入次数、頂点数を受け取り、そのトポロジカルソートを記録した配列を返す関数
vector<int> topological_sort(vector<vector<ll>> &G, vector<int> &indegree, int V) {
    // トポロジカルソートを記録する配列
    vector<int> sorted_vertices;
    // 入次数が0の頂点を発見したら、処理待ち頂点としてキューに追加する
    queue<int> que;
    for (int i = 1; i < V+1; i++) {
        if (indegree[i] == 0) {
            que.push(i);
            //break;
        }
    }
    // キューが空になるまで、操作1~3を繰り返す
    while (que.empty() == false) {
        if(que.size()!=1){
            //vector<int> tmp;
            //return tmp;
        }
        // キューの先頭の頂点を取り出す
        int v = que.front();
        que.pop();
        // その頂点と隣接している頂点の入次数を減らし、0になればキューに追加
        for (int i = 0; i < G[v].size(); i++) {
            int u = G[v][i];
            indegree[u] -= 1;
            if (indegree[u] == 0) que.push(u);
        }
        // 頂点vを配列の末尾に追加する 
        sorted_vertices.push_back(v);
    }
    // トポロジカルソートを返す
    return sorted_vertices;
}
template <class T = long long>
struct UnionFindTemplate {
    vector<T> par; // par[i]:iの親の番号　(例) par[3] = 2 : 3の親が2
    vector<T> vsize;
    T Gc;
    
    UnionFindTemplate() {
    }

    UnionFindTemplate(T N) : par(N),vsize(N) { //最初は全てが根であるとして初期化
        for(T i = 0; i < N; i++) par[i] = i;
        for(T i = 0; i < N; i++) vsize[i] = 1;
        Gc = N;
    }
    
    T root(T x) { // データxが属する木の根を再帰で得る：root(x) = {xの木の根}
        if (par[x] == x) return x;
        return par[x] = root(par[x]);
    }
    
    void unite(T x, T y) { // xとyの木を併合
        T rx = root(x); //xの根をrx
        T ry = root(y); //yの根をry
        if (rx == ry) return; //xとyの根が同じ(=同じ木にある)時はそのまま
        Gc--;
        vsize[ry] += vsize[rx];
        par[rx] = ry; //xとyの根が同じでない(=同じ木にない)時：xの根rxをyの根ryにつける
    }
    
    bool same(T x, T y) { // 2つのデータx, yが属する木が同じならtrueを返す
        T rx = root(x);
        T ry = root(y);
        return rx == ry;
    }
    T size(T x){
        return vsize[root(x)];
    }
};
using UnionFind = UnionFindTemplate<ll>;

vector<ll> era(ll n){
    vector<ll> ret(n+1,1);
    ret[1] = 0;
    rep(i,1,n){
        if(ret[i]){
            for(int j=2;i*j<=n;j++){
                ret[i*j] = 0;
            }
        }
    }
    vector<ll> ans;
    rep(i,1,n+1){
        if(ret[i])ans.push_back(i);
    }
    return ans;
}

// ヒストグラフ内最大長方形
long long histglaphMaxRect(vector<ll> v){
    for(ll t:v)assert(t >= 0);
    ll ret = 0;
    v.push_back(-1);
    
    ll N = v.size();
    stack<tuple<ll,ll,ll>> s;
    s.push({-1,-1,-1});
    rep(i,0,N){
        ll lastleftindex = i;
        while(get<0>(s.top()) > v[i]){
            auto [s1,s2,s3] = s.top();
            s3 = i;
            if(ret < s1*(i-s2)){
                ret = s1*(i-s2);
            }
            lastleftindex = s2;
            s.pop();
        }
        s.push({v[i],lastleftindex,-1});
    }
    
    v.erase(--(v.end()));
    return ret;
};


template<
    class S
    ,S (*op)(S,S)
    ,S (*e)()
    ,class F
    ,S (*mapping)(F,S)
    ,F (*composition)(F,F)
    ,F (*id)()
    >
class mylazy_segtree{
    private:
        bool debugflg = false;
        ll n;
        ll size;
        ll log;
        vector<S> d;
        vector<F> ld;
        void update(ll k){
            if(k < size){
                d[k] = op(d[2*k],d[2*k+1]);
            }
        }
        void all_apply(ll k,F f){
            d[k] = mapping(f,d[k]);
            if(k < size)ld[k] = composition(f,ld[k]);
        }
        void push(ll k){
            if(k < size){
                all_apply(2*k  ,ld[k]);
                all_apply(2*k+1,ld[k]);
                ld[k] = id();
            }
        }
        S prod(ll l,ll r,ll a,ll b,ll k){
            assert(0 <= l && l <= r && r <= n);
            if(b <= l || r <= a)return e();
            push(k);
            if(l <= a && b <= r){
                return d[k];
            }
            S t1 = prod(l,r,a      ,(a+b)/2,2*k  );
            S t2 = prod(l,r,(a+b)/2,b      ,2*k+1);
            return op(t1,t2);
        }
        void apply(ll l,ll r,F f,ll a,ll b,ll k){
            if(b <= l || r <= a)return;
            push(k);
            if(l <= a && b <= r){
                all_apply(k,f);
                //push(k);
            }else{
                apply(l,r,f,a      ,(a+b)/2,2*k  );
                apply(l,r,f,(a+b)/2,b      ,2*k+1);
                update(k);
            }
            return;
        }
    public:
        mylazy_segtree(){}
        mylazy_segtree(ll _n):n(_n){
            size = 1;
            log = 1;
            while(size < n){
                size <<= 1LL;
                log++;
            }
            d.resize(2*size,e());
            ld.resize(size,id());
        }
        mylazy_segtree(vector<S> v):mylazy_segtree(v.size()){
            rep(i,0,n)set(i,v[i]);
            rrep(i,size-1,1)update(i);
        }

        void set(ll i,S p){a
            i+=size;
            for(ll j=log;j>=1;j--)push(i>>j);
            d[i] = p;
            for(ll j=1;j<=log;j++)update(i>>j);
        }
        S get(ll i){
            i+=size;
            for(ll j=log;j>=1;j--)push(i>>j);
            return d[i];
        }
        S prod(ll l,ll r){
            S tmp = prod(l,r,0,size,1);
            return tmp;     
        }
        S all_prod(){
            return d[1];
        }
        void apply(ll l,ll r,F f){
            //cout << "apply start" << endl;
            apply(l,r,f,0,size,1);
            //cout << "apply end" << endl;
        }
};

struct MyCombination{
    private:
        ll n;
        vector<ll> memokai;
        vector<ll> memokaiinv;
    public:
        MyCombination():n(0){
        }
        MyCombination(ll _n):n(_n){
            if(_n <= 0)return;
            memokai.resize(n+1);
            memokai[1]=1;
            rep(i,2,n+1){
                memokai[i] = (memokai[i-1]*i)%mod1e7;
            }
            memokaiinv.resize(n+1);
            rep(i,1,n+1){
                memokaiinv[i] = power(memokai[i],mod1e7-2);
            }
        }
        ll comb(ll a,ll b){
            if(b==0 || a==b)return 1;
            if(b==1)return a;
            ll ret = 1;
            ret = (memokai[a]*memokaiinv[a-b])%mod1e7;
            ret = (ret*memokaiinv[b])%mod1e7;
            return ret;
        }
};
/*
        using S = ll;
        struct F{
            ll range;
            ll p;
        };
        S op(S a, S b){ return std::min(a, b); }
        S e(){ return 1e9+1; }
        S mapping(F f, S x){
            x = (x*(power(f.range,mod-2,mod)*(f.range-1))%mod)%mod;
            x = (x+(f.p*power(f.range,mod-2,mod))%mod)%mod;
            return x;
        }
        F composition(F f, F g){
            F ret;
            ret.p = ((((f.range-1)*power((f.range+g.range-1)%mod,mod-2,mod))%mod)*g.p)%mod;
            ret.p = (((ret.p+(g.range*f.p)%mod)*power((f.range+g.range-1)%mod,mod-2,mod))%mod)%mod;
        
            ret.range = (((g.range*f.range)%mod)*power((f.range+g.range-1)%mod,mod-2,mod))%mod;
        }
        F id(){
            F ret;
            ret.range = 0;
            ret.p = 0;
            return ret;
        }
*/

/*
#include <atcoder/all>
using S = long long;
using F = long long;
S op(S a, S b){ return std::max(, b); }
S e(){ return 0; }
S mapping(F f, S x){ return x^=1; }
F composition(F f, F g){ return f^=1; }
F id(){ return 0; }
bool g(S x){return x>=1LL;}
//atcoder::lazy_segtree<S, op, e, F, mapping, composition, id> seg(N);

*/
//#include <atcoder/all>
//using namespace atcoder;
//using mint = modint998244353;
vector<ll> ten(211000),one(211000);
struct Srange{
    ll l;
    ll r;
    ll fl;
    public:
        Srange(){};
        Srange(ll a,ll b,ll c):l(a),r(b),fl(c){};
};
using S = vector<ll>;
using F = ll;
const F ID = INF;
S op(S a, S b){
    return a;
}
S e(){ 
    return {INF};
}
S mapping(F f, S x){
    if(f==ID)return x;
    return {f};
}
F composition(F f, F g){ 
    if(f==ID)return g;
    return f;
}
F id(){ return ID; }


class Main{
    private:
    public:
    void solve(){
        ll N;
        cin >> N;
        vector<ll> c(N);
        rep(i,0,N){
            char ch;cin >> ch;
            c[i] = ch-'a';
        }
        vector<vector<ll>> G(N);
        rep(i,0,N-1){
            ll a,b;cin >> a >> b;
            a--;b--;
            G[a].push_back(b);
            G[b].push_back(a);
        }
        vector<vector<ll>> dp(N,vector<ll>(3,0));

        auto dfs = [&](auto self,ll in,ll bef,ll dmod) -> void {
            ll cnt = 0;
            ll ans0 = 1;
            ll ans1 = 1;
            ll ans2 = 1;

            for(ll t:G[in]){
                if(t==bef)continue;
                self(self,t,in,dmod);
                cnt++;
                if(c[in] == 0){
                    ans0 *= (dp[t][0]+dp[t][2])%dmod;
                    ans0 %= dmod;
                }else if(c[in] == 1){
                    ans1 *= (dp[t][1]+dp[t][2])%dmod;
                    ans1 %= dmod;
                }
                ans2 *= (dp[t][0]+dp[t][1]+2*dp[t][2])%dmod;
                ans2 %= dmod;
            }
            if(!cnt){
                if(c[in] == 0)dp[in][0] = 1;
                if(c[in] == 1)dp[in][1] = 1;
                return;
            }
            if(c[in] == 0){
                dp[in][0] = ans0;
                dp[in][1] = 0;
                dp[in][2] = (ans2-dp[in][0]+dmod)%dmod;
            }else{
                dp[in][0] = 0;
                dp[in][1] = ans1;
                dp[in][2] = (ans2-dp[in][1]+dmod)%dmod;
            }
            return;
        };

        dfs(dfs,0,-1,mod1e7);
        cout << dp[0][2] << endl;

        return;
    }
};

#include <random>
void test(){
    rep(k,0,1000){
    ll _n = 100;
    cout << endl;
    cout << _n << " " << 40 << " " << 20 << endl;
    std::srand(k+1000);
    rep(i,0,_n){
        cout<< rand()%200001 << " ";
    }
    }
}
void wraptest(ll n){
    rep(i,0,n){
        test();
    }
}
int main() {

    Main m;
    ll t;
    t=1;
    //cin >> t;
    rep(i,0,t)m.solve();
    //test();
    

    return 0;

}