#include <bits/stdc++.h>
#include <iostream>
 
using namespace std;
 
#define ll long long
using vl=vector<ll>;
using pll=pair<ll,ll>;
using plll=pair<ll,pair<ll,ll>>;
using sl=set<ll>;
using unsl=unordered_set<ll>;
using sc=set<char>;
using unsc=unordered_set<char>;
using PQ=priority_queue<ll>;
using minPQ=priority_queue<ll,vector<ll>,greater<ll>>;
#define MOD 1000000007
#define PI = 3.1415926535897932384626433832795
#define pb push_back
#define for0(i, n) for (ll i = 0; i < (ll)(n); ++i) // 0 based indexing
#define for1(i, n) for (ll i = 1; i <= (ll)(n); ++i) // 1 based indexing
#define forc(i, l, r) for (ll i = (ll)(l); i <= (ll)(r); ++i) // closed llerver from l to r r inclusive
#define forr0(i, n) for (ll i = (ll)(n) - 1; i >= 0; --i) // reverse 0 based.
#define forr1(i, n) for (ll i = (ll)(n); i >= 1; --i) // reverse 1 based
#define fi first
#define se second
#define endl "\n"
// to be used with algorithms that processes a container Eg: find(all(c),42)
#define all(x) (x).begin(), (x).end() //Forward traversal
#define rall(x) (x).rbegin(), (x).rend() //reverse traversal
// traversal function to avoid long template definition. Now with C++11 auto alleviates the pain.
#define tr(c,i) for(__typeof__((c)).begin() i = (c).begin(); i != (c).end(); i++)
// find if a given value is present in a container. Container version. Runs in log(n) for set and map
#define present(c,x) ((c).find(x) != (c).end())
//find version works for all containers. This is present in std namespace.
#define cpresent(c,x) (find(all(c),x) != (c).end())
// Avoiding wrap around of size()-1 where size is a unsigned ll.
#define sz(a) ll((a).size())
ll min(ll a,int b) { if (a<b) return a; return b; }
ll min(int a,ll b) { if (a<b) return a; return b; }
ll max(ll a,int b) { if (a>b) return a; return b; }
ll max(int a,ll b) { if (a>b) return a; return b; }
ll gcd(ll a,ll b) { if (b==0) return a; return gcd(b, a%b); }
ll lcm(ll a,ll b) { return a/gcd(a,b)*b; }
string to_upper(string a) { for (ll i=0;i<(ll)a.size();++i) if (a[i]>='a' && a[i]<='z') a[i]-='a'-'A'; return a; }
string to_lower(string a) { for (ll i=0;i<(ll)a.size();++i) if (a[i]>='A' && a[i]<='Z') a[i]+='a'-'A'; return a; }
bool prime(ll a) { if (a==1) return 0; for (ll i=2;i<=round(sqrt(a));++i) if (a%i==0) return 0; return 1; }
#define yes "YES"
#define no "NO"
 
ll popcnt(ll x) { return __builtin_popcount(x); }
 
vector<ll> sieve(ll n)
{
    vector<ll> primes;
    vector<bool> is_prime(n + 1, true);
    is_prime[0] = is_prime[1] = false;
    for (ll i = 2; i <= n; i++)
    {
        if (is_prime[i])
        {
            primes.push_back(i);
            cout<<i<<",";
            for (ll j = i * i; j <= n; j += i)
                is_prime[j] = false;
        }
    }
    return primes;
}
 
unordered_map<ll, bool> isPrime;
bool primecheck(ll n){
    // for big primes
    // checking (2**(n-1)) % n == 1
    if(n==1) return false;
    if(n==2) return true;
    if(isPrime.count(n)) return isPrime[n];
    ll base=2, mod=n, expo=n-1, res=1;
    if(mod==1)return true;
    base%=mod;
    while(expo>0){
        if(expo&1){
            res=(res*base)%mod;
        }
        base=(base*base)%mod;
        expo >>= 1;
    }
    return isPrime[n] = (res==1);
}
 
unordered_map<ll, ll> invs;
ll inv(ll a, ll m)
{
    if (!invs.count(a))
        invs[a] = a <= 1 ? a : m - (ll)(m / a) * inv(m % a, m) % m;
    return invs[a];
}
 
ll mex (ll a, ll b) {
    priority_queue<ll, vector<ll>, greater<ll>> pq;
    pq.push(0);
    pq.push(1);
    pq.push(2);
    while(pq.top() == a || pq.top() == b){
        pq.pop();
    }
    return pq.top();
}
 
ll maxSubArraySum(vl a, ll n) {
    // account for negative numbers as well
    ll max_so_far = INT_MIN, max_ending_here = 0;
    for (ll i = 0; i < n; i++) {
        max_ending_here += a[i];
        if (max_so_far < max_ending_here) {
            max_so_far = max_ending_here;
        }
        if (max_ending_here < 0) {
            max_ending_here = 0;
        }
    }
    return max_so_far;
}
 
vector<ll> genR(ll n){
    vector<ll> row;
    row.push_back(1); // first element is always 1
 
    ll val=1;
    for(int i=1;i<n;i++){
        val = val * (n - i) / i; // calculate binomial coefficient C(n, i)
        row.push_back(val);
    }
    return row;
}
 
vector<vector<ll>> pascalTriangle(ll n) {
    vector<vector<ll>> pt;
    for(int i=1;i<=n;i++){
        vector<ll> row = genR(i);
        pt.push_back(row);
    }
    return pt;
}
 
// DSU (Union–Find) structure
struct DSU {
    vector<int> p, r;
    DSU(int n): p(n, -1), r(n, 0) {}
    int find(int x) {
        return p[x] < 0 ? x : p[x] = find(p[x]);
    }
    // returns true if a and b were in different components
    bool unite(int a, int b) {
        a = find(a); 
        b = find(b);
        if (a == b) return false;
        if (r[a] < r[b]) swap(a, b);
        p[b] = a;
        if (r[a] == r[b]) r[a]++;
        return true;
    }
};

void solve() {
    ll n,m;
    cin>>n>>m;

    vl a(n);
    for0(i,n) cin>>a[i];

    sort(all(a), greater<ll>());
    ll lmt = max(n,m);
    ll ans= 0;
    ll k = min(n, m);
    for (ll i = 0; i < k; ++i) {
        ans += a[i] * (m - i);
    }

    cout<<ans;
}
 
int_fast32_t main()
{
    ios::sync_with_stdio(false);
    cin.tie(nullptr);  
    cout.tie(nullptr);
 
#ifndef ONLINE_JUDGE
    freopen("input.txt", "r", stdin);
    freopen("time.txt", "w", stderr);
    freopen("output.txt", "w", stdout);
#endif
 
    ll t = 1; // default for single test case
    cin >> t;
    while (t--)
    {
        solve();
        cout << "\n";
    }
 
    cerr << "time taken : " << (float)clock() / CLOCKS_PER_SEC << " secs" << endl;
    return 0;
}