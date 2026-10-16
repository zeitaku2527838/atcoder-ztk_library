#include <bits/stdc++.h>
#include <random>
#include <atcoder/all>
using namespace std;
using ll = long long;
using vecl = vector<ll>;
using vvecl = vector<vecl>;
using vvvecl = vector<vvecl>;
using vecd = vector<double>;
using vvecd = vector<vecd>;
using vvvecd = vector<vvecd>;
using vecs = vector<string>;
using pairl = pair<ll,ll>;
using paird = pair<double,double>;
using vecpl = vector<pairl>;
using setl = set<ll>;
using mapl = map<ll,ll>;
using deql = deque<ll>;
template <class T> using pque/*降順*/ = priority_queue<T>;
template <class T> using rpque/*昇順*/ = priority_queue<T, vector<T>, greater<T>>;
#define rep(i,n) for(ll i=0; i<n; i++)
#define rep2(i,l,r) for(ll i=l; i<r; i++)
#define pushb push_back
#define popb pop_back
#define pushf push_front
#define popf pop_front
#define lowb lower_bound
#define upb upper_bound
#define all(v) v.begin(),v.end()
#define rall(v) v.rbegin(),v.rend()
#define fix(n) fixed << setprecision(n)
#define endl "\n"
#define YES cout<<"Yes"<<endl
#define NO cout<<"No"<<endl
#define ALICE cout<<"Alice"<<endl
#define BOB cout<<"Bob"<<endl
const ll INF = 0x1fffffffffffffff;
const ll NFP = 1 ? /*1*/998244353LL : /*0*/1000000007LL;
const vector<pairl> d4 = {{1,0},{0,1},{-1,0},{0,-1}};
const vector<pairl> d8 = {{1,0},{1,1},{0,1},{-1,1},{-1,0},{-1,-1},{0,-1},{1,-1}};
ll powll(ll n, ll m)/*ll用のnのm乗.*/{ll res=1,t=n;while(m){if(m&1)res=res*t;t=t*t;m>>=1;}return res;}
ll sqrtll(ll x)/*ll用のsqrt(x)*/{ll res=(ll)sqrt(x);while((res+1)*(res+1)<=x)res++;while(x<res*res)res--;return res;}
ll logll(ll x)/*ll用のlog2(x)*/{ll res=(ll)log2(x);if(x==0)return-INF;while(1LL<<(res+1)<=x)res++;while(x<1LL<<res)res--;return res;}
ll modpow(ll n, ll m, ll p)/*nのm乗を正整数pで割った余り.*/{ll res=1%p;while(m){if(m&1)res=res*n%p;n=n*n%p;m>>=1;}return res;}
#define mpow(n,m) modpow(n,m,NFP) /*法が混在しているときに用いてはならない.*/
ll modinv(ll n,ll p)/*nの,nと互いに素な正整数pを法とするmod逆元.*/{struct tpl{ll x,y,r;};tpl t0={1,0,n},t1={0,1,p};while(t1.r){ll q=t0.r/t1.r;t0={t0.x-q*t1.x,t0.y-q*t1.y,t0.r-q*t1.r};swap(t0,t1);}if(t0.r==1)return(t0.x%p+p)%p;else throw runtime_error("`modinv` requires coprime arguments");}
#define minv(n) modinv(n,NFP) /*法が混在しているときに用いてはならない.*/
pair<vecl,vecl> modfac(ll n, ll p)/*n以下の非負整数iの階乗をiと互いに素な正整数pで割った余りとそのmod逆元の配列*/{pair<vecl,vecl> res;auto&[pt,nt]=res;pt.resize(n+1),nt.resize(n+1);pt[0]=1;rep(i,n)pt[i+1]=pt[i]*(i+1)%p;nt[n]=modinv(pt[n],p);rep(i,n)nt[n-i-1]=nt[n-i]*(n-i)%p;return res;}
#define mfac(n) modfac(n,NFP) /*法が混在しているときに用いてはならない.*/
ll gcd(ll n, ll m)/*正整数n,mの最大公約数(n,mの大小を問わない)*/{if(n<m)swap(n,m);ll r=n%m;if(r)return gcd(m,r);else return m;};
ll randll(ll n)/*シード値をnとする一様非負整数乱数*/{mt19937_64 mt(n);uniform_int_distribution<ll> dis((ll)0,0x7fffffffffffffff);return dis(mt);}
ll clockll()/*ll用の現在時刻[ns](初期時刻は不定)*/{return (chrono::duration_cast<chrono::nanoseconds>(chrono::steady_clock::now().time_since_epoch())).count();}
namespace ztk {
    template <class T> class sorted_vector {
        private:
            ll root = -1;
            struct node {
                optional<T> value;
                ll size = 0;
                ll height = 0;
                ll parent = -1;
                ll left = -1, right = -1;
            };
            vector<node> tree;
            ll search(ll p, optional<T> v){
                if(!tree[p].value.has_value()){
                    return p;
                }else{
                    if(v.value() < tree[p].value.value()){
                        return search(tree[p].left, v);
                    }else if(tree[p].value.value() < v.value()){
                        return search(tree[p].right, v);
                    }else{
                        return p;
                    }
                }
            }
            ll search_next(ll p, optional<T> v){
                if(!tree[p].value.has_value()){
                    return p;
                }else{
                    if(v.value() < tree[p].value.value()){
                        return search_next(tree[p].left, v);
                    }else{
                        return search_next(tree[p].right, v);
                    }
                }
            }
            void rot_l(ll &p){
                ll nxp = tree[p].right;
                if(p==root) root = nxp;
                else{
                    if(tree[tree[p].parent].left == p) tree[tree[p].parent].left = nxp;
                    else tree[tree[p].parent].right = nxp;
                }
                tree[nxp].parent = tree[p].parent;
                tree[p].parent = nxp;
                tree[tree[nxp].left].parent = p;
                tree[p].right = tree[nxp].left;
                tree[nxp].left = p;
                tree[p].size = tree[tree[p].left].size + tree[tree[p].right].size + 1;
                tree[nxp].size = tree[tree[nxp].left].size + tree[tree[nxp].right].size + 1;
                tree[p].height = max(tree[tree[p].left].height,tree[tree[p].right].height)+1;
                tree[nxp].height = max(tree[tree[nxp].left].height,tree[tree[nxp].right].height)+1;
                p = nxp;
            }
            void rot_r(ll &p){
                ll nxp = tree[p].left;
                if(p==root) root = nxp;
                else{
                    if(tree[tree[p].parent].left == p) tree[tree[p].parent].left = nxp;
                    else tree[tree[p].parent].right = nxp;
                }
                tree[nxp].parent = tree[p].parent;
                tree[p].parent = nxp;
                tree[tree[nxp].right].parent = p;
                tree[p].left = tree[nxp].right;
                tree[nxp].right = p;
                tree[p].size = tree[tree[p].left].size + tree[tree[p].right].size + 1;
                tree[nxp].size = tree[tree[nxp].left].size + tree[tree[nxp].right].size + 1;
                tree[p].height = max(tree[tree[p].left].height,tree[tree[p].right].height)+1;
                tree[nxp].height = max(tree[tree[nxp].left].height,tree[tree[nxp].right].height)+1;
                p = nxp;
            }
            void append(ll p, optional<T> v){
                ll sz = tree.size();
                tree[p] = {
                    v,
                    3,
                    1,
                    tree[p].parent,
                    sz, sz+1
                };
                tree.push_back({
                    nullopt,
                    1,
                    0,
                    p,
                    -1, -1
                });
                tree.push_back({
                    nullopt,
                    1,
                    0,
                    p,
                    -1, -1
                });
                while(p!=-1){
                    if(tree[tree[p].left].height+1 < tree[tree[p].right].height){
                        if(tree[tree[tree[p].right].left].height > tree[tree[tree[p].right].right].height){
                            ll tp = tree[p].right;
                            rot_r(tp);
                        }
                        rot_l(p);
                    }else if(tree[tree[p].left].height > tree[tree[p].right].height+1){
                        if(tree[tree[tree[p].left].left].height < tree[tree[tree[p].left].right].height){
                            ll tp = tree[p].left;
                            rot_l(tp);
                        }
                        rot_r(p);
                    }
                    tree[p].size = tree[tree[p].left].size+tree[tree[p].right].size+1;
                    tree[p].height = max(tree[tree[p].left].height,tree[tree[p].right].height)+1;
                    p = tree[p].parent;
                }
            }
            void remove(ll p){
                ll nxp;
                while(tree[tree[p].left].value.has_value() || tree[tree[p].right].value.has_value()){
                    if(tree[tree[p].left].value.has_value()){
                        nxp = tree[p].left;
                        while(tree[tree[nxp].right].value.has_value()){
                            nxp = tree[nxp].right;
                        }
                        swap(tree[p].value, tree[nxp].value);
                        swap(p,nxp);
                    }else if(tree[tree[p].right].value.has_value()){
                        nxp = tree[p].right;
                        while(tree[tree[nxp].left].value.has_value()){
                            nxp = tree[nxp].left;
                        }
                        swap(tree[p].value, tree[nxp].value);
                        swap(p,nxp);
                    }
                }
                if(p == root){
                    root = -1;
                }else{
                    tree[p] = {
                        nullopt,
                        1,
                        0,
                        tree[p].parent,
                        -1, -1
                    };
                }
                p = tree[p].parent;
                while(p!=-1){
                    if(tree[tree[p].left].height+1 < tree[tree[p].right].height){
                        if(tree[tree[tree[p].right].left].height > tree[tree[tree[p].right].right].height){
                            ll tp = tree[p].right;
                            rot_r(tp);
                        }
                        rot_l(p);
                    }else if(tree[tree[p].left].height > tree[tree[p].right].height+1){
                        if(tree[tree[tree[p].left].left].height < tree[tree[tree[p].left].right].height){
                            ll tp = tree[p].left;
                            rot_l(tp);
                        }
                        rot_r(p);
                    }
                    tree[p].size = tree[tree[p].left].size+tree[tree[p].right].size+1;
                    tree[p].height = max(tree[tree[p].left].height,tree[tree[p].right].height)+1;
                    p = tree[p].parent;
                }
            }
        public:
            using value_type = T;
            using size_type = size_t;
            using reference = T&;
            using const_reference = const T&;
            sorted_vector() = default;
            ~sorted_vector() = default;
            size_type size(){
                if(root==-1) return 0;
                return tree[root].size/2;
            }
            void push(const_reference v){
                if(root==-1){
                    root = tree.size();
                    tree.push_back({
                        v,
                        3,
                        1,
                        -1,
                        root+1, root+2
                    });
                    tree.push_back({
                        nullopt,
                        1,
                        0,
                        root,
                        -1, -1
                    });
                    tree.push_back({
                        nullopt,
                        1,
                        0,
                        root,
                        -1, -1
                    });
                }else{
                    append(search_next(root, v),v);
                }
            }
            void pop(const_reference v){
                if(root==-1) return;
                ll p = search(root,v);
                if(!tree[p].value.has_value()) return;
                if(v == tree[p].value.value()){
                    remove(p);
                }
            }
            ll lower_bound(const_reference v){
                ll res = 0, p = root;
                while(p!=-1 && tree[p].value.has_value()){
                    if(v <= tree[p].value){
                        p = tree[p].left;
                    }else{
                        res += tree[p].size/2;
                        p = tree[p].right;
                        res -= tree[p].size/2;
                    }
                }
                return res;
            }
            ll upper_bound(const_reference v){
                ll res = 0, p = root;
                while(p!=-1 && tree[p].value.has_value()){
                    if(v < tree[p].value){
                        p = tree[p].left;
                    }else{
                        res += tree[p].size/2;
                        p = tree[p].right;
                        res -= tree[p].size/2;
                    }
                }
                return res;
            }
            reference operator[](size_type ix){
                ll p = root;
                ll ac=0, wa=tree[root].size/2;
                while(ac+1<wa){
                    if(ix < ac + tree[tree[p].left].size/2){
                        wa = ac + tree[tree[p].left].size/2;
                        p = tree[p].left;
                    }else if(ac + tree[tree[p].left].size/2 < ix){
                        ac = ac + tree[tree[p].left].size/2 + 1;
                        p = tree[p].right;
                    }else{
                        ac = ac + tree[tree[p].left].size/2;
                        wa = ac;
                    }
                }
                return tree[p].value.value();
            }
    };
    template <class T> class treap_vector {
        private:
            ll root = -1;
            struct node {
                optional<T> value;
                ll size = 0;
                ll height = 0;
                ll parent = -1;
                ll left = -1, right = -1;
            };
            vector<node> tree;
            ll search(ll ix){
                ll p = root;
                ll ac=0, wa=tree[root].size/2+1;
                while(ac+1<wa){
                    if(ix < ac + tree[tree[p].left].size/2){
                        wa = ac + tree[tree[p].left].size/2;
                        p = tree[p].left;
                    }else if(ac + tree[tree[p].left].size/2 < ix){
                        ac = ac + tree[tree[p].left].size/2 + 1;
                        p = tree[p].right;
                    }else{
                        ac = ac + tree[tree[p].left].size/2;
                        wa = ac;
                    }
                }
                return p;
            }
            void rot_l(ll &p){
                ll nxp = tree[p].right;
                if(p==root) root = nxp;
                else{
                    if(tree[tree[p].parent].left == p) tree[tree[p].parent].left = nxp;
                    else tree[tree[p].parent].right = nxp;
                }
                tree[nxp].parent = tree[p].parent;
                tree[p].parent = nxp;
                tree[tree[nxp].left].parent = p;
                tree[p].right = tree[nxp].left;
                tree[nxp].left = p;
                tree[p].size = tree[tree[p].left].size + tree[tree[p].right].size + 1;
                tree[nxp].size = tree[tree[nxp].left].size + tree[tree[nxp].right].size + 1;
                tree[p].height = max(tree[tree[p].left].height,tree[tree[p].right].height)+1;
                tree[nxp].height = max(tree[tree[nxp].left].height,tree[tree[nxp].right].height)+1;
                p = nxp;
            }
            void rot_r(ll &p){
                ll nxp = tree[p].left;
                if(p==root) root = nxp;
                else{
                    if(tree[tree[p].parent].left == p) tree[tree[p].parent].left = nxp;
                    else tree[tree[p].parent].right = nxp;
                }
                tree[nxp].parent = tree[p].parent;
                tree[p].parent = nxp;
                tree[tree[nxp].right].parent = p;
                tree[p].left = tree[nxp].right;
                tree[nxp].right = p;
                tree[p].size = tree[tree[p].left].size + tree[tree[p].right].size + 1;
                tree[nxp].size = tree[tree[nxp].left].size + tree[tree[nxp].right].size + 1;
                tree[p].height = max(tree[tree[p].left].height,tree[tree[p].right].height)+1;
                tree[nxp].height = max(tree[tree[nxp].left].height,tree[tree[nxp].right].height)+1;
                p = nxp;
            }
            void append(ll p, optional<T> v){
                ll sz = tree.size();
                tree[p] = {
                    v,
                    3,
                    1,
                    tree[p].parent,
                    sz, sz+1
                };
                tree.push_back({
                    nullopt,
                    1,
                    0,
                    p,
                    -1, -1
                });
                tree.push_back({
                    nullopt,
                    1,
                    0,
                    p,
                    -1, -1
                });
                while(p!=-1){
                    if(tree[tree[p].left].height+1 < tree[tree[p].right].height){
                        if(tree[tree[tree[p].right].left].height > tree[tree[tree[p].right].right].height){
                            ll tp = tree[p].right;
                            rot_r(tp);
                        }
                        rot_l(p);
                    }else if(tree[tree[p].left].height > tree[tree[p].right].height+1){
                        if(tree[tree[tree[p].left].left].height < tree[tree[tree[p].left].right].height){
                            ll tp = tree[p].left;
                            rot_l(tp);
                        }
                        rot_r(p);
                    }
                    tree[p].size = tree[tree[p].left].size+tree[tree[p].right].size+1;
                    tree[p].height = max(tree[tree[p].left].height,tree[tree[p].right].height)+1;
                    p = tree[p].parent;
                }
            }
            void remove(ll p){
                ll nxp;
                while(tree[tree[p].left].value.has_value() || tree[tree[p].right].value.has_value()){
                    if(tree[tree[p].left].value.has_value()){
                        nxp = tree[p].left;
                        while(tree[tree[nxp].right].value.has_value()){
                            nxp = tree[nxp].right;
                        }
                        swap(tree[p].value, tree[nxp].value);
                        swap(p,nxp);
                    }else if(tree[tree[p].right].value.has_value()){
                        nxp = tree[p].right;
                        while(tree[tree[nxp].left].value.has_value()){
                            nxp = tree[nxp].left;
                        }
                        swap(tree[p].value, tree[nxp].value);
                        swap(p,nxp);
                    }
                }
                if(p == root){
                    root = -1;
                }else{
                    tree[p] = {
                        nullopt,
                        1,
                        0,
                        tree[p].parent,
                        -1, -1
                    };
                }
                p = tree[p].parent;
                while(p!=-1){
                    if(tree[tree[p].left].height+1 < tree[tree[p].right].height){
                        if(tree[tree[tree[p].right].left].height > tree[tree[tree[p].right].right].height){
                            ll tp = tree[p].right;
                            rot_r(tp);
                        }
                        rot_l(p);
                    }else if(tree[tree[p].left].height > tree[tree[p].right].height+1){
                        if(tree[tree[tree[p].left].left].height < tree[tree[tree[p].left].right].height){
                            ll tp = tree[p].left;
                            rot_l(tp);
                        }
                        rot_r(p);
                    }
                    tree[p].size = tree[tree[p].left].size+tree[tree[p].right].size+1;
                    tree[p].height = max(tree[tree[p].left].height,tree[tree[p].right].height)+1;
                    p = tree[p].parent;
                }
            }
        public:
            using value_type = T;
            using size_type = size_t;
            using reference = T&;
            using const_reference = const T&;
            treap_vector() = default;
            ~treap_vector() = default;
            size_type size(){
                if(root==-1) return 0;
                return tree[root].size/2;
            }
            void push(size_type ix, const_reference v){
                if(root==-1){
                    root = tree.size();
                    tree.push_back({
                        v,
                        3,
                        1,
                        -1,
                        root+1, root+2
                    });
                    tree.push_back({
                        nullopt,
                        1,
                        0,
                        root,
                        -1, -1
                    });
                    tree.push_back({
                        nullopt,
                        1,
                        0,
                        root,
                        -1, -1
                    });
                }else{
                    ll p = search((ll)ix);
                    if(!tree[p].value.has_value()) append(p,v);
                    else{
                        p = tree[p].left;
                        while(tree[p].value.has_value()){
                            p = tree[p].right;
                        }
                        append(p,v);
                    }
                }
            }
            void pop(size_type ix){
                if(root==-1) return;
                ll p = search((ll)ix);
                if(!tree[p].value.has_value()) return;
                remove(p);
            }
            reference operator[](size_type ix){
                ll p = search((ll)ix);
                return tree[p].value.value();
            }
    };
    template <ll mod> struct modll {
        ll value;
        modll() : value(0LL){}
        modll(const ll &a){
            value = a%mod;
            if(value<0) value += mod;
        }
        modll<mod> inv() const{
            struct tpl{
                ll x,y,r;
            };
            tpl t0={1,0,value}, t1={0,1,mod};
            while(t1.r){
                ll q = t0.r/t1.r;
                t0 = {t0.x-q*t1.x, t0.y-q*t1.y, t0.r-q*t1.r};
                swap(t0,t1);
            }
            return modll<mod>(t0.x);
        }
        modll<mod>& operator+=(const modll<mod> &a){
            value = (value+a.value)%mod;
            return *this;
        }
        friend modll<mod> operator+(const modll<mod> &b, const modll<mod> &a){
            return modll<mod>(b) += a;
        }
        modll<mod>& operator-=(const modll<mod> &a){
            value = (value-a.value +mod)%mod;
            return *this;
        }
        friend modll<mod> operator-(const modll<mod> &b, const modll<mod> &a){
            return modll<mod>(b) -= a;
        }
        modll<mod>& operator*=(const modll<mod> &a){
            value = value*a.value %mod;
            return *this;
        }
        friend modll<mod> operator*(const modll<mod> &b, const modll<mod> &a){
            return modll<mod>(b) *= a;
        }
        modll<mod>& operator^=(ll a){
            modll<mod> r = *this;
            value = 1;
            while(a){
                if(a&1) *this *= r;
                r *= r;
                a >>= 1;
            }
            return *this;
        }
        friend modll<mod> operator^(const modll<mod> &b, const ll &a){
            return modll<mod>(b) ^= (ll)a;
        }
        modll<mod>& operator/=(const modll<mod> &a){
            *this *= a.inv();
            return *this;
        }
        friend modll<mod> operator/(const modll<mod> &b, const modll<mod> &a){
            return modll<mod>(b) /= a;
        }
        friend bool operator==(const modll<mod> &b, const modll<mod> &a){
            return b.value == a.value;
        }
    };
    template <class T> struct vec2 {
        T x;
        T y;
        vec2() : x(0),y(0) {}
        vec2(const pair<T,T> &a){
            x = a.first;
            y = a.second;
        }
        template <class U>
        vec2(const vec2<U> &a){
            x = (T)a.x;
            y = (T)a.y;
        }
        vec2<T>& operator+=(const vec2<T> &a){
            x += a.x;
            y += a.y; 
            return *this;
        }
        vec2<T>& operator-=(const vec2<T> &a){
            x -= a.x;
            y -= a.y; 
            return *this;
        }
        vec2<T>& operator*=(const T &a){
            x *= a;
            y *= a; 
            return *this;
        }
        vec2<T>& operator/=(const T &a){
            x /= a;
            y /= a; 
            return *this;
        }
        vec2<T>& operator%=(const T &a){
            x %= a;
            y %= a; 
            return *this;
        }
        friend vec2<T> operator+(const vec2<T> &b, const vec2<T> &a){
            return vec2<T>(b) += a;
        }
        friend vec2<T> operator-(const vec2<T> &b, const vec2<T> &a){
            return vec2<T>(b) -= a;
        }
        friend vec2<T> operator*(const vec2<T> &b, const T &a){
            return vec2<T>(b) *= a;
        }
        friend vec2<T> operator*(const T &b, const vec2<T> &a){
            return vec2<T>(a) *= b;
        }
        friend T operator*(const vec2<T> &b, const vec2<T> &a){
            return b.x*a.x + b.y*a.y;
        }
        friend vec2<T> operator/(const vec2<T> &b, const T &a){
            return vec2<T>(b) /= a;
        }
        friend vec2<T> operator%(const vec2<T> &b, const T &a){
            return vec2<T>(b) %= a;
        }
        friend bool operator==(const vec2<T> &l, const vec2<T> &r){
            return l.x==r.x && l.y==r.y;
        }
        friend bool operator<(const vec2<T> &l, const vec2<T> &r){
            return atan2(l.y,l.x) < atan2(r.y,r.x);
        }
        friend bool operator>(const vec2<T> &l, const vec2<T> &r){
            return atan2(l.y,l.x) > atan2(r.y,r.x);
        }
        friend bool operator<=(const vec2<T> &l, const vec2<T> &r){
            return l<r || l==r;
        }
        friend bool operator>=(const vec2<T> &l, const vec2<T> &r){
            return l>r || l==r;
        }
    };
}
using mll = ztk::modll<NFP>;/*法が混在しているときに用いてはならない.*/
using v2l = ztk::vec2<ll>;
using v2d = ztk::vec2<double>;

/*
    https://github.com/zeitaku2527838/atcoder-ztk_library.git
*/



int main() {
    
    ll mitana;

}
