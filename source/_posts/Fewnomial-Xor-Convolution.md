---
title: 稀疏集合幂级数对称差卷积
date: 2026-04-19 01:38:59
tags: algorithms
mathjax: true
thumbnail: "/images/我们都拥有海洋.jpg"
---

{% callout type="primary" title="Statement" class="custom-class" %}

对于一个奇素数 $P$，在环 $\mathbb{F}_P[x_1,x_2,\cdots,x_n]/(x_1^2-1,x_2^2-1,\cdots,x_n^2-1)$ 求

$$
\prod_{i=1}^m\sum_{j=1}^{d_i}a_j\prod_{k=1}^n x_k^{c_{i,j,k}}
$$

保证 $0\leq c_{i,j,k}<2$，且 $2^{d_i}$ 之和以及 $2^n$ 不大。

{% endcallout %}

不妨假定 $F_P$ 上的运算是 $\mathcal{O}(1)$ 的。

朴素做法是对每个少项式做一次 FWT 再点乘起来求 IFWT，但是这样时间复杂度是 $\mathcal{O}(nm2^n)$ 的，并没有利用到 $2^{d_i}$ 之和不大的性质。

那你考虑你希望让你能做一遍 FWT 承担这么多次乘法，就比如说如果你只需要对位加的话可以利用 FWT 的线性性只改那么几个点，但是这里是乘法，所以你希望你的 FWT 是对原本的对数值做的，因此你需要在此前对对数值先做一次 IFWT，不难说明做完后非 $0$ 的位置也只有不超过 $2^{d_i}$ 个。

接下来需要解决的是避开求离散对数这一步。

(TBD)

[模板](https://qoj.ac/problem/85)

目前搭配我的蒙哥马利模乘是 QOJ 最优解第一，但是其实也只有乐零和我写了…… 

一个小优化是可以平移下下标这样把每个少项式的某一项下标强制钦定 $0$，相当于可以少做一次。写线性基说不定还可以再减少常数，但是显然这个可以卡满。

```cpp
#include<bits/stdc++.h>
#include"modint.hpp"
using namespace std;
namespace Mortis{
constexpr uint64_t P=1000000000000125953;
using mint=ModInt<P>;
struct Xorshift64s{
    uint64_t s;
    constexpr Xorshift64s(uint64_t seed=20100107):s(seed){}
    constexpr uint64_t operator()(){
        s^=s>>12,s^=s<<25,s^=s>>27;
        return s*0x2545F4914F6CDD1Dull;
    }
};
class info{
private:
    static constexpr mint calc_t(){
        Xorshift64s rng{};
        mint x;
        for(;x={uint64_t((__uint128_t(rng())*(P-1))>>64)+1},qpw(x,(P-1)>>1)==mint(1););
        return x;
    }
    static const mint t;
    static const mint invt;
    static inline int k=-1;
public:
    static void set_k(int _k){k=_k;}
    mint xp,xq;
    long long y;uint64_t cnt0;
private:
    info(mint _xp,mint _xq,long long _y,uint64_t _cnt0):xp(_xp),xq(_xq),y(_y),cnt0(_cnt0){}
public:
    info():xp(1),xq(1),y(0),cnt0(0){}
    info(mint _x,int _k):xp(_x),xq(1),y(0),cnt0(0){
        if(_x==mint{}){xp=mint(1),cnt0=1;}
        else{
            for(int i=0;i<_k;++i){
                if(qpw(xp,(P-1)>>1)==ModInt<P>(1))xp=sqrt(xp);
                else xp=sqrt(xp*invt),y|=1ull<<i;
            }y<<=k-_k;
        }
    }
    info operator*(const info&rsh)const{return info(xp*rsh.xp,xq*rsh.xq,y+rsh.y,cnt0+rsh.cnt0);}
    info operator/(const info&rsh)const{return info(xp*rsh.xq,xq*rsh.xp,y-rsh.y,cnt0-rsh.cnt0);}
    info&operator*=(const info&rsh){return xp*=rsh.xp,xq*=rsh.xq,y+=rsh.y,cnt0+=rsh.cnt0,*this;}
    info&operator/=(const info&rsh){return xp*=rsh.xq,xq*=rsh.xp,y-=rsh.y,cnt0-=rsh.cnt0,*this;}
    mint val(){
        if(cnt0)return mint{};
        if(y>0)return xp*qpw(xq,P-2)*qpw(t,y>>k);
        else if(y<0)return xp*qpw(xq,P-2)*qpw(invt,(-y)>>k);
        else return xp*qpw(xq,P-2);
    }
};
constexpr mint info::t=calc_t();
constexpr mint info::invt=inv(info::t);
void main(){
    int n,m,k;
    cin>>n>>m>>k,k=0;
    vector<vector<pair<int,uint64_t>>>a(m);
    for(auto&b:a){
        int d;cin>>d;
        k=max(k,d-1);
        b.resize(d);
        for(auto&[s,_]:b)cin>>s;
        for(auto&[_,x]:b)cin>>x;
    }
    vector<info>f(1<<n);
    info::set_k(k);
    int delta=0;
    for(auto&b:a){
        int d=b.size()-1;
        int u=b[d].first;mint v=b[d].second;
        delta^=u;
        vector<int>mask(1<<d);
        vector<mint>g(1<<d);
        for(int i=0;i<d;++i)tie(mask[1<<i],g[1<<i])=b[i],mask[1<<i]^=u;
        for(int s=1;s<(1<<d);++s)mask[s]=mask[s^(s&(-s))]^mask[s&(-s)];
        for(int i=0;i<d;++i)
            for(int s=0;s<(1<<d);++s)
                if((s>>i)&1){
                    int t=s^(1<<i);
                    auto p=g[t],q=g[s];
                    g[t]=p+q,g[s]=p-q;
                }
        for(int s=0;s<(1<<d);++s)g[s]+=v;
        vector<info>h(1<<d);
        for(int s=0;s<(1<<d);++s)h[s]=info(g[s],d);
        for(int i=0;i<d;++i)
            for(int s=0;s<(1<<d);++s)
                if((s>>i)&1){
                    int t=s^(1<<i);
                    auto p=h[t],q=h[s];
                    h[t]=p*q,h[s]=p/q;
                }
        for(int s=0;s<(1<<d);++s)f[mask[s]]*=h[s];
    }
    for(int i=0;i<n;++i)
        for(int s=0;s<(1<<n);++s)
            if((s>>i)&1){
                int t=s^(1<<i);
                auto p=f[t],q=f[s];
                f[t]=p*q,f[s]=p/q;
            }
    vector<mint>res(1<<n);
    for(int s=0;s<(1<<n);++s)res[s]=f[s].val();
    for(int i=0;i<n;++i)
        for(int s=0;s<(1<<n);++s)
            if((s>>i)&1){
                int t=s^(1<<i);
                auto p=res[t],q=res[s];
                res[t]=(p+q)*mint((P+1)>>1),res[s]=(p-q)*mint((P+1)>>1);
            }
    for(int s=0;s<(1<<n);++s)cout<<res[s^delta].val()<<' ';
}
}
int main(){
    ios_base::sync_with_stdio(false),cin.tie(nullptr);
    Mortis::main();
    return 0;
}
```