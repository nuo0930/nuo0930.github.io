---
title: Montgomery 模乘
date: 2026-04-19 01:17:08
tags: algorithms
mathjax: true
thumbnail: "/images/波奇2.jpg"
---

核心在于把数表示成 $x\equiv \frac{y}{R}\pmod P$ 的形式，其中 $R=2^k>P$。

我们需要解决在已知 $y$ 的情况下如何快速得到 $x$，显然有 $xR+aP=y$，反过来看 $a$ 是 $\mathbb{Z}_R$ 上 $P$ 的逆元乘以 $y$，于是预处理下 $P$ 的逆元的相反数 $b$，取 $a=by\bmod R$，就有 $x=\frac{aP+y}{R}$，可以分析出这样 $x$ 介于 $[0,P)$ 内，而且只需要利用到乘法、自然溢出与右移，因此优化明显。至于加减乘都是在此基础上容易实现的，这是我的实现（需要特化 $P=2$），一个小技巧是可以只限制 $y$ 在 $[0,2P)$ 上，这样乘法时可以少判断一次：

```cpp
#ifndef RAINSTOP_MODINT
//我喜欢王煜婷 QwQ
#define RAINSTOP_MODINT
#ifndef DEBUG
#define NDEBUG
#endif
#include<cassert>
#include<chrono>
#include<utility>
#include<cstdint>
#include<type_traits>
#include<iostream>
template<uint64_t P> class ModInt;
template<uint64_t P> constexpr ModInt<P> qpw(ModInt<P>,uint64_t);
template<uint64_t P> constexpr ModInt<P> inv(ModInt<P>);
template<uint64_t P> constexpr ModInt<P> sqrt(ModInt<P>);
template<uint64_t P>
class ModInt{
    static_assert(!(P>>62));
    static_assert(P&1);
private:
    static constexpr uint64_t PP=P<<1;
    uint64_t x;
    static constexpr uint64_t calc_pinv(){
        uint64_t inv=P;
        return inv*=2-P*inv,inv*=2-P*inv,inv*=2-P*inv,inv*=2-P*inv,inv*=2-P*inv,-inv;
    }
    static constexpr uint64_t calc_r2(){
        __uint128_t r=-1;
        return r%P+1;
    }
    static constexpr uint64_t PINV=calc_pinv(),R2=calc_r2();
    static constexpr uint64_t reduce(__uint128_t T){
        uint64_t m=uint64_t(T)*PINV;
        uint64_t t=(T+__uint128_t(m)*P)>>64;
        return t;
    }
    struct RawConstructTag{};
    constexpr ModInt(uint64_t raw_val,RawConstructTag):x(raw_val){}
public:
    constexpr ModInt():x(0){}
    constexpr ModInt(uint64_t _x):x(reduce((__uint128_t)(_x)*R2)){
        if consteval{
            if(_x>=PP)
                throw "Compile-time Error: You've forgotten to reduce x in [0,2P)!";
        }else{
            assert(_x<PP);
        }
    }
    constexpr uint64_t val()const{uint64_t t=reduce(x);return t-(P&-(t>=P));}
    constexpr ModInt operator+(const ModInt&rhs)const{
        uint64_t t=x+rhs.x;
        return ModInt(t-=(PP&-(t>=PP)),RawConstructTag{});
    }
    constexpr ModInt operator-(const ModInt&rhs)const{
        uint64_t t=x-rhs.x;
        return ModInt(t+=(PP&(int64_t(t)>>63)),RawConstructTag{});
    }
    constexpr ModInt operator*(const ModInt&rhs)const{
        return ModInt(reduce(__uint128_t(x)*rhs.x),RawConstructTag{});
    }
    constexpr ModInt operator-()const{
        return ModInt((PP-x)&((int64_t)(-x)>>63),RawConstructTag{});
    }
    constexpr ModInt&operator+=(const ModInt&rhs){
        return x+=rhs.x,x-=(PP&-(x>=PP)),*this;
    }
    constexpr ModInt&operator-=(const ModInt&rhs){
        return x-=rhs.x,x+=(PP&(int64_t(x)>>63)),*this;
    }
    constexpr ModInt&operator*=(const ModInt&rhs){
        return x=reduce(__uint128_t(x)*rhs.x),*this;
    }
    constexpr bool operator==(const ModInt&rhs)const{
        uint64_t a=x-(P&(-(x>=P))),b=rhs.x-(P&(-(rhs.x>=P)));
        return a==b;
    }
    constexpr bool operator!=(const ModInt&rhs)const{
        uint64_t a=x-(P&(-(x>=P))),b=rhs.x-(P&(-(rhs.x>=P)));
        return a!=b;
    }
    friend constexpr ModInt<P> qpw<>(ModInt<P>,uint64_t);
    friend constexpr ModInt<P> inv<>(ModInt<P>);
    friend constexpr ModInt<P> sqrt<>(ModInt<P>);
};
template<uint64_t P>
constexpr ModInt<P> qpw(ModInt<P> x,uint64_t y){
    ModInt<P> res{1};
    for(;y;y>>=1,x*=x)
        if(y&1)
            res*=x;
    return res;
}
template<uint64_t P>
constexpr ModInt<P> inv(ModInt<P> x){
    if consteval{
        if(x==ModInt<P>(0))
            throw "Comiple-time Error: Attempted to calculate inverse of zero";
    }else{
        assert(x!=ModInt<P>(0));
    }
    ModInt<P> res{1};
    for(uint64_t y=P-2;y;y>>=1,x*=x)
        if(y&1)
            res*=x;
    return res;
}
template<uint64_t P>
constexpr ModInt<P> sqrt(ModInt<P>x){
    if(x==ModInt<P>(0))return x;
    if consteval{
        if(qpw(x,(P-1)>>1)!=ModInt<P>(1))
            throw "Compile-time Error: Attempted to calculate sqrt of a non-quadratic residue!";
    }else{
        assert(qpw(x,(P-1)>>1)==ModInt<P>(1));
    }
    ModInt<P> a{},w2;
    for(;qpw(w2=a*a-x,(P-1)>>1)==ModInt<P>(1);a+=ModInt<P>(1));
    if(w2==ModInt<P>(0))return a;
    uint64_t y=(P+1)>>1;
    std::pair<ModInt<P>,ModInt<P>>res{ModInt<P>(1),ModInt<P>()},X{a,ModInt<P>(1)};
    auto mul=[&w2](const std::pair<ModInt<P>,ModInt<P>>&a,const std::pair<ModInt<P>,ModInt<P>>&b) constexpr ->std::pair<ModInt<P>,ModInt<P>> {
        return {a.first*b.first+a.second*b.second*w2,a.first*b.second+a.second*b.first};
    };
    for(;y;y>>=1,X=mul(X,X))if(y&1)res=mul(res,X);
    return res.first;
}
template<> class ModInt<2>;
template<> constexpr ModInt<2> qpw(ModInt<2>,uint64_t);
template<> constexpr ModInt<2> inv(ModInt<2>);
template<> constexpr ModInt<2> sqrt(ModInt<2>);
template<>
class ModInt<2>{
private:
    uint8_t x;
public:
    constexpr ModInt<2>():x(0){}
    constexpr ModInt<2>(uint64_t _x):x(_x&1){}
    constexpr uint64_t val(){return x;}
    constexpr ModInt<2> operator+(const ModInt<2>&rhs)const{
        return ModInt<2>(x^rhs.x);
    }
    constexpr ModInt<2> operator-(const ModInt<2>&rhs)const{
        return ModInt<2>(x^rhs.x);
    }
    constexpr ModInt<2> operator*(const ModInt<2>&rhs)const{
        return ModInt<2>(x&rhs.x);
    }
    constexpr ModInt<2> operator-()const{
        return ModInt<2>(x);
    }
    constexpr ModInt<2>&operator+=(const ModInt<2>&rhs){
        return x^=rhs.x,*this;
    }
    constexpr ModInt<2>&operator-=(const ModInt<2>&rhs){
        return x^=rhs.x,*this;
    }
    constexpr ModInt<2>&operator*=(const ModInt<2>&rhs){
        return x&=rhs.x,*this;
    }
    constexpr bool operator==(const ModInt<2>&rhs)const{return x==rhs.x;}
    constexpr bool operator!=(const ModInt<2>&rhs)const{return x!=rhs.x;}
    constexpr friend ModInt<2> qpw<>(ModInt<2>,uint64_t);
    constexpr friend ModInt<2> inv<>(ModInt<2>);
    constexpr friend ModInt<2> sqrt<>(ModInt<2>);
};
template<>
constexpr ModInt<2> qpw(ModInt<2>x,uint64_t y){
    return ModInt<2>(x.x|(!y));
}
template<>
constexpr ModInt<2> inv(ModInt<2>x){
    if consteval{
        if(x==ModInt<2>(0))
            throw "Comiple-time Error: Attempted to calculate inverse of zero";
    }else{
        assert(x!=ModInt<2>(0));
    }
    return x;
}
template<>
constexpr ModInt<2> sqrt(ModInt<2>x){
    return x;
}
#ifndef DEBUG
#undef NDEBUG
#endif
#undef CONSTEXPR_ASSERT
#endif
```