---
title: Task-3
date: 2026-05-04 15:48:42
tags:
---

## CF2159 E. Super-Short-Polynomial-San

### Statement

给定参数 $a,b,c$，你需要支持 $q$ 次询问查询 $\sum\limits_{i=0}^k[x^i](ax^2+bx+c)^n\bmod P$，$n,i$ 都是每次询问给定，强制在线。

$n,q\leq 3\times 10^5$

$1\leq a,b,c<P=10^9+7$

### Solution

{% folding title="Sol" class="green" open=false %}

首先不妨把前缀和改成提单点，即求 $[x^k]\frac{(ax^2+bx+c)^n}{1-x}$

记 $N=\max\{n\}$。

先考虑 $a=0,b=1,c=1$，这是经典组合数行前缀和问题，标准做法是莫队，在线化的话就是设置一个阈值 $B$，把 $k$ 拆成 $uB+v$，查询的是 $[x^k](x+1)^v\frac{(x+1)^{uB}}{1-x}$，预处理下每个 $\frac{(x+1)^{uB}}{1-x}$，然后查询时利用到 $(x+1)^v$ 是小于 $B$ 次的可以 $\mathcal{O}(B)$ 查询，因此时间复杂度是 $\mathcal{O}(\frac{N^2}{B})$ 预处理，$\mathcal{O}(B)$ 查询。

你期望把这个做法套用过来，需要解决的是我们需要快速处理出来 $(ax^2+bx+c)^{iB}$，从 $i-1$ 转移过来的时间复杂度是 $\mathcal{O}(BN)$，预处理就退化为 $\mathcal{O}(N^2)$ 了。

不妨设 $f(x)=(ax^2+bx+c)^n=\sum p_ix^i$，于是有

$$
\begin{aligned}
f'(x)&=n(2ax+bx)(ax^2+bx+c)^{n-1}\\
(ax^2+bx+c)f'(x)&=n(2ax+b)f(x)\\
p_{i+1}&=\frac{b(n-i)p_i+a(2n-i+1)p_{i-1}}{c(i+1)}
\end{aligned}
$$

于是就做完了。

{% endfolding %}