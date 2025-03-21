# [CDP11] 组会论文笔记

$$
\newcommand{\com}[1]{\left[#1\right]}
\newcommand{\vcom}[1]{\com{\mathbf{#1}}}
\newcommand{\mac}{\mathsf{MAC}}
\newcommand{\bf}{\mathbf}
\newcommand{\bbF}{\mathbb{F}}
\newcommand{\dim}{\mathsf{dim}}
\newcommand{\enc}{\mathsf{Encode}}
$$

这是前三周小组会上的一篇笔记。

阅读：

- Ronald Cramer, Ivan Damgard and Valerio Pastro. On the **Amortized** Complexity of Zero Knowledge Protocols for Multiplicative Relations

贡献：

- 给出了信息论承诺方案和线性秘密分享方案
- 给出了乘法协议（over field），通信复杂度相比于[CDD99]降低了$l$倍
- 给出了乘法协议（over integer），相比于[DO97,DF02]，不需要任何假设，并且通信复杂度增加较少。
- 将乘法协议扩展到电路中，给出了验证电路的协议，并给出了利用MPC-in the head进一步降低了通信复杂度的方法。

关键技术：

- 预处理的信息论承诺方案：预处理阶段要使得承诺方和接收方带有**未知随机数**，且二者的未知随机数**相互关联**
- 乘法协议/验证电路协议：将许多相似的陈述的证明合并到一个协议中，使得每个证明的**摊销复杂度**变小
- 验证电路协议：利用MPC-in the head ，将对一些随机数的同态承诺换为对MPC各方的View的承诺（不需要满足同态性），进而降低通信复杂度

## 1 工具一：信息论承诺

利用添加**预处理**过程，使得信息论安全、简单高效的**同态**承诺方案成为可能。

## 1.1 有限域上

$K$ 是一个很小的域，$L$ 是其扩域，下面是对 $v_1,\cdots,v_\ell\in K$ 的承诺：

- 预处理阶段：可信第三方发送随机的 $u_1,\cdots,u_\ell\leftarrow K$ 以及对应的 $\{m_i:=a\cdot u_i+b_i\}_{i\in [\ell]}$ 给承诺者，发送对应的 $a,b_i\leftarrow L$ 给接收者
  - 可以认为发送者持有 $u_i$ 信息及其 $\mac_{sk_i}(u_i)$，而接收者持有 $sk_i=(a,b_i)$
- 承诺阶段：发送者发送 $u_i-v_i$ 作为承诺；接收者计算 $\mac_{sk_i}(u_i-v_i)$
- 打开阶段：发送者发送 $v_i,\mac_{sk_i}(u_i)$ 作为打开；接收者检验是否有 $a\cdot v_i+\mac_{sk_i}(u_i-v_i)=\mac_{sk_i}(u_i)$

此带有处理的承诺具有统计 binding 和统计 hiding 性质：

- 统计 binding：承诺发送者在打开阶段无法打开两个 $v_i\not=v_i'$，否则发送者可以计算出 $(a,b_i)$，事实上 $(a,b_i)$ 的信息是信息论掩盖的（发送者只收到预处理的 $u_i,\mac_{sk_i}(u_i)$）
- 统计 hiding：接收者无法判断发送者承诺的是消息 $v_i$ 还是 $v_i'$，这也是一样的原因，接收者只知道 $sk_i=(a,b_i)$，而没有关于 $u_i$ 的信息

具体地，我们可以计算出打破binding的概率：

- $1/|L|$

同时也容易注意到上述性质是具有同态性的：

- 预处理部分：$u_i+u_j,\mac_{a,b_i+b_j}(u_i+u_j):=\mac_{sk_i}(u_i)+\mac_{sk_j}(u_j)$
- 发送者信息部分：$v_i+v_j$
- 接收者密钥部分：$sk_{ij}:=(a,b_i+b_j)=sk_i\oplus sk_j$
- 承诺部分：$(u_i-v_i)+(u_j-v_j)$
- 检验部分：$a\cdot (v_i+v_j)+\mac_{sk_{ij}}(u_i-v_i+u_j-v_j)=\mac_{sk_i}(u_i)+\mac_{sk_j}(u_j)$

## 1.2 整数上

要承诺 $k$ 比特的数 $m_1,\cdots,m_\ell$：

- 预处理：
  - 发送给承诺者 $u_i\leftarrow [-2^{k+\kappa},\cdots,2^{k+\kappa}]$ 和对应的 $\mac_{a,b_i}(u_i)$
  - 发送给接收者 $a\leftarrow \mathsf{Prime}([-2^\kappa,\cdots,2^\kappa])$ 和 $b_i\leftarrow [-2^{k+3\kappa},\cdots,2^{k+3\kappa}]$

- 其他的都是类似的

此带有处理的承诺具有统计 binding 和统计 hiding 性质：

- 统计 binding：能否计算 $a\cdot \Delta_1=\Delta_2$，仅仅知道 $u_i,\mac_{a,b_i}(u_i)$
  - 这里也可以看出为什么 $a,b_i$ 的范围要如此取，$b_i$ 需要完全 smudge $a\cdot u_i$
  - 需要计算 condition on $u_i,\mac_{a,b_i}(u_i)$ 下，$(a,b_i)$ 有多少种选择可能：$\Theta(2^\kappa/\kappa)$

- 统计 hiding：使用 smudging lemma

同时也容易注意到上述性质是具有同态性的，但是由于是在 $\Z$ 上的，无法支持无限次操作。

## 2 工具二：线性秘密分享

下面给出支持打包（packed）线性秘密分享方案的线性代数描述，可以对照**packed shamir sharing**进行理解：（LSSS 是 SS 的一种特殊情况，SS 的完整描述需要对**控制结构**的刻画，例如可以利用布尔电路；而 LSSS 我们可以很方便地使用）

- 下面的描述可以用 packed-Shamir Sharing 作为参考物，一部分 index 上放 secrets（例如可以放在最前面的 index，这部分不会被分发出去！），另外的 index 上放冗余的秘密编码信息（这部分分发出去！）
- $C$ 是秘密分享的编码空间，$C\subset K^m$，假定其维度为 $n$
- $I$ 表示选定的 index 集合 $I=[m]$
- $\bf{x}=(x_i)_{i\in I}\in K^m$
- **索引限制映射** restriction：$\pi_A:\bf{x}\mapsto (x_i)_{i\in A}$
- 【Shares 的分布】关于 $C$，**称 $S$ 提供了 $S$-uniformity**（刻画常有的 shares 的**分布**性质）当且仅当 $\pi_S(C)=K^{|S|}$
  - 若把 $C$ 表示为矩阵，由某组基底表出，那么这些基底的索引限制映射在 $K^{|S|}$ 上满秩
- 【Recover 算法的存在】关于 $C$，**称 $A$ 索引确定了 $S$ 索引**（处理 SS 方案的**冗余**，例如 SS 方案当中的恢复 Recover 算法） ，有：$\exists\ f\ \forall\ \bf{c}\in C,s.t.\ (f\circ\pi_A)(\bf{c})=\pi_S(\bf{c})$
  - 用矩阵可以表示为 $\exists\ \bf{F}\ \forall\ \bf{x}\in \bbF_{|K|}^n:\bf{FAC}\cdot \bf{x}=\bf{SC}\cdot \bf{x}$ 
  - 即有 $(\bf{FA-S})\cdot \bf{C}=0$，其含义是可以找到投影算子 $\bf{F}$，使得任意向量 $\bf{x}\in \bbF_{|K|}^m$ 有在 $\bf{FA}$ 和 $\bf{S}$ 二者上的投影在 $\bf{C}^\perp$ 的**同一个**陪集上
- 【Privacy 的保证】关于 $C$，**称 $A$ 索引和 $S$ 索引独立**（刻画两部分的 shares 不相互影响，即 privacy 性质），有：$\pi_{A,S}(\bf{c})=(\pi_A(\bf{c}),\pi_S(\bf{c}))$ 可以**跑遍** $\pi_A(C)\times \pi_S(C)$ 
  - 直觉是由于 $\pi_{A,S}$ 映射是 regular 的，对于任意一个投影 $\pi_A(\bf{c})$ 都**不会影响**$\pi_S(\bf{c})$上的值
  - 矩阵角度：$(\bf{AC})^\perp$ 包含 $\bf{SC}$ 组成的向量空间，即存在 $\bf{F}$, s.t. $\bf{F}\cdot (\bf{AC})^\perp = \bf{SC}$
- 【编码算法的特殊“转移”性质】关于 $C$，**称 $g$ 编码函数为 $S$-generator**，当且仅当：
  - 编码算法：$g:K^{|S|+e}\rightarrow C$ 为满射，即 $K^{|S|+e}$ 大于等于 $C$ 的维度，**刻画LSSS的编码算法**（此处 $e$ 是为了放置随机数隐藏秘密s）
  - $S$ 拥有 $S$-uniformity （被下面的“编码转移特点”蕴涵？有了这个条件也能设计 $g$ 满足“编码转移特点”）
  - 编码转移特点：$\pi_{[|S|]}=\pi_S\circ g$，此处可以看作秘密的编码 $g$ 的特点，$K^{|S|+e}$ 中前 $|S|$ 的秘密会迁移到编码后 $C$ 的索引集合 $S$ 上
  - $g$ 编码函数的存在性：
    - 关于 $C$, $S$ 提供 $S$-uniformity
    - $|S|+e\ge \dim(C)$

基于上述的线性代数描述的术语，我们下面定义 LSSS 方案：

- $S\subset I$, $S^*=I\backslash S$; $S^*$ 上存放分发的分片，被称为**玩家索引集**，而 $S$ 上放上秘密和不会分发出去的分片，被称为**秘密索引集**，$\pi_j(C)$ 被称为第 $j$ 个玩家的 share 份额（若 $j\in S^*$）
- $(C,S)$-LSSS 是指：关于 $C$，有 $S$-uniformity，以及 $S^*$ 决定 $S$ （即 $|S^*|\ge \dim(C)$）
  - 我们关心的 $(C,S)$-LSSS generator 是针对 $C$ 的 $S$-generator
  - 产生 shares 的过程：选择 $K^{|S|+e}$ 的前 $|S|$ 位置作为**秘密** $\bf{s}$，再随机填充剩下的 $e$ 个位置作为噪声（防止能直接通过 $C$ 的少数个位置的值就可以直接学习到 $\bf{s}$），得到 $\rho_\bf{s}$，得到 $\bf{c}=g(\rho_\bf{s})\in C$，分配 $\pi_{S^*}(\bf{c})$ 给诸位玩家
- $A$-privacy: $A\subset S^*$ 且关于 $C$，$A$ 索引上的份额和 $S$ 索引上的份额相互独立，即 $A$ 索引集为一个 unqualified set
  - 若对任意 $|A|=t$ 的 $A$ 都有 $A$-privacy，则称为 $t$-privacy
- $A$-reconstruction: $A$ 决定 $S$，即 $A$ 索引集为一个 qualified set
  - 若对任意 $|A|=r$ 的 $A$ 都有 $A$-reconstruction，则称为 $r$-privacy

- 容易验证，对于 LSSS 而言，都具有上述的 threshold 性质

Schur-Product Transform:
$$
ST(C):=\left\{\forall\ m\in\N:\ \sum_{i=1}^ma_i\cdot (\bf{x}_i*\bf{y}_i) \mid \bf{x}_i,\ \bf{y}_i\in C,\ a_i\in \N \right\}
$$
显然经过该乘积变换后，维数不减；此时 $|S^*|\le \dim(C)$ 可能并不一定成立，如果仍然成立，我们可有找到 $\hat{r}$-product reconstruction

Sweeping vectors: 如果我们想要找到 $C$ 上 $S$ 索引集上取值为 $(x_1,\cdots,x_{|S|})$ 且unqualified set $A$ 中对应的份额都与分享秘密0的份额一样

- 找到 $\pi_{A,S}(\bf{c}_{A,j})=(\bf{0},e_j)$ 及其在 $g$ 下的原像 $\bf{w}_{A,j}$
- 选择 $\rho_\bf{0}$ 的前 $|S|$ 位为 $0$

$$
\rho_\bf{0}+\sum_{j=1}^{|S|}x_j\cdot \bf{w}_{A,j}
$$

## 3 主协议：批量乘法验证

主协议本质的想法，是利用承诺的**同态性**，$\underline{将验证 \bf{x}*\bf{y}=\bf{z} 转化为验证 \enc(\bf{x,r_x})* \enc(\bf{y,r_y})=\enc(\bf{z,r_z})}$，由于有“编码平移性”，所以可以保证 soundness：

- 若没有 $\bf{x}*\bf{y}=\bf{z}$，则对于任意的 $\bf{r_x},\bf{r_y}$ 都找不到 $\bf{r_z}$，使得上述 Encode 的式子成立，那么恶意 prover 无法蒙骗过关，因为 Encode 本身的纠错特性
- 另外一方面，我们也可以注意到 $\bf{r_{x,y,z}}$ 的加入可以方便地实现 ZK
- Note：事实上，整个 zksnark 中的 PIOP 构造就是关于纠错码的故事；例如上述的编码如果为 RS code，是不是 $\vcom{x}$ 就是最为简单的多项式承诺，即把特定的 evaluation represnetation 承诺起来？

在上述的指导思想下，主协议的设计是简单的：

- NP Relation = $\{(\vcom{x},\vcom{y},\vcom{z};\bf{x,y,z})\mid \vcom{x},\vcom{y},\vcom{z}~\mbox{open to}~\bf{x,y,z}\and \bf{x}*\bf{y}=\bf{z}\}$
- pp 当中包含 $M,\hat{M}$
-  Step 1: Prover 发送 $\vcom{r_x},\vcom{r_y},\vcom{r_z}$
- Step 2: Verifier 选择 Encode 后随机的索引集 $O\subset S^*$ 打开（注意为了保证 ZK，此处 $O$ 需要为 unqualified set，这和 CDS94 的思路一致）
- Step 3: Prover 打开，Verifier 验证：
  - 打开是否正确
  - 对应的打开是否满足乘法关系

<img src=".\Protocol 1.png" alt="Protocol 1" style="zoom:40%;" />

小问题：$\hat{M}$ 从算法的角度来说，应该如何选择？

我们假定 $g$ 的像空间的一组基底为 $\bf{m}_1,\cdots,\bf{m}_k$
$$
\left(\sum_{i=1}^k a_i\cdot \bf{w}_i\right)*\left(\sum_{i=1}^k b_i\cdot \bf{w}_i\right)
$$
从而我们只需要选择 $(\bf{w}_1,\cdots,\bf{w}_k)\otimes (\bf{w}_1,\cdots,\bf{w}_k)$ 的一组基即可

---

主定理：若使用上述的信息论承诺，则上述算法是完美零知识的，且如果存在 $i,x_iy_i\not= z_i$，能通过的上述协议的概率最多为：
$$
((\hat{r}-1)/d)^t+1/|L|
$$
ZK 分析：

- 由于 perfect hiding 性质的存在，我们可以将 $\vcom{x,r_x}$ 解释为 $\vcom{r_1}$，类似地解释其他的，然后保证乘积关系
- 利用 LSSS 的 Privacy 性质可以证明对应的分布完全相同

Soundness 分析（**此处的分析比起常用的 soundness 性质要弱！**此处直接假定了 $\vcom{x},\vcom{y},\vcom{z}$ 直接对应到 $\bf{x,y,z}$）：

- 根据纠错码的性质，我们知道最多有 $\hat{r}-1$ 个相同，能在 $((\hat{r}-1)/d)^t$ 概率内逃过检查
- 或者能够采用新的打开方式（打破 binding）
- 对上述使用 Union Bound

关于 Soundness 的讨论，由于本文的 NP Relation 带有预处理，可能需要定义为如下：
$$
\left\{(\bf{c}_1,\bf{c}_2,\bf{c}_3;\bf{x},\bf{y},\bf{z})\mid R_{pp_c}(\bf{c}_1,\bf{c}_2,\bf{c}_3;\bf{x},\bf{y},\bf{z})=1\right\}
$$

- 这里 statement 是 $(\bf{c}_1,\bf{c}_2,\bf{c}_3;\bf{x},\bf{y},\bf{z})$
- $(pp_c,pp_r)\leftarrow \mathsf{Setup}(1^\kappa)$ 是隐私的只有 prover (comitter)、verifier (receiver) 拿到的预处理参数
- $R_{pp_c}$ 算法即为利用 $pp_c$ 进行打开并检验 $\bf{x}*\bf{y}=\bf{z}$，注意到这里是完美 binding

则此处 soundness 定义和一般的 ZKP 不同，考虑一种带有预处理的 soundness：
$$
\Pr[(pp_c,pp_r)\leftarrow \mathsf{Setup}(1^\kappa),view_V\leftarrow \braket{ \mathcal{A}(pp_c),\mathcal{V}(1^\kappa,pp_r)}:R_{pp_c}(\bf{c}_1,\bf{c}_2,\bf{c}_3,\bf{x},\bf{y},\bf{z})=0\and \mathsf{Verify}_{pp_r}(view_V)=1]\le \mathsf{negl}(1^\kappa)
$$

---

接下来，再讨论一点和协议相关的问题：

- $O$ 有两种表示方法：一种是直接表示 $O$ 中的数字，第二种是使用 bitmap

- LSSS 的参数设计：通信复杂度显然是 $\Theta(\kappa_c(e+\hat{e})+\kappa_ot+d)$

  - 假定我们想要达到 $2^{-u}$ 的安全性，同时能保证 
    $$
    e,\hat{e}=O(u),\hat{r}=O(l+u),t=\Theta(u),d=O(l+u),(\hat{r}-1)/d=1/2
    $$

  - 从而可以实现均摊通信复杂性 $O(\frac{u}{l}(\kappa_c+\kappa_o))$, 再注意到之前的信息论承诺方案有 $\kappa_c=O(1),\kappa_o=O(u)$，那么，只要 $l>u^2$，则均摊复杂性可以达到 $O(1)$

  - 一个具体的例子：考虑一个 packed shamir sharing，参数选择如下

    - 求值集合 $\{q_1,\cdots,q_l,p_1,\cdots,p_t,\cdots,p_d\}$
    - $2(t+l-1)<d$
    - 从而为 $l$-multi-secret $K$-linear SS of length $d$, with $t$-privacy, $(2t+2l-1)$-reconstruction
    - 具体参数选择：$u=l,t=l,d=8l,|K|>9l,e=2l,\hat e=4l-1$，此处唯一无法实现的是 $\kappa_c=O(1)$，即我们需要思考如何在常数大小的域上进行选择
    - 但是如果我们感兴趣的命题是在小域 $K_0\subset K$ 上的，而我秘密分享方案也是在 $K$ 上的，$[K:K_0]=\mu$，那可以利用添加位置以坐标进行模拟（可以验证仍然可以进行对应的矩阵计算）

  - 更优的参数选择：

    - 此处需要 Algebraic Function Field 理论，可以达到上述期望的参数

- 应用到电路验证问题上：直接对线路进行承诺，然后利用此具有 amortization 的协议

## 4 协议扩展

本质的想法：

- 将电路中输入和输出之间满足关系进行批量验证。对输入和输出进行编码，编码后原来输入上的一些微小改变在编码后都被放大了，验证者对编码后的值进行随机挑战，若输入和输出不满足特定的关系，则验证者可以以很大的概率捕捉到证明者的谎言。

协议简单描述：

- 与批量乘法协议基本一样，只是将原来要验证的关系 $\mathbf{x*y=z}$ 拓展到更一般的关系 $D(\mathbf{x_{1},...,x_{v}} )$

<img src=".\Protocol 2.png" alt="Protocol 2" style="zoom:40%;" />

开销：

- 若电路的乘法深度为 $\delta$,电路的输入个数为 $v$ ,若保证错误概率为 $2^{-l}$,则摊销复杂度为 $O(2^{\delta}\kappa+v\kappa+\delta logl)$

两个变体：

- 乘法门：对电路 $D$ 中的每个乘法门 $T$,利用 Verify Multiplication protocol进行验证

  - 对乘法门 $T$ 的输入 $\mathbf x_{T}、\mathbf y_{T}$ 和输出 $\mathbf z_{T}$ 进行承诺，利用 Verify Multiplication protocol进行验证 $\mathbf{x_{T}*y_{T}=z_{T}}$

  - 由于承诺具有**同态性**，在电路 $D$ 中的线性操作可以由验证者自己验证。

    开销：$O(\mu\kappa+v\kappa)$,其中 $\mu$ 是电路中乘法门的数量。

    参数选择：当 $\delta=O(logv)$或者 $\delta=O(v)$，且 $\mu> 2^{\delta}$ 时，使用 Verify Circuit protocol开销更低

- 结合 MPC-in-the-Head：

  - **Purpose：**在 Verify Circuit Protocol中，由于 $\tilde e=2^{\delta}n+1-l$,导致 $\tilde r _{z}=(r_{1},...,r_{\tilde e})$ 长度比较长，因此利用MPC-in the head的方法， 证明者不直接发送 $[\tilde r _{z}]$,而发送需要的 $[(\tilde c _{z})_{i}]$

  ![image-20250314191725555](CDP11笔记.assets/image-20250314191725555.png)

  ![image-20250314191339788](CDP11笔记.assets/image-20250314191339788.png)

  - 开销：使用MPC-in the head后，验证电路的协议中 $O(\tilde e\kappa_{c})$部分的开销变为 $O((at+a)\kappa_{c})$

## 5 整数上的补正

本质的想法：

- 将秘密$s_{1},...,s_{l}$和随机数$r_{1},...,r_{t}$看作在固定集合上 $K,|K|=l+t$上的求值，从而确定一个次数小于等于$l+t-1$的多项式，利用多项式在 $\mathbb Z \setminus K$中的求值得到秘密份额（可以看作$s_{1},...,s_{l}$编码后得到的值），验证者选择的挑战$|O|\le T$，不会泄露关于秘密的任何信息，而且由于LSS的重构性质，保证了若份额之间满足关系${\enc(\bf{x,r_x})* \enc(\bf{y,r_y})=\enc(\bf{z,r_z})}$,那么秘密之间以很大的概率满足 $\mathbf {x*y=z}$。

协议的简单描述：

- LSSS
  - 若使用类似于域上的packed secret sharing scheme，则多项式的系数中可能会出现分数，无法使用整数承诺，因此需要在通过拉格朗日插值后得到的多项式前面乘以 $\Delta$,使其变成整系数多项式。

![image-20250321213613083](CDP11笔记.assets/image-20250321213613083.png)

- Protocol

<img src=".\Protocol 3.png" alt="Protocol 3" style="zoom:55%;" />









