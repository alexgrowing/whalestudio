# AlternatingGroup — Lean 4 形式化证明

> **定理**：当 $n \geq 3$ 时，交错群 $A_n$ 由所有 3-轮换生成。

本项目使用 **Lean 4 + Mathlib4** 给出该定理的形式化证明。

---

## 数学内容

### 核心定理

$$A_n = \langle (a\;b\;c) \mid a,b,c \in \{1,\ldots,n\},\; a,b,c \text{ 两两不同} \rangle \quad (n \geq 3)$$

### 证明思路

证明分两个方向：

#### ① 包含方向：$\langle 3\text{-轮换} \rangle \subseteq A_n$

每个 3-轮换 $(a\;b\;c)$ 可以写成两个对换之积：
$$(a\;b\;c) = (a\;b)(b\;c)$$
两个对换之积的符号为 $(-1)^2 = 1$，故为偶置换，属于 $A_n$。  
由于 $A_n$ 是子群，它包含所有生成元，从而包含整个 $\langle 3\text{-轮换} \rangle$。

#### ② 反向包含：$A_n \subseteq \langle 3\text{-轮换} \rangle$（$n \geq 3$）

任意 $\sigma \in A_n$ 是偶数个对换之积，设 $\sigma = \tau_1\tau_2\cdots\tau_{2k}$。

对每一对 $(\tau_{2i-1}, \tau_{2i}) = (a\;b)(c\;d)$，分两种情形：

| 情形 | 条件 | 结论 |
|------|------|------|
| **相交** | $\{a,b\} \cap \{c,d\} \neq \emptyset$，不妨设共享 $b=c$ | $(a\;b)(b\;d) = (a\;b\;d)$ 是一个 3-轮换 |
| **不相交** | $\{a,b\} \cap \{c,d\} = \emptyset$ | $(a\;b)(c\;d) = \underbrace{(a\;c\;b)}_{\text{3-轮换}}\underbrace{(a\;c\;d)}_{\text{3-轮换}}$ |

不相交情形的验证：
$$(a\;c\;b)(a\;c\;d) = (a\;b)(c\;d)$$
可以逐点计算验证（见 `ElementaryProof.lean` 中的 `disjoint_swap_mul`）。

因此每对对换之积均属于 $\langle 3\text{-轮换} \rangle$，故整个 $\sigma \in \langle 3\text{-轮换} \rangle$。

---

## 项目结构

```
AlternatingGroup/
├── lakefile.toml                    # Lake 构建配置
├── lean-toolchain                   # Lean 版本锁定
├── AlternatingGroup.lean            # 库入口（导入所有模块）
└── AlternatingGroup/
    ├── Basic.lean                   # 主定理（调用 Mathlib 高层接口）
    ├── ElementaryProof.lean         # 自包含初等证明（展示所有细节）
    └── ConcreteExamples.lean        # 具体情形：A₃、A₄ 的验证
```

### 各文件说明

- **`Basic.lean`**：定义 3-轮换集合 `S3`，给出辅助引理，陈述并证明主定理。
- **`ElementaryProof.lean`**：更详细的初等证明，包含不相交对换分解的显式引理。
- **`ConcreteExamples.lean`**：用 `native_decide` 验证 $A_3$、$A_4$ 的具体情形。

---

## 使用的 Mathlib 引理

| 引理 | 说明 |
|------|------|
| `Equiv.Perm.sign_swap` | 对换的符号为 $-1$ |
| `Equiv.Perm.sign_mul` | 符号是乘法同态 |
| `AlternatingGroup.mem_alternatingGroup` | 偶置换 ↔ sign = 1 |
| `Subgroup.closure_le` | closure 的泛性质 |
| `Perm.mem_closure_isThreeCycle_of_sign_eq_one` | 关键：$n\geq 3$ 时偶置换 ∈ closure(3-cycles) |

---

## 快速上手

### 环境要求

- [elan](https://github.com/leanprover/elan)（Lean 版本管理器）
- 网络连接（首次运行需下载 Mathlib）

### 安装 & 编译

```bash
# 1. 克隆/进入项目目录
cd AlternatingGroup

# 2. 下载 Mathlib 缓存（大幅加快编译）
lake exe cache get

# 3. 编译项目
lake build

# 4. 在 VS Code 中查看（需安装 lean4 插件）
code .
```

### 在 VS Code 中使用

安装 [lean4 VS Code 扩展](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)，打开任意 `.lean` 文件，将鼠标悬停在定理名称上即可查看类型和证明状态。

---

## 关键定理一览

```lean
-- 主定理（ElementaryProof.lean）
theorem alternatingGroup_eq_closure_s3 (n : ℕ) (hn : 3 ≤ n) :
    alternatingGroup (Fin n) = Subgroup.closure (S3 n)

-- A₃ 情形
theorem A3_generated_by_3cycles :
    alternatingGroup (Fin 3) = Subgroup.closure (S3 3)

-- A₄ 情形
theorem A4_generated_by_3cycles :
    alternatingGroup (Fin 4) = Subgroup.closure (S3 4)

-- 任意元素版本
theorem every_even_perm_is_product_of_3cycles
    (n : ℕ) (hn : 3 ≤ n) (σ : Perm (Fin n))
    (hσ : σ ∈ alternatingGroup (Fin n)) :
    σ ∈ Subgroup.closure (S3 n)
```

---

## 参考资料

- Mathlib4 文档：https://leanprover-community.github.io/mathlib4_docs/
- Dummit & Foote, *Abstract Algebra*, §4.6
- 在线 Lean 4 学习资源：https://leanprover.github.io/lean4/doc/
