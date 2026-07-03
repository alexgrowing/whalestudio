# MyProject — 一个简单的 Lean 4 示例项目

## 项目结构

```
lean_project/
├── lakefile.lean          # 构建配置（Lake 构建系统）
├── lean-toolchain         # 指定 Lean 版本
├── Main.lean              # 程序入口
└── MyProject/
    ├── Basic.lean         # 核心函数定义
    └── Theorems.lean      # 定理与形式化证明
```

## 包含内容

### 函数（`Basic.lean`）
| 函数 | 说明 |
|------|------|
| `double n` | 将自然数翻倍 |
| `factorial n` | 阶乘（递归定义） |
| `fibonacci n` | 斐波那契数列 |
| `isEven n` | 判断偶数 |
| `myMax a b` | 两数取最大值 |

### 定理（`Theorems.lean`）
| 定理 | 说明 |
|------|------|
| `double_eq_add` | `double n = n + n` |
| `zero_isEven` | 0 是偶数 |
| `even_add_two` | 偶数 +2 仍是偶数 |
| `double_mono` | double 保持单调性 |
| `factorial_pos` | 阶乘恒正 |
| `myMax_comm` | myMax 满足交换律 |

## 快速上手

### 安装 Lean 4 / elan

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
```

### 构建并运行

```bash
cd lean_project
lake build
lake exe myproject
```

### 仅检查证明（不运行）

```bash
lake build MyProject
```

## 学习资源

- [Lean 4 官方文档](https://leanprover.github.io/lean4/doc/)
- [Lean 4 定理证明教程](https://leanprover.github.io/theorem_proving_in_lean4/)
- [Mathlib4](https://leanprover-community.github.io/mathlib4_docs/)
