import Mathlib

set_option linter.style.emptyLine false

/-!
每种语法结构如何使用与证明
-/

-- 存在量词在条件中
-- 存在量词在结论中
-- 全称量词在条件中
-- 全称量词在结论中

example (x : U) (A B : Set U) (h1 : A ⊆ B) (h2 : x ∈ A) : x ∈ B := by
-- A ⊆ B本质上就是∀x ∈ A, x ∈ B，也就是∀x, x ∈ A → x ∈ B
  exact h1 h2

example (x : U) (A B C : Set U) (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : x ∈ A) : x ∈ C := by
-- h1 h3得到 x ∈ B，则h2 (h1 h3)就是 x ∈ C
  exact h2 (h1 h3)

example {x : U} {A B C : Set U} (h1 : A ⊆ B) (h2 : x ∈ B → x ∈ C) : x ∈ A → x ∈ C := by
-- 要证明的结论是 → 的结构，用intro可以把 → 前面的 x ∈ A拿出来作为该证明的条件，只需要证明 x ∈ C
  intro h
  exact h2 (h1 h)

example (A : Set U) : A ⊆ A := by
-- A ⊆ A本质上就是∀x, x ∈ A → x ∈ A，由于intro是提取 → 前面的内容作为条件
-- 因此有与前一条（只有一个Object）不同，此处的intro伴随两个Object
  intro x hx
  exact hx

example {A B : Set U} {x : U} (h1 : x ∈ A) (h2 : x ∉ B) : ¬A ⊆ B := by
-- ¬A ⊆ B本质上就是A ⊆ B → False，因此使用intro hAB后，条件中多了A ⊆ B，结论变成了False
  intro hAB
-- x ∉ B本质就是x ∈ B → False，因此通过hAB h1得到x ∈ B后，h2作用上去就得到了False
  exact h2 (hAB h1)

-- 这是上一题另一种证明方法
example {A B : Set U} {x : U} (h1 : x ∈ A) (h2 : x ∉ B) : ¬A ⊆ B := by
  intro hAB
-- 此处执行apply h2后，要证明的结论从False变成了x ∈ B，参见diff_between_apply_and_exact
  apply h2
  exact hAB h1

example (A : Set U) (x : U) : x ∈ Aᶜ ↔ x ∉ A := by
-- ↔ 两侧的形式虽然不同，但仍然可以用rfl，除了这个例子，还有
-- x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B
-- x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B
-- A ⊆ B ↔ ∀x, x ∈ A → x ∈ B
  rfl

example {A B : Set U} (h1 : A ⊆ B) : Bᶜ ⊆ Aᶜ := by
-- 此处的intro其实是把两个步骤合并了
-- 首先intro x hb增加前提 x ∈ Bᶜ，结论为 x ∈ Aᶜ
-- 再次intro ha增加前提 x ∈ Aᶜ，结论为 False
  intro x hb ha
  exact hb (h1 ha)

example (A : Set U) : Aᶜᶜ = A := by
-- 当要证明两个集合相等 A = B，ext x会引入任意的x，将结论转变为x ∈ A ↔ x ∈ B
  ext x
-- 当要证明的结论是P ↔ Q时，constructor将结论转变成两个目标P → Q和P ← Q
-- 当要证明的结论是P ∧ Q时，constructor将结论转变成两个目标P和Q
  constructor
  · intro hx
    by_contra h
    exact hx h
  · intro hx
-- 此时要证明的是 x ∈ Aᶜᶜ，也就是 x ∈ Aᶜ → False
-- 也就是要证明的结论是一个函数，接受一个参数值为x ∈ Aᶜ，返回为False
-- 下面的方法正是构造出了这么一个函数
    exact fun h => h hx

example (A B : Set U) : A ⊆ B ↔ Bᶜ ⊆ Aᶜ := by
  constructor
  · intro h x hxB hxA
    exact hxB (h hxA)
  · intro h x hA
-- 通过by_contra hB得到x ∉ B就等价于x ∈ Bᶜ，就可以直接被Bᶜ ⊆ Aᶜ作用了
    by_contra hB
    exact h hB hA

example (x : U) (A B : Set U) (h : x ∈ A ∧ x ∈ B) : x ∈ A := by
-- 可以直接取某个前提中的一部分
  exact h.left

example (x : U) (A B : Set U) (h : x ∈ A ∩ B) : x ∈ B := by
-- 由于x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B，所以就可以直接取h.right
  exact h.right

example (x : U) (A B C : Set U) (h : x ∈ A ∩ B ∩ C) : x ∈ B := by
-- 除了用left和right，也还可以用1,2来表示，等价于(h.left).right
  exact (h.1).2

example (x : U) (A B : Set U) (h1 : x ∈ A) (h2 : x ∈ B) : x ∈ A ∩ B := by
-- 可以先用constructor分拆成 x ∈ A 和 x ∈ B，然后分别证明
-- 也可以直接用exact And.intro h1 h2
-- 更简洁一些就是exact ⟨h1, h2⟩ TODO 好像还有其它地方也是用⟨⟩，这个符号表示的一般意义是什么
  exact ⟨h1, h2⟩

example (A B C : Set U) (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ B ∩ C := by
  intro x h
  exact ⟨h1 h, h2 h⟩

example (A B C : Set U) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  ext x
  constructor
  · intro h
-- ⟨h.1.1, h.1.2, h.2⟩会自动解析成⟨h.1.1, ⟨h.1.2, h.2⟩⟩
    exact ⟨h.1.1, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨h.1, h.2.1⟩,h.2.2⟩

example (x : U) (A B : Set U) (h : x ∈ A) : x ∈ A ∨ x ∈ B := by
-- 可以先left再exact h，也可以简洁地写成exact Or.inl h
  exact Or.inl h

example (A B C : Set U) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  ext x
  constructor
  · intro h
    rcases h with (hA | hB) | hC
    · exact Or.inl hA
-- 已知hB : x ∈ B，居然还能这么证明 x ∈ A ∪ (B ∪ C)
    · exact Or.inr (Or.inl hB)
    · exact Or.inr (Or.inr hC)
  · intro h
    rcases h with hA | (hB | hC)
    · exact Or.inl (Or.inl hA)
    · exact Or.inl (Or.inr hB)
    · exact Or.inr hC

example (A B : Set U) : (A ∪ B)ᶜ = Aᶜ ∩ Bᶜ := by
  ext x
  constructor
  · intro h
    constructor
    · intro ha
-- 这也是没想到，此处也可以直接通过Or.inl ha将x ∈ A转换成x ∈ A ∪ B
      exact h (Or.inl ha)
    · intro hb
      exact h (Or.inr hb)
  · intro h hAB
    rcases hAB with hA | hB
    · exact h.left hA
    · exact h.right hB

-- 下面三个命题的证明，熟练使用rcases和对于结论 ∧ 和 ∨ 的exact
section
example (A B C : Set U) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by
  ext x
  constructor
  · intro h
    rcases h with ⟨hA, (hB | hC)⟩
    · exact Or.inl ⟨hA, hB⟩
    · exact Or.inr ⟨hA, hC⟩
  · intro h
    rcases h with ⟨hA, hB⟩ | ⟨hA, hC⟩
    · exact ⟨hA, Or.inl hB⟩
    · exact ⟨hA, Or.inr hC⟩

example (A B C : Set U) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  ext x
  constructor
  · intro h
    rcases h with hA | ⟨hB, hC⟩
    · exact ⟨Or.inl hA, Or.inl hA⟩
    · exact ⟨Or.inr hB, Or.inr hC⟩
  · intro h
    rcases h with ⟨hA1 | hB, hA2 | hC⟩
    · exact Or.inl hA1
    · exact Or.inl hA1
    · exact Or.inl hA2
    · exact Or.inr ⟨hB, hC⟩

example (A B C : Set U) (h1 : A ∪ C ⊆ B ∪ C) (h2 : A ∩ C ⊆ B ∩ C) : A ⊆ B := by
  intro x h
  rcases h1 (Or.inl h) with hB | hC
  · exact hB
  · exact (h2 ⟨h, hC⟩).left
end


example (F G : Set (Set U)) (h1 : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := by
  intro x h
  rw[Set.mem_sInter] at h ⊢
  intro S hS
  exact h S (h1 hS)

example (F G : Set (Set U)) (h1 : F ⊆ G) : ⋂₀ G ⊆ ⋂₀ F := by
-- x ∈ ⋂₀F ↔ ∀S, S ∈ F → x ∈ S，因此对于目标⋂₀G ⊆ ⋂₀F，可以连续intro x h S hS
  intro x h S hS
-- 同样在证明结论时，由于h : x ∈ ⋂₀G ↔ ∀S, S ∈ G → x ∈ S，不需要先rw[Set.mem_sInter]就可以直接调用
  exact h S (h1 hS)

example (A B : Set U) : A ∩ B = ⋂₀ {A, B} := by
  ext x
  constructor
  · intro ⟨hA, hB⟩ S hS
-- 把hS拆成 S = A 和 S = B，然后直接替换前提中的S
    rcases hS with rfl | rfl
    · exact hA
    · exact hB
  · intro hx
    constructor
-- 这里rfl的用法也是神妙啊
    · exact hx A (Or.inl rfl)
    · exact hx B (Or.inr rfl)

-- 用intro把结论中的前提一层一层扒出来，用exact一层一层推导下去
example (A : Set U) (F : Set (Set U)) : A ⊆ ⋂₀ F ↔ ∀ s ∈ F, A ⊆ s := by
  constructor
  · intro h S hS x hx
    exact h hx S hS
  · intro h x hx S hS
    exact h S hS hx

example (A : Set U) (F G : Set (Set U)) (h1 : ∀ s ∈ F, A ∪ s ∈ G) : ⋂₀ G ⊆ A ∪ (⋂₀ F) := by
  intro x h
-- by_cases的使用
  by_cases  hA : x ∈ A
  · exact Or.inl hA
  · right
    intro S hS
    have _h : x ∈ A ∪ S := (h (A ∪ S) (h1 S hS))
    rcases _h with hxA | hxS
-- 前提中如果有两项矛盾，用False.elim直接推出结论
    · exact False.elim (hA hxA)
    · exact hxS

example (A : Set U) (F : Set (Set U)) (h1 : A ∈ F) : A ⊆ ⋃₀ F := by
  intro x hx
-- 证明存在性命题，用exact，其中的每个参数分别是存在的对象，以及对应的每个 ∧ 的条件
  exact ⟨A, h1, hx⟩

example (F G : Set (Set U)) (h1 : F ⊆ G) : ⋃₀ F ⊆ ⋃₀ G := by
  intro x hx
  rcases hx with ⟨S, ⟨hSF, hxS⟩⟩
  exact ⟨S, (h1 hSF), hxS⟩

example (A B : Set U) : A ∪ B = ⋃₀ {A, B} := by
  ext x
  constructor
  · intro hx
    have hA : A ∈ ({A, B} : Set (Set U)) := by
      left
      rfl
    have hB : B ∈ ({A, B} : Set (Set U)) := by
      right
      rfl
    rcases hx with hxA | hxB
-- 下面用到的 hA 和 hB 也可以直接 by simp，不需要在前面证明
    · exact ⟨A, hA, hxA⟩
    · exact ⟨B, hB, hxB⟩
  · intro hx
    rcases hx with ⟨S, rfl | rfl, hxS⟩
    · exact Or.inl hxS
    · exact Or.inr hxS

example (F G : Set (Set U)) : ⋃₀ (F ∪ G) = (⋃₀ F) ∪ (⋃₀ G) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨S, hSF | hSG, hxS⟩
    · exact Or.inl ⟨S, hSF, hxS⟩
    · exact Or.inr ⟨S, hSG, hxS⟩
  · intro hx
    rcases hx with ⟨S, hSF, hxS⟩ | ⟨S, hSG, hxS⟩
-- exact里面需要用的命题，也可以直接用Or.inl，挺好
    · exact ⟨S, Or.inl hSF, hxS⟩
    · exact ⟨S, Or.inr hSG, hxS⟩

example (A : Set U) (F : Set (Set U)) : ⋃₀ F ⊆ A ↔ ∀ s ∈ F, s ⊆ A := by
  constructor
  · intro h S hSF x hx
-- 其中⟨S, hSF, hx⟩ 就是 x ∈ ⋃₀F
    exact h ⟨S, hSF, hx⟩
  · intro h x ⟨S, hSF, hxS⟩
    exact (h S hSF) hxS


example (A : Set U) (F : Set (Set U)) : A ∩ (⋃₀ F) = ⋃₀ {s | ∃ u ∈ F, s = A ∩ u} := by
  ext x
  constructor
  · intro h
    rcases h with ⟨hA, hxF⟩
    rcases hxF with ⟨S, hSF, hxS⟩
    -- 下面两段可以合并到一个exact里面去
    -- use A ∩ S
    -- exact ⟨⟨S, hSF, rfl⟩, ⟨hA, hxS⟩⟩
    exact ⟨A ∩ S, ⟨S, hSF, rfl⟩, ⟨hA, hxS⟩⟩
  · intro h
    rcases h with ⟨S, hS, hxS⟩
    rcases hS with ⟨Su, hSu, rfl⟩
    refine ⟨hxS.left, ⟨Su, hSu, hxS.right⟩⟩

example (F : Set (Set U)) : (⋃₀ F)ᶜ = ⋂₀ {s | sᶜ ∈ F} := by
  ext x
  constructor
  · intro h S hS
    by_contra hxS
    -- rw[Set.mem_setOf] at hS
    -- have _h : x ∈ ⋃₀F := by
    --   exact ⟨Sᶜ, hS, hxS⟩
    -- exact h _h
    -- 上面那几行，可以简写成下面这一行，x ∈ ⋃₀F := ⟨Sᶜ, hS, hxS⟩，绝了
    exact h ⟨Sᶜ, hS, hxS⟩
  · intro h hx
    rcases hx with ⟨S, hS, hxS⟩
    have _h : Sᶜ ∈ {s | sᶜ ∈ F} := by
      rw[Set.mem_setOf, compl_compl]
      exact hS
    have h1 := h Sᶜ _h
    exact h1 hxS

example (F : Set (Set U)) : (⋂₀ F)ᶜ = ⋃₀ {s | sᶜ ∈ F} := by
  ext x
  constructor
  · intro h
    rw[Set.mem_compl_iff, Set.mem_sInter] at h
    push Not at h
    rcases h with ⟨S, hS, hxS⟩
    rw[← compl_compl S] at hS
    exact ⟨Sᶜ, hS, hxS⟩
  · intro h hx
    rcases h with ⟨S, hS, hxS⟩
    exact hx Sᶜ hS hxS

example (F G : Set (Set U)) (h1 : ∀ s ∈ F, ∃ t ∈ G, s ⊆ t) (h2 : ∃ s ∈ F, ∀ t ∈ G, t ⊆ s)
  : ∃ u, u ∈ F ∩ G := by
  rcases h2 with ⟨S, hSF, _h2⟩
  rcases h1 S hSF with ⟨S1, hS1G, hSS1⟩
  have hS1S := _h2 S1 hS1G
  have _eq := HasSubset.Subset.antisymm hSS1 hS1S
  rw[_eq] at hSF
  exact ⟨S1, ⟨hSF, hS1G⟩⟩

example (F G H : Set (Set U)) (h1 : ∀ s ∈ F, ∃ u ∈ G, s ∩ u ∈ H) : (⋃₀ F) ∩ (⋂₀ G) ⊆ ⋃₀ H := by
-- 其实可以用 rintro x ⟨⟨S, hSF, hxS⟩, hr⟩ 把下面两段合并起来
  intro x hx
  rcases hx with ⟨⟨S, hSF, hxS⟩, hr⟩
  rcases h1 S hSF with ⟨T, hTG, hST⟩
  exact ⟨S ∩ T, hST, ⟨hxS, (hr T hTG)⟩⟩

example (F G : Set (Set U)) : (⋃₀ F) ∩ (⋃₀ G)ᶜ ⊆ ⋃₀ (F ∩ Gᶜ) := by
  intro x hx
  rcases hx with ⟨⟨S, hSF, hxS⟩, hxGc⟩
  rw[Set.mem_compl_iff, Set.mem_sUnion] at hxGc
  push Not at hxGc
  refine ⟨S, ⟨hSF, ?_⟩, hxS⟩
-- S ∈ Gᶜ 就是 S ∈ G → False，通过intro把 S ∈ G 提取出来就能直接用到hxGc了，比我一开始考虑的要五步的方法顺
-- by_contra _hSGc
-- refine (hxGc S ?_) hxS
-- rw[Set.mem_compl_iff] at _hSGc
-- push Not at _hSGc
-- exact _hSGc
  intro hSG
  exact (hxGc S hSG) hxS


example (F G : Set (Set U)) (h1 : ⋃₀ (F ∩ Gᶜ) ⊆ (⋃₀ F) ∩ (⋃₀ G)ᶜ) : (⋃₀ F) ∩ (⋃₀ G) ⊆ ⋃₀ (F ∩ G)
:= by
  intro x hx
  rcases hx with ⟨⟨S, hSF, hxS⟩,⟨T, hTG, hxT⟩⟩
-- 原来的参考答案是 _h : S ⊆ ⋃₀(F ∩ Gᶜ)，挺复杂的，换成 S ∈ G 试试，而且感觉这样更自然一些
  by_cases _h : S ∈ G
  · exact ⟨S, ⟨hSF, _h⟩, hxS⟩
  · have h2 : S ∈ F ∩ Gᶜ := by exact ⟨hSF, _h⟩
    have h3 : x ∈ ⋃₀(F ∩ Gᶜ) := by exact ⟨S, h2, hxS⟩
    have h4 : x ∈ ⋃₀F ∩ (⋃₀G)ᶜ := by exact h1 h3
    have h4r := h4.right
    rw[Set.mem_compl_iff, Set.mem_sUnion] at h4r
    push Not at h4r
    exact False.elim (h4r T hTG hxT)

example (F G : Set (Set U)) : (⋃₀ F) ∩ (⋂₀ G)ᶜ ⊆ ⋃₀ {s | ∃ u ∈ F, ∃ v ∈ G, s = u ∩ vᶜ} := by
  intro x h
  rcases h with ⟨⟨S, hSF, hxS⟩, hr⟩
  rw[Set.mem_compl_iff, Set.mem_sInter] at hr
  push Not at hr
  rcases hr with ⟨T, hTG, hxT⟩
-- 这连续三个∃的嵌套，用refine命令一点一点展开，写起来比较顺
-- 经过判断，第一个 ∃ 应该是 S ∩ Tᶜ，因此先有
-- refine ⟨S ∩ Tᶜ, ?_, ?_⟩
-- 经查看，可知后面两个需要证明的分别是 S ∩ Tᶜ ∈ {s | ∃ u ∈ F, ∃ v ∈ G, s = u ∩ vᶜ} 和 x ∈ S ∩ Tᶜ
-- 显然第两个比较容易，先写上
-- refine ⟨S ∩ Tᶜ, ?_, ⟨hxS, hxT⟩⟩
-- 第一个也是一个 ∃ 命题，经判断，应该是 ∃ S，于是有
-- refine ⟨S ∩ Tᶜ, ⟨S, ?_, ?_⟩, ⟨hxS, hxT⟩⟩
-- 经查看，可知后面两个需要证明的分别是 S ∈ F 和 ∃ v ∈ G, S ∩ Tᶜ = S ∩ vᶜ
-- 先把第一个写上，于是有
-- refine ⟨S ∩ Tᶜ, ⟨S, hSF, ?_⟩, ⟨hxS, hxT⟩⟩
-- 另一个 ∃ 命题，应该是 ∃ T，于是有
-- refine ⟨S ∩ Tᶜ, ⟨S, hSF, ⟨T, ?_, ?_⟩⟩, ⟨hxS, hxT⟩⟩
-- 经查看，还需要证明 T ∈ G 和 S ∩ Tᶜ = S ∩ Tᶜ，于是得到最终答案
  refine ⟨S ∩ Tᶜ, ⟨S, hSF, ⟨T, hTG, rfl⟩⟩, ⟨hxS, hxT⟩⟩



section diff_between_apply_refine_and_exact
/-!
  exact表示“我已经有了完整证明，直接交出去“
  apply表示”我有一个定理，它的结论能匹配当前目标，于是可以转换当前目标，将这个定理的前提作为新的目标“
  refine是apply的升级版本
  -- exact h：h的类型必须正是当前goal，不留任何剩余义务
  -- exact h ?_ ?_：h的类型比当前goal多几个参数，可以用 ?_ 占位，Lean会把这些占位符当前新的goal让你继续证明
-/

example (x : U) (A B : Set U) (h : x ∈ A) : x ∈ A ∨ x ∈ B := by
  exact Or.inl h

example (x : U) (A B : Set U) (h : x ∈ A) : x ∈ A ∨ x ∈ B := by
  apply Or.inl
  exact h


example (A B C : Set U) (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ B ∩ C := by
  intro x h
  exact ⟨h1 h, h2 h⟩

example (A B C : Set U) (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ B ∩ C := by
  intro x h
  refine ⟨h1 ?_, h2 ?_⟩
  · exact h
  · exact h

end diff_between_apply_refine_and_exact


section diff_between_cases_and_rcases
/-!
  对比cases（Lean原生命令）与rcases（Mathlib提供的增强版模式匹配命令）
-/
-- 前提中对∨的分解
example (A B C : Set U) (h1 : A ⊆ C) (h2 : B ⊆ C) : A ∪ B ⊆ C := by
  intro x h
  cases h with
    |inl ha => exact h1 ha
    |inr hb => exact h2 hb

example (A B C : Set U) (h1 : A ⊆ C) (h2 : B ⊆ C) : A ∪ B ⊆ C := by
  intro x h
  rcases h with ha | hb
  · exact h1 ha
  · exact h2 hb

example (A B C : Set U) (h1 : A ⊆ C) (h2 : B ⊆ C) : A ∪ B ⊆ C := by
-- 用intro可以不断对结论分解
-- 但是在分解结论的过程中，某些提取出来的前提也还是可以进一步分解的
-- 于是就要另写一个rcases语句分解前提
-- 由于 intro + rcases 的组合非常普遍，因此就有了rintro
-- rintro 就是把 intro + rcases 组合在一条语句中完成
  rintro x (ha | hb)
  · exact h1 ha
  · exact h2 hb

-- 前提中对∧的分解
example (P Q : Prop) (h : P ∧ Q) : P := by
  cases h with
  | intro hP hQ =>
      exact hP

example (P Q : Prop) (h : P ∧ Q) : P := by
  rcases h with ⟨hP, hQ⟩
  exact hP

-- 前提中对∧的嵌套
example (P Q R : Prop) (h : P ∧ Q ∧ R) : R := by
  cases h with
  | intro hP hQR =>
      cases hQR with
      | intro hQ hR =>
        exact hR

example (P Q R : Prop) (h : P ∧ Q ∧ R) : R := by
  rcases h with ⟨hP, hQ, hR⟩
  exact hR

-- 前提中对∃的分解
example {A B : Set U} (h : ∃ x, x ∈ A ∧ x ∈ B) : ∃ x, x ∈ B := by
  cases h with
  | intro x hx =>
    cases hx with
    | intro hA hB =>
      exact ⟨x, hB⟩

example {A B : Set U} (h : ∃ x, x ∈ A ∧ x ∈ B) : ∃ x, x ∈ B := by
  rcases h with ⟨x, hA, hB⟩
  exact ⟨x, hB⟩

example {A B : Set U} (h : ∃ x, x ∈ A ∧ x ∈ B) : ∃ x, x ∈ B := by
  obtain ⟨x, hA, hB⟩ := h
  exact ⟨x, hB⟩

example {A B : Set U} (h : ∃ x, x ∈ A ∨ x ∈ B) : ∃ x, x ∈ A ∪ B := by
  cases h with
  | intro x hx =>
      cases hx with
      | inl hA => exact ⟨x, Or.inl hA⟩
      | inr hB => exact ⟨x, Or.inr hB⟩

example {A B : Set U} (h : ∃ x, x ∈ A ∨ x ∈ B) : ∃ x, x ∈ A ∪ B := by
  rcases h with ⟨x, (hA | hB)⟩
  · exact ⟨x, Or.inl hA⟩
  · exact ⟨x, Or.inr hB⟩

example {A B : Set U} (h : ∃ x, x ∈ A ∨ x ∈ B) : ∃ x, x ∈ A ∪ B := by
  obtain⟨x, hA | hB⟩ := h
  · exact ⟨x, Or.inl hA⟩
  · exact ⟨x, Or.inr hB⟩
end diff_between_cases_and_rcases












example {U : Type} (A : Set U) (h1 : ∀ F:Set (Set U), (⋃₀ F = A → A ∈ F)) :
    ∃ x, A = {x} := by
  let F : Set (Set U) := {S | ∃ x ∈ A, S = ({x} : Set U)}

  have hUnion : ⋃₀ F = A := by
    ext y
    constructor
    · intro hy
-- hy : y ∈ ⋃₀F ↔ ∃S, S ∈ F, y ∈ S
      rcases hy with ⟨S, hSF, hyS⟩
-- hSF : S ∈ F ↔ S ∈ {S | ∃x ∈ A, S = {x}}
-- 一般而言，我们会写hSx把 S = {x} 提取出来
-- 此处用rfl，是rcases的一个特殊模式，会直接把所有前提中的 S 替换成 {x}
      rcases hSF with ⟨x, hxA, rfl⟩
      rw[Set.mem_singleton_iff] at hyS
      rw [hyS]
      exact hxA
    · intro hyA
-- 结论要证明的是 y ∈ ⋃₀F，根据集合并集的成员的定义，等价于找到一个S，使得
-- ∃S, S ∈ F ∧ y ∈ S
-- exact的三个部分
---- {y} 取 S = {y}
---- ⟨y, hyA, rfl⟩证明 {y} ∈ F
-------- {y} ∈ F = {S | ∃x ∈ A, S ={x}} ↔ ∃x, x ∈ A ∧ {y} = {x}
-------- 那么自然就是取 x = y
-------- hyA 满足 y ∈ A
-------- rfl 满足 {y} = {y}
---- by simp 证明 y ∈ {y}
      exact ⟨{y}, ⟨y, hyA, rfl⟩, by simp⟩

  have hA : A ∈ F := h1 F hUnion
  rcases hA with ⟨x, _hxA, hAx⟩
  exact ⟨x, hAx⟩
