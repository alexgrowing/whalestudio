import Mathlib
import GroundTheory.AutomorphicForms.InductionParabolic
import GroundTheory.AutomorphicForms.AffineBruhat

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal ValuativeRel Topology Filter Set

section Elimination

variable {F : Type*} [Field F] {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)

def elimKey (i : Fin n) : α ×ₗ Fin n := toLex (β i, i)

variable {β}

omit [LinearOrder α] in
theorem elimKey_injective : Function.Injective (elimKey β) := fun i j h => by
  have := congrArg (fun p => (ofLex p).2) h
  simpa [elimKey] using this

theorem le_of_elimKey_lt {i j : Fin n} (h : elimKey β i < elimKey β j) : β i ≤ β j := by
  rw [elimKey, elimKey, Prod.Lex.toLex_lt_toLex] at h
  rcases h with h | ⟨h, -⟩
  · exact h.le
  · exact h.le

theorem lt_of_elimKey_lt {i j : Fin n} (h : elimKey β i < elimKey β j) (hβ : Monotone β) :
    i < j := by
  rw [elimKey, elimKey, Prod.Lex.toLex_lt_toLex] at h
  rcases h with h | ⟨-, h⟩
  · exact lt_of_not_ge fun hji => (hβ hji).not_gt h
  · exact h

theorem elimKey_lt_of_le {i j : Fin n} (h : elimKey β i ≤ elimKey β j) (hij : i ≠ j) :
    elimKey β i < elimKey β j :=
  lt_of_le_of_ne h fun e => hij (elimKey_injective e)

variable (β)

def elimCol (h : Matrix (Fin n) (Fin n) F) (a : Fin n) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i k => if k = a ∧ elimKey β a < elimKey β i then h i a / h a a else 0

variable {β}

theorem elimCol_apply (h : Matrix (Fin n) (Fin n) F) (a i k : Fin n) :
    elimCol β h a i k = if k = a ∧ elimKey β a < elimKey β i then h i a / h a a else 0 := rfl

theorem elimCol_mul_elimCol (h : Matrix (Fin n) (Fin n) F) (a : Fin n) :
    elimCol β h a * elimCol β h a = 0 := by
  ext i l
  rw [mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k = a
  · subst hk
    rw [elimCol_apply h k k l, if_neg (fun h => lt_irrefl _ h.2), mul_zero]
  · rw [elimCol_apply, if_neg (fun h => hk h.1), zero_mul]

theorem elimCol_mul_apply (h : Matrix (Fin n) (Fin n) F) (a i l : Fin n) :
    (elimCol β h a * h) i l = if elimKey β a < elimKey β i then h i a / h a a * h a l else 0 := by
  rw [mul_apply]
  simp only [elimCol_apply]
  split_ifs with hi
  · rw [Finset.sum_eq_single a]
    · rw [if_pos ⟨rfl, hi⟩]
    · intro k _ hk
      rw [if_neg (fun h => hk h.1), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  · refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg (fun h => hi h.2), zero_mul]

variable (β)

def elimGL (h : Matrix (Fin n) (Fin n) F) (a : Fin n) : GL (Fin n) F where
  val := 1 - elimCol β h a
  inv := 1 + elimCol β h a
  val_inv := by
    rw [sub_mul, mul_add, mul_add, one_mul, mul_one, one_mul, elimCol_mul_elimCol]
    abel
  inv_val := by
    rw [add_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, elimCol_mul_elimCol]
    abel

variable {β}

theorem elimGL_apply (h : Matrix (Fin n) (Fin n) F) (a i k : Fin n) :
    (elimGL β h a : GL (Fin n) F) i k = (1 : Matrix (Fin n) (Fin n) F) i k - elimCol β h a i k :=
  rfl

theorem elimGL_inv_apply (h : Matrix (Fin n) (Fin n) F) (a i k : Fin n) :
    ((elimGL β h a)⁻¹ : GL (Fin n) F) i k =
      (1 : Matrix (Fin n) (Fin n) F) i k + elimCol β h a i k :=
  rfl

theorem elimGL_mem_blockUpper_dual (h : Matrix (Fin n) (Fin n) F) (a : Fin n) :
    elimGL β h a ∈ blockUpper F n (OrderDual.toDual ∘ β) := by
  rw [mem_blockUpper]
  intro i k hik
  have hik' : β i < β k := hik
  show (1 : Matrix (Fin n) (Fin n) F) i k - elimCol β h a i k = 0
  rw [one_apply_ne (fun e => hik'.ne (by rw [e])), elimCol_apply, if_neg, sub_zero]
  rintro ⟨rfl, hk⟩
  exact (le_of_elimKey_lt hk).not_gt hik'

theorem exists_mul_mem_blockUpper (K : Subgroup (GL (Fin n) F))
    (hdiag : ∀ h ∈ K, ∀ a, (h : GL (Fin n) F) a a ≠ 0)
    (helim : ∀ h ∈ K, ∀ a, elimGL β ((h : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a ∈ K)
    {g : GL (Fin n) F} (hg : g ∈ K) :
    ∃ q ∈ K ⊓ blockUpper F n (OrderDual.toDual ∘ β), q * g ∈ blockUpper F n β := by
  classical
  have key : ∀ s : Finset (Fin n), ∃ q ∈ K ⊓ blockUpper F n (OrderDual.toDual ∘ β),
      ∀ j ∈ s, ∀ i, elimKey β j < elimKey β i → (q * g : GL (Fin n) F) i j = 0 := by
    intro s
    induction s using Finset.induction_on_max_value (elimKey β) with
    | empty => exact ⟨1, one_mem _, fun j hj => absurd hj (Finset.notMem_empty j)⟩
    | insert a s ha hmax ih =>
      obtain ⟨q, hq, hz⟩ := ih
      set h : GL (Fin n) F := q * g with hh
      have hK : h ∈ K := K.mul_mem (Subgroup.mem_inf.1 hq).1 hg
      refine ⟨elimGL β (h : Matrix (Fin n) (Fin n) F) a * q,
        Subgroup.mem_inf.2 ⟨K.mul_mem (helim h hK a) (Subgroup.mem_inf.1 hq).1,
          Subgroup.mul_mem _ (elimGL_mem_blockUpper_dual _ a) (Subgroup.mem_inf.1 hq).2⟩, ?_⟩
      intro j hj i hji
      have hentry : ((elimGL β (h : Matrix (Fin n) (Fin n) F) a * q * g : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) i j =
          (h : Matrix (Fin n) (Fin n) F) i j -
            (elimCol β (h : Matrix (Fin n) (Fin n) F) a * (h : Matrix (Fin n) (Fin n) F)) i j := by
        rw [mul_assoc, Units.val_mul, ← hh]
        show ((1 - elimCol β (h : Matrix (Fin n) (Fin n) F) a) *
          (h : Matrix (Fin n) (Fin n) F)) i j = _
        rw [sub_mul, one_mul, Matrix.sub_apply]
      show ((elimGL β (h : Matrix (Fin n) (Fin n) F) a * q * g : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F) i j = 0
      rw [hentry, elimCol_mul_apply]
      rcases Finset.mem_insert.1 hj with rfl | hjs
      · rw [if_pos hji, div_mul_cancel₀ _ (hdiag h hK j), sub_self]
      · have hja : elimKey β j < elimKey β a :=
          elimKey_lt_of_le (hmax j hjs) (fun e => ha (e ▸ hjs))
        have h1 : (h : GL (Fin n) F) i j = 0 := hz j hjs i hji
        have h2 : (h : GL (Fin n) F) a j = 0 := hz j hjs a hja
        change (h : Matrix (Fin n) (Fin n) F) i j - _ = 0 at *
        split_ifs
        · rw [show (h : Matrix (Fin n) (Fin n) F) a j = 0 from h2, mul_zero, sub_zero]
          exact h1
        · rw [sub_zero]
          exact h1
  obtain ⟨q, hq, hz⟩ := key Finset.univ
  refine ⟨q, hq, ?_⟩
  rw [mem_blockUpper]
  intro i j hji
  refine hz j (Finset.mem_univ j) i ?_
  rw [elimKey, elimKey, Prod.Lex.toLex_lt_toLex]
  exact Or.inl hji

theorem mem_levi_dual {g : GL (Fin n) F} :
    g ∈ levi F n (OrderDual.toDual ∘ β) ↔ g ∈ levi F n β := by
  rw [mem_levi, mem_levi]
  simp only [Function.comp_apply, ne_eq, EmbeddingLike.apply_eq_iff_eq]

theorem iwahoriFactorization_of_elim (K : Subgroup (GL (Fin n) F))
    (hdiag : ∀ h ∈ K, ∀ a, (h : GL (Fin n) F) a a ≠ 0)
    (helim : ∀ h ∈ K, ∀ a, elimGL β ((h : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a ∈ K)
    (hlevi : ∀ p (hp : p ∈ blockUpper F n β), p ∈ K →
      ((leviProj F n β ⟨p, hp⟩ : levi F n β) : GL (Fin n) F) ∈ K)
    (hlevi' : ∀ p (hp : p ∈ blockUpper F n (OrderDual.toDual ∘ β)), p ∈ K →
      ((leviProj F n (OrderDual.toDual ∘ β) ⟨p, hp⟩ : levi F n (OrderDual.toDual ∘ β)) :
        GL (Fin n) F) ∈ K) :
    ∀ k ∈ K, ∃ z ∈ K ⊓ oppositeUnipotentRadical F n β, ∃ y ∈ K ⊓ levi F n β,
      ∃ x ∈ K ⊓ unipotentRadical F n β, k = z * y * x := by
  intro k hk
  obtain ⟨q, hq, hqk⟩ := exists_mul_mem_blockUpper K hdiag helim hk
  obtain ⟨hqK, hqP⟩ := Subgroup.mem_inf.1 hq
  set p := q⁻¹ with hp
  have hpK : p ∈ K := K.inv_mem hqK
  have hpP : p ∈ blockUpper F n (OrderDual.toDual ∘ β) := Subgroup.inv_mem _ hqP
  set h := q * k with hh
  have hhK : h ∈ K := K.mul_mem hqK hk
  set m₁ := leviProj F n (OrderDual.toDual ∘ β) ⟨p, hpP⟩ with hm₁
  set m₂ := leviProj F n β ⟨h, hqk⟩ with hm₂
  have hm₁K : (m₁ : GL (Fin n) F) ∈ K := hlevi' p hpP hpK
  have hm₂K : (m₂ : GL (Fin n) F) ∈ K := hlevi h hqk hhK
  have hu₁ := leviProj_inv_mul_mem (F := F) (β := OrderDual.toDual ∘ β) ⟨p, hpP⟩
  have hu₂ := leviProj_inv_mul_mem (F := F) (β := β) ⟨h, hqk⟩
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hu₁ hu₂
  change (m₁ : GL (Fin n) F)⁻¹ * p ∈ oppositeUnipotentRadical F n β at hu₁
  change (m₂ : GL (Fin n) F)⁻¹ * h ∈ unipotentRadical F n β at hu₂
  refine ⟨p * (m₁ : GL (Fin n) F)⁻¹, Subgroup.mem_inf.2 ⟨K.mul_mem hpK (K.inv_mem hm₁K), ?_⟩,
    (m₁ : GL (Fin n) F) * m₂, Subgroup.mem_inf.2 ⟨K.mul_mem hm₁K hm₂K,
      (levi F n β).mul_mem (mem_levi_dual.1 m₁.2) m₂.2⟩,
    (m₂ : GL (Fin n) F)⁻¹ * h, Subgroup.mem_inf.2 ⟨K.mul_mem (K.inv_mem hm₂K) hhK, hu₂⟩, ?_⟩
  · have := conj_mem_unipotentRadical (levi_le_blockUpper m₁.2) hu₁
    rwa [mul_inv_cancel_left] at this
  · rw [hh, hp]
    group

end Elimination

section Local

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}

local notation "ϖ" => ((GLnLocal.uniformizer F : 𝒪[F]) : F)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem valuation_one_apply_le (i j : Fin n) :
    valuation F ((1 : Matrix (Fin n) (Fin n) F) i j) ≤ 1 := by
  by_cases h : i = j
  · rw [h, one_apply_eq, map_one]
  · rw [one_apply_ne h, map_zero]
    exact zero_le

theorem mem_congruenceSubgroup_of_le {m : ℕ} {g : GL (Fin n) F}
    (h1 : ∀ i j, valuation F (g i j - (1 : Matrix (Fin n) (Fin n) F) i j) ≤ valuation F ϖ ^ m)
    (h2 : ∀ i j, valuation F ((g⁻¹ : GL (Fin n) F) i j - (1 : Matrix (Fin n) (Fin n) F) i j) ≤
      valuation F ϖ ^ m) :
    g ∈ congruenceSubgroup F n m := by
  have hle : valuation F ϖ ^ m ≤ 1 := pow_le_one' (valuation_uniformizer_lt_one F).le m
  have hint : ∀ (x : F) (i j : Fin n),
      valuation F (x - (1 : Matrix (Fin n) (Fin n) F) i j) ≤ valuation F ϖ ^ m → x ∈ 𝒪[F] := by
    intro x i j hx
    refine (Valuation.mem_integer_iff _ _).mpr ?_
    have : x = (x - (1 : Matrix (Fin n) (Fin n) F) i j) + (1 : Matrix (Fin n) (Fin n) F) i j := by
      ring
    rw [this]
    exact Valuation.map_add_le _ (hx.trans hle) (valuation_one_apply_le i j)
  rw [mem_congruenceSubgroup_iff F n, mem_integralGL_iff F n]
  exact ⟨⟨fun i j => hint _ i j (h1 i j), fun i j => hint _ i j (h2 i j)⟩, h1⟩

theorem diag_ne_zero_of_mem_iwahori {h : GL (Fin n) F} (hh : h ∈ iwahori F n) (a : Fin n) :
    h a a ≠ 0 := fun e => by
  have := ((mem_iwahori_iff F n).1 hh).2.2 a
  rw [e, map_zero] at this
  exact zero_ne_one this

theorem diag_ne_zero_of_mem_congruenceSubgroup {m : ℕ} (hm : 1 ≤ m) {h : GL (Fin n) F}
    (hh : h ∈ congruenceSubgroup F n m) (a : Fin n) : h a a ≠ 0 :=
  diag_ne_zero_of_mem_iwahori
    (congruenceSubgroup_one_le_iwahori F n (congruenceSubgroup_antitone F n hm hh)) a

theorem valuation_elimCol_le {m : ℕ} (hm : 1 ≤ m) {h : GL (Fin n) F}
    (hh : h ∈ congruenceSubgroup F n m) (a i k : Fin n) :
    valuation F (elimCol β (h : Matrix (Fin n) (Fin n) F) a i k) ≤ valuation F ϖ ^ m := by
  rw [elimCol_apply]
  split_ifs with hik
  · have hia : i ≠ a := fun hh' => lt_irrefl _ (hh' ▸ hik.2)
    have h1 := ((mem_congruenceSubgroup_iff F n).1 hh).2 i a
    rw [one_apply_ne hia, sub_zero] at h1
    have hdiag := ((mem_iwahori_iff F n).1
      (congruenceSubgroup_one_le_iwahori F n (congruenceSubgroup_antitone F n hm hh))).2.2 a
    rw [map_div₀, hdiag, div_one]
    exact h1
  · rw [map_zero]
    exact zero_le

theorem elimGL_mem_congruenceSubgroup {m : ℕ} (hm : 1 ≤ m) {h : GL (Fin n) F}
    (hh : h ∈ congruenceSubgroup F n m) (a : Fin n) :
    elimGL β (h : Matrix (Fin n) (Fin n) F) a ∈ congruenceSubgroup F n m :=
  mem_congruenceSubgroup_of_le
    (fun i k => by
      rw [elimGL_apply, sub_sub_cancel_left, Valuation.map_neg]
      exact valuation_elimCol_le hm hh a i k)
    (fun i k => by
      rw [elimGL_inv_apply, add_sub_cancel_left]
      exact valuation_elimCol_le hm hh a i k)

theorem leviProj_mem_congruenceSubgroup {m : ℕ} {p : GL (Fin n) F}
    (hp : p ∈ blockUpper F n β) (hpK : p ∈ congruenceSubgroup F n m) :
    ((leviProj F n β ⟨p, hp⟩ : levi F n β) : GL (Fin n) F) ∈ congruenceSubgroup F n m := by
  have key : ∀ q : blockUpper F n β, (q : GL (Fin n) F) ∈ congruenceSubgroup F n m →
      ∀ i j, valuation F (((leviProj F n β q : levi F n β) : GL (Fin n) F) i j -
        (1 : Matrix (Fin n) (Fin n) F) i j) ≤ valuation F ϖ ^ m := by
    intro q hq i j
    rw [leviProj_apply]
    split_ifs with hij
    · exact ((mem_congruenceSubgroup_iff F n).1 hq).2 i j
    · rw [one_apply_ne (fun hh => hij (by rw [hh])), sub_zero, map_zero]
      exact zero_le
  refine mem_congruenceSubgroup_of_le (key ⟨p, hp⟩ hpK) ?_
  have : ((leviProj F n β ⟨p, hp⟩ : levi F n β) : GL (Fin n) F)⁻¹ =
      ((leviProj F n β (⟨p, hp⟩ : blockUpper F n β)⁻¹ : levi F n β) : GL (Fin n) F) := by
    rw [map_inv, Subgroup.coe_inv]
  rw [this]
  exact key _ ((congruenceSubgroup F n m).inv_mem hpK)

theorem leviProj_mem_iwahori {p : GL (Fin n) F} (hp : p ∈ blockUpper F n β)
    (hpI : p ∈ iwahori F n) :
    ((leviProj F n β ⟨p, hp⟩ : levi F n β) : GL (Fin n) F) ∈ iwahori F n := by
  obtain ⟨h1, h2, h3⟩ := (mem_iwahori_iff F n).1 hpI
  rw [mem_iwahori_iff F n]
  refine ⟨fun i j => ?_, fun i j hij => ?_, fun i => ?_⟩
  · rw [leviProj_apply]
    split_ifs
    · exact h1 i j
    · rw [map_zero]
      exact zero_le
  · rw [leviProj_apply]
    split_ifs
    · exact h2 i j hij
    · rw [map_zero]
      exact zero_lt_one
  · rw [leviProj_apply, if_pos rfl]
    exact h3 i

theorem valuation_elimCol_lt_one (hβ : Monotone β) {h : GL (Fin n) F} (hh : h ∈ iwahori F n)
    (a i k : Fin n) : valuation F (elimCol β (h : Matrix (Fin n) (Fin n) F) a i k) < 1 := by
  obtain ⟨-, h2, h3⟩ := (mem_iwahori_iff F n).1 hh
  rw [elimCol_apply]
  split_ifs with hik
  · rw [map_div₀, h3 a, div_one]
    exact h2 i a (lt_of_elimKey_lt hik.2 hβ)
  · rw [map_zero]
    exact zero_lt_one

theorem elimGL_mem_iwahori (hβ : Monotone β) {h : GL (Fin n) F} (hh : h ∈ iwahori F n)
    (a : Fin n) : elimGL β (h : Matrix (Fin n) (Fin n) F) a ∈ iwahori F n := by
  have hD := valuation_elimCol_lt_one hβ hh a
  rw [mem_iwahori_iff F n]
  refine ⟨fun i k => ?_, fun i k hki => ?_, fun i => ?_⟩
  · rw [elimGL_apply]
    exact Valuation.map_sub_le _ (valuation_one_apply_le i k) (hD i k).le
  · rw [elimGL_apply, one_apply_ne hki.ne', zero_sub, Valuation.map_neg]
    exact hD i k
  · rw [elimGL_apply, one_apply_eq]
    refine (Valuation.map_eq_of_sub_lt _ ?_).trans (map_one _)
    rw [sub_sub_cancel_left, Valuation.map_neg, map_one]
    exact hD i i

variable (β) in

theorem congruenceSubgroup_iwahoriFactorization {m : ℕ} (hm : 1 ≤ m) :
    ∀ k ∈ congruenceSubgroup F n m,
      ∃ z ∈ congruenceSubgroup F n m ⊓ oppositeUnipotentRadical F n β,
      ∃ y ∈ congruenceSubgroup F n m ⊓ levi F n β,
      ∃ x ∈ congruenceSubgroup F n m ⊓ unipotentRadical F n β, k = z * y * x :=
  iwahoriFactorization_of_elim _ (fun _ hh a => diag_ne_zero_of_mem_congruenceSubgroup hm hh a)
    (fun _ hh a => elimGL_mem_congruenceSubgroup hm hh a)
    (fun _ hp hpK => leviProj_mem_congruenceSubgroup hp hpK)
    (fun _ hp hpK => leviProj_mem_congruenceSubgroup hp hpK)

theorem iwahori_iwahoriFactorization (hβ : Monotone β) :
    ∀ k ∈ iwahori F n, ∃ z ∈ iwahori F n ⊓ oppositeUnipotentRadical F n β,
      ∃ y ∈ iwahori F n ⊓ levi F n β, ∃ x ∈ iwahori F n ⊓ unipotentRadical F n β,
        k = z * y * x :=
  iwahoriFactorization_of_elim _ (fun _ hh a => diag_ne_zero_of_mem_iwahori hh a)
    (fun _ hh a => elimGL_mem_iwahori hβ hh a)
    (fun _ hp hpI => leviProj_mem_iwahori hp hpI)
    (fun _ hp hpI => leviProj_mem_iwahori hp hpI)

end Local

theorem iwahoriFactorization_symm {G : Type*} [Group G] {K Nbar M N : Subgroup G}
    (h : ∀ k ∈ K, ∃ z ∈ K ⊓ Nbar, ∃ y ∈ K ⊓ M, ∃ x ∈ K ⊓ N, k = z * y * x) :
    ∀ k ∈ K, ∃ x ∈ K ⊓ N, ∃ y ∈ K ⊓ M, ∃ z ∈ K ⊓ Nbar, k = x * y * z := by
  intro k hk
  obtain ⟨z, hz, y, hy, x, hx, e⟩ := h k⁻¹ (K.inv_mem hk)
  refine ⟨x⁻¹, Subgroup.inv_mem _ hx, y⁻¹, Subgroup.inv_mem _ hy, z⁻¹, Subgroup.inv_mem _ hz, ?_⟩
  rw [← inv_inv k, e]
  group

section LocalSymm

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)

theorem congruenceSubgroup_iwahoriFactorization' {m : ℕ} (hm : 1 ≤ m) :
    ∀ k ∈ congruenceSubgroup F n m, ∃ x ∈ congruenceSubgroup F n m ⊓ unipotentRadical F n β,
      ∃ y ∈ congruenceSubgroup F n m ⊓ levi F n β,
      ∃ z ∈ congruenceSubgroup F n m ⊓ oppositeUnipotentRadical F n β, k = x * y * z :=
  iwahoriFactorization_symm (congruenceSubgroup_iwahoriFactorization β hm)

variable {β} in

theorem iwahori_iwahoriFactorization' (hβ : Monotone β) :
    ∀ k ∈ iwahori F n, ∃ x ∈ iwahori F n ⊓ unipotentRadical F n β,
      ∃ y ∈ iwahori F n ⊓ levi F n β, ∃ z ∈ iwahori F n ⊓ oppositeUnipotentRadical F n β,
        k = x * y * z :=
  iwahoriFactorization_symm (iwahori_iwahoriFactorization hβ)

end LocalSymm

section Contraction

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}

local notation "ϖ" => ((GLnLocal.uniformizer F : 𝒪[F]) : F)

theorem valuation_zpow_mul_le_pow_mul {x : F} {e : ℕ} {z : ℤ} (hz : (e : ℤ) ≤ z) :
    valuation F (ϖ ^ z * x) ≤ valuation F ϖ ^ e * valuation F x := by
  obtain ⟨d, rfl⟩ : ∃ d : ℕ, z = e + d := ⟨(z - e).toNat, by omega⟩
  rw [zpow_add₀ uniformizer_ne_zero, zpow_natCast, zpow_natCast, map_mul, map_mul, map_pow,
    map_pow, mul_right_comm]
  exact mul_le_of_le_one_right' (pow_le_one' (valuation_uniformizer_lt_one F).le d)

theorem valuation_rankTorus_conj_sub_le {e : ℕ} {u : GL (Fin n) F}
    (hu : u ∈ unipotentRadical F n β) (i j : Fin n) :
    valuation F ((rankTorus F n β e * u * (rankTorus F n β e)⁻¹ : GL (Fin n) F) i j -
      (1 : Matrix (Fin n) (Fin n) F) i j) ≤
        valuation F ϖ ^ e * valuation F (u i j - (1 : Matrix (Fin n) (Fin n) F) i j) := by
  obtain ⟨hP, h1⟩ := mem_unipotentRadical.1 hu
  rw [rankTorus_conj_apply]
  rcases lt_trichotomy (β i) (β j) with h | h | h
  · have hij : i ≠ j := fun hh => h.ne (by rw [hh])
    rw [one_apply_ne hij, sub_zero, sub_zero]
    refine valuation_zpow_mul_le_pow_mul ?_
    have := blockRank_lt h
    have : e * blockRank β i + e ≤ e * blockRank β j := by nlinarith
    push_cast
    omega
  · rw [h1 i j h, blockRank_eq h, sub_self, zpow_zero, one_mul, sub_self, map_zero]
    exact zero_le
  · rw [hP h, mul_zero, one_apply_ne (fun hh => h.ne' (by rw [hh])), sub_zero, map_zero]
    exact zero_le

theorem valuation_rankTorus_inv_conj_sub_le {e : ℕ} {z : GL (Fin n) F}
    (hz : z ∈ oppositeUnipotentRadical F n β) (i j : Fin n) :
    valuation F (((rankTorus F n β e)⁻¹ * z * rankTorus F n β e : GL (Fin n) F) i j -
      (1 : Matrix (Fin n) (Fin n) F) i j) ≤
        valuation F ϖ ^ e * valuation F (z i j - (1 : Matrix (Fin n) (Fin n) F) i j) := by
  obtain ⟨hlow, h1⟩ := mem_oppositeUnipotentRadical.1 hz
  rw [rankTorus_inv_conj_apply]
  rcases lt_trichotomy (β i) (β j) with h | h | h
  · rw [hlow i j h, mul_zero, one_apply_ne (fun hh => h.ne (by rw [hh])), sub_zero, map_zero]
    exact zero_le
  · rw [h1 i j h, blockRank_eq h, sub_self, zpow_zero, one_mul, sub_self, map_zero]
    exact zero_le
  · have hij : i ≠ j := fun hh => h.ne' (by rw [hh])
    rw [one_apply_ne hij, sub_zero, sub_zero]
    refine valuation_zpow_mul_le_pow_mul ?_
    have := blockRank_lt h
    have : e * blockRank β j + e ≤ e * blockRank β i := by nlinarith
    push_cast
    omega

theorem rankTorus_conj_mem_congruenceSubgroup {e m : ℕ} {u : GL (Fin n) F}
    (hu : u ∈ congruenceSubgroup F n m ⊓ unipotentRadical F n β) :
    rankTorus F n β e * u * (rankTorus F n β e)⁻¹ ∈
      congruenceSubgroup F n (m + e) ⊓ unipotentRadical F n β := by
  have hb : ∀ w ∈ congruenceSubgroup F n m ⊓ unipotentRadical F n β, ∀ i j,
      valuation F ((rankTorus F n β e * w * (rankTorus F n β e)⁻¹ : GL (Fin n) F) i j -
        (1 : Matrix (Fin n) (Fin n) F) i j) ≤ valuation F ϖ ^ (m + e) := by
    intro w hw i j
    obtain ⟨hwK, hwN⟩ := Subgroup.mem_inf.1 hw
    refine (valuation_rankTorus_conj_sub_le hwN i j).trans ?_
    rw [pow_add, mul_comm (valuation F ϖ ^ m)]
    gcongr
    exact ((mem_congruenceSubgroup_iff F n).1 hwK).2 i j
  refine Subgroup.mem_inf.2 ⟨mem_congruenceSubgroup_of_le (hb u hu) ?_,
    conj_mem_unipotentRadical (rankTorus_mem_blockUpper e) (Subgroup.mem_inf.1 hu).2⟩
  have : (rankTorus F n β e * u * (rankTorus F n β e)⁻¹)⁻¹ =
      rankTorus F n β e * u⁻¹ * (rankTorus F n β e)⁻¹ := by group
  rw [this]
  exact hb _ (Subgroup.inv_mem _ hu)

theorem rankTorus_inv_conj_mem_congruenceSubgroup {e m : ℕ} {z : GL (Fin n) F}
    (hz : z ∈ congruenceSubgroup F n m ⊓ oppositeUnipotentRadical F n β) :
    (rankTorus F n β e)⁻¹ * z * rankTorus F n β e ∈
      congruenceSubgroup F n (m + e) ⊓ oppositeUnipotentRadical F n β := by
  have hb : ∀ w ∈ congruenceSubgroup F n m ⊓ oppositeUnipotentRadical F n β, ∀ i j,
      valuation F (((rankTorus F n β e)⁻¹ * w * rankTorus F n β e : GL (Fin n) F) i j -
        (1 : Matrix (Fin n) (Fin n) F) i j) ≤ valuation F ϖ ^ (m + e) := by
    intro w hw i j
    obtain ⟨hwK, hwN⟩ := Subgroup.mem_inf.1 hw
    refine (valuation_rankTorus_inv_conj_sub_le hwN i j).trans ?_
    rw [pow_add, mul_comm (valuation F ϖ ^ m)]
    gcongr
    exact ((mem_congruenceSubgroup_iff F n).1 hwK).2 i j
  have htP : (rankTorus F n β e)⁻¹ ∈ blockUpper F n (OrderDual.toDual ∘ β) :=
    Subgroup.inv_mem _ (Subgroup.mem_inf.1 (rankTorus_mem_levi (F := F) (β := β) e)).2
  have hN := conj_mem_unipotentRadical htP (Subgroup.mem_inf.1 hz).2
  rw [inv_inv] at hN
  refine Subgroup.mem_inf.2 ⟨mem_congruenceSubgroup_of_le (hb z hz) ?_, hN⟩
  have : ((rankTorus F n β e)⁻¹ * z * rankTorus F n β e)⁻¹ =
      (rankTorus F n β e)⁻¹ * z⁻¹ * rankTorus F n β e := by group
  rw [this]
  exact hb _ (Subgroup.inv_mem _ hz)

variable (β) in

theorem exists_central_contracting (m : ℕ) :
    ∃ a ∈ levi F n β, (∀ y ∈ levi F n β, a * y = y * a) ∧
      (∀ u ∈ congruenceSubgroup F n m ⊓ unipotentRadical F n β,
        a * u * a⁻¹ ∈ congruenceSubgroup F n m ⊓ unipotentRadical F n β) ∧
      (∀ z ∈ congruenceSubgroup F n m ⊓ oppositeUnipotentRadical F n β,
        a⁻¹ * z * a ∈ congruenceSubgroup F n m ⊓ oppositeUnipotentRadical F n β) ∧
      ∀ U ∈ 𝓝 (1 : GL (Fin n) F), ∃ k : ℕ,
        (∀ u ∈ congruenceSubgroup F n m ⊓ unipotentRadical F n β, a ^ k * u * (a ^ k)⁻¹ ∈ U) ∧
        ∀ z ∈ congruenceSubgroup F n m ⊓ oppositeUnipotentRadical F n β,
          (a ^ k)⁻¹ * z * a ^ k ∈ U := by
  have hmono : congruenceSubgroup F n (m + 1) ≤ congruenceSubgroup F n m :=
    congruenceSubgroup_antitone F n (by omega)
  refine ⟨rankTorus F n β 1, rankTorus_mem_levi 1, fun y hy => rankTorus_commute 1 hy,
    fun u hu => ?_, fun z hz => ?_, fun U hU => ?_⟩
  · have := Subgroup.mem_inf.1 (rankTorus_conj_mem_congruenceSubgroup (e := 1) hu)
    exact Subgroup.mem_inf.2 ⟨hmono this.1, this.2⟩
  · have := Subgroup.mem_inf.1 (rankTorus_inv_conj_mem_congruenceSubgroup (e := 1) hz)
    exact Subgroup.mem_inf.2 ⟨hmono this.1, this.2⟩
  · obtain ⟨t, -, ht⟩ := (hasBasis_nhds_one F n).mem_iff.1 hU
    have hle : congruenceSubgroup F n (m + t) ≤ congruenceSubgroup F n t :=
      congruenceSubgroup_antitone F n (by omega)
    refine ⟨t, fun u hu => ht ?_, fun z hz => ht ?_⟩
    · rw [rankTorus_pow, one_mul]
      exact hle (Subgroup.mem_inf.1 (rankTorus_conj_mem_congruenceSubgroup hu)).1
    · rw [rankTorus_pow, one_mul]
      exact hle (Subgroup.mem_inf.1 (rankTorus_inv_conj_mem_congruenceSubgroup hz)).1

end Contraction

section Jacquet

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
  {V : Type*} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}

theorem jacquetFixedMap_surjective_congruenceSubgroup (hπ : IsAdmissible π) {m : ℕ} (hm : 1 ≤ m) :
    Function.Surjective (jacquetFixedMap F n β π (congruenceSubgroup F n m)) :=
  jacquetFixedMap_surjective hπ (isCompact_congruenceSubgroup F n m)
    (isOpen_congruenceSubgroup F n m) (congruenceSubgroup_iwahoriFactorization β hm)

variable {β} in

theorem jacquetFixedMap_surjective_iwahori (hπ : IsAdmissible π) (hβ : Monotone β) :
    Function.Surjective (jacquetFixedMap F n β π (iwahori F n)) :=
  jacquetFixedMap_surjective hπ (isCompact_iwahori F n) (isOpen_iwahori F n)
    (iwahori_iwahoriFactorization hβ)

end Jacquet

end Parabolic

end GroundTheory.Automorphic
