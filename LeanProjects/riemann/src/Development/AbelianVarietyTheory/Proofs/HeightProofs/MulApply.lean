import Mathlib

namespace GlobalTheory.OrbitGrowth

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def orb (A : Subalgebra ℂ (Module.End ℂ M)) (x : M) : Submodule ℂ M :=
  Submodule.span ℂ {y | ∃ a ∈ A, y = (a : M → M) x}

lemma orb_le {A : Subalgebra ℂ (Module.End ℂ M)} {x : M} {U : Submodule ℂ M} :
    orb A x ≤ U ↔ ∀ a ∈ A, (a : M → M) x ∈ U := by
  unfold orb
  rw [Submodule.span_le]
  constructor
  · intro h a ha; exact h ⟨a, ha, rfl⟩
  · rintro h y ⟨a, ha, rfl⟩; exact h a ha

lemma mem_orb {A : Subalgebra ℂ (Module.End ℂ M)} {x : M} {a : Module.End ℂ M} (ha : a ∈ A) :
    (a : M → M) x ∈ orb A x := Submodule.subset_span ⟨a, ha, rfl⟩

lemma mul_apply' (a b : Module.End ℂ M) (y : M) : (a * b) y = a (b y) := rfl

def good (A : Subalgebra ℂ (Module.End ℂ M)) : Submodule ℂ M where
  carrier := {x | FiniteDimensional ℂ (orb A x)}
  zero_mem' := by
    show FiniteDimensional ℂ (orb A 0)
    have : orb A 0 ≤ ⊥ := orb_le.mpr (fun a _ => by simp)
    exact Submodule.finiteDimensional_of_le this
  add_mem' := by
    intro x y hx hy
    haveI : FiniteDimensional ℂ (orb A x) := hx
    haveI : FiniteDimensional ℂ (orb A y) := hy
    show FiniteDimensional ℂ (orb A (x + y))
    have : orb A (x + y) ≤ orb A x ⊔ orb A y := orb_le.mpr (fun a ha => by
      rw [map_add]
      exact Submodule.add_mem_sup (mem_orb ha) (mem_orb ha))
    exact Submodule.finiteDimensional_of_le this
  smul_mem' := by
    intro c x hx
    haveI : FiniteDimensional ℂ (orb A x) := hx
    show FiniteDimensional ℂ (orb A (c • x))
    have : orb A (c • x) ≤ orb A x := orb_le.mpr (fun a ha => by
      rw [map_smul]
      exact Submodule.smul_mem _ c (mem_orb ha))
    exact Submodule.finiteDimensional_of_le this

lemma mem_good {A : Subalgebra ℂ (Module.End ℂ M)} {x : M} :
    x ∈ good A ↔ FiniteDimensional ℂ (orb A x) := Iff.rfl

def grow (A : Subalgebra ℂ (Module.End ℂ M)) (W : Submodule ℂ M) : Submodule ℂ M :=
  Submodule.span ℂ {y | ∃ a ∈ A, ∃ x ∈ W, y = (a : M → M) x}

lemma grow_le {A : Subalgebra ℂ (Module.End ℂ M)} {W U : Submodule ℂ M} :
    grow A W ≤ U ↔ ∀ a ∈ A, ∀ x ∈ W, (a : M → M) x ∈ U := by
  unfold grow
  rw [Submodule.span_le]
  constructor
  · intro h a ha x hx; exact h ⟨a, ha, x, hx, rfl⟩
  · rintro h y ⟨a, ha, x, hx, rfl⟩; exact h a ha x hx

lemma mem_grow {A : Subalgebra ℂ (Module.End ℂ M)} {W : Submodule ℂ M} {a : Module.End ℂ M}
    (ha : a ∈ A) {x : M} (hx : x ∈ W) : (a : M → M) x ∈ grow A W :=
  Submodule.subset_span ⟨a, ha, x, hx, rfl⟩

lemma le_grow (A : Subalgebra ℂ (Module.End ℂ M)) (W : Submodule ℂ M) : W ≤ grow A W := by
  intro x hx
  have := mem_grow A.one_mem hx
  simpa using this

lemma grow_inv {A : Subalgebra ℂ (Module.End ℂ M)} {W : Submodule ℂ M} {a : Module.End ℂ M}
    (ha : a ∈ A) {x : M} (hx : x ∈ grow A W) : (a : M → M) x ∈ grow A W := by
  have h : grow A W ≤ (grow A W).comap a := grow_le.mpr (fun b hb y hy => by
    show a (b y) ∈ grow A W
    rw [← mul_apply']
    exact mem_grow (A.mul_mem ha hb) hy)
  exact h hx

lemma grow_inv' {A : Subalgebra ℂ (Module.End ℂ M)} {W : Submodule ℂ M} {c : Module.End ℂ M}
    (hc : ∀ x ∈ W, c x ∈ W) (hcomm : ∀ a ∈ A, c * a = a * c) {x : M} (hx : x ∈ grow A W) :
    c x ∈ grow A W := by
  have h : grow A W ≤ (grow A W).comap c := grow_le.mpr (fun b hb y hy => by
    show c (b y) ∈ grow A W
    rw [← mul_apply', hcomm b hb, mul_apply']
    exact mem_grow hb (hc y hy))
  exact h hx

lemma grow_fd {A : Subalgebra ℂ (Module.End ℂ M)} {W : Submodule ℂ M} [FiniteDimensional ℂ W]
    (hW : W ≤ good A) : FiniteDimensional ℂ (grow A W) := by
  obtain ⟨s, hs⟩ : W.FG := (Submodule.fg_iff_finiteDimensional W).mpr inferInstance
  haveI : ∀ y : s, FiniteDimensional ℂ (orb A (y : M)) := fun y => by
    have hy : (y : M) ∈ W := by rw [← hs]; exact Submodule.subset_span y.2
    exact mem_good.mp (hW hy)
  have hle : grow A W ≤ ⨆ y : s, orb A (y : M) := grow_le.mpr (fun a ha x hx => by
    have h2 : W ≤ (⨆ y : s, orb A (y : M)).comap a := by
      rw [← hs, Submodule.span_le]
      intro y hy
      exact Submodule.mem_iSup_of_mem (⟨y, hy⟩ : s) (mem_orb ha)
    exact h2 hx)
  exact Submodule.finiteDimensional_of_le hle

lemma grow_good {A B : Subalgebra ℂ (Module.End ℂ M)} {W : Submodule ℂ M} (hW : W ≤ good B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) : grow A W ≤ good B :=
  grow_le.mpr (fun a ha x hx => by
    haveI : FiniteDimensional ℂ (orb B x) := mem_good.mp (hW hx)
    have hle : orb B (a x) ≤ (orb B x).map a := orb_le.mpr (fun b hb => by
      have e : b (a x) = a (b x) := by
        rw [← mul_apply', ← mul_apply', hcomm a ha b hb]
      rw [e]
      exact Submodule.mem_map_of_mem (mem_orb hb))
    exact mem_good.mpr (Submodule.finiteDimensional_of_le hle))

theorem main : ∀ (M : Type) [inst : AddCommGroup M] [inst_1 : Module ℂ M] (ι : Type) [Finite ι]
    (A : ι → Subalgebra ℂ (Module.End ℂ M)),
    (∀ (i j : ι), i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a) → ∀ (m : M),
    (∀ (i : ι), FiniteDimensional ℂ ↥(Submodule.span ℂ {x : M | ∃ a ∈ A i, x = (a : M → M) m})) →
    ∃ (W : Submodule ℂ M), FiniteDimensional ℂ ↥W ∧ m ∈ W ∧
      ∀ (i : ι), ∀ a ∈ A i, ∀ x ∈ W, (a : M → M) x ∈ W := by
  intro M _ _ ι _ A hcomm m hfin
  classical
  haveI := Fintype.ofFinite ι
  have key : ∀ S : Finset ι, ∃ W : Submodule ℂ M, FiniteDimensional ℂ W ∧ m ∈ W ∧
      (∀ i ∈ S, ∀ a ∈ A i, ∀ x ∈ W, a x ∈ W) ∧ (∀ j, j ∉ S → W ≤ good (A j)) := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · refine ⟨Submodule.span ℂ {m}, inferInstance, Submodule.mem_span_singleton_self m,
        by simp, ?_⟩
      intro j _
      rw [Submodule.span_le, Set.singleton_subset_iff]
      exact mem_good.mpr (hfin j)
    · intro j S hj ih
      obtain ⟨W, hWfd, hmW, hinv, hgood⟩ := ih
      refine ⟨grow (A j) W, grow_fd (hgood j hj), le_grow _ _ hmW, ?_, ?_⟩
      · intro i hi a ha x hx
        rcases Finset.mem_insert.mp hi with rfl | hiS
        · exact grow_inv ha hx
        · have hij : i ≠ j := fun h => hj (h ▸ hiS)
          exact grow_inv' (hinv i hiS a ha) (fun b hb => hcomm i j hij a ha b hb) hx
      · intro k hk
        have hkj : k ≠ j := fun h => hk (h ▸ Finset.mem_insert_self j S)
        have hkS : k ∉ S := fun h => hk (Finset.mem_insert_of_mem h)
        exact grow_good (hgood k hkS) (fun a ha b hb => (hcomm k j hkj b hb a ha).symm)
  obtain ⟨W, h1, h2, h3, -⟩ := key Finset.univ
  exact ⟨W, h1, h2, fun i a ha x hx => h3 i (Finset.mem_univ i) a ha x hx⟩

end GlobalTheory.OrbitGrowth
