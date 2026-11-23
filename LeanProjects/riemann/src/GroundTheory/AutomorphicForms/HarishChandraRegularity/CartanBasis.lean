import Mathlib
import GroundTheory.AutomorphicForms.GKModules.Casimir
import GroundTheory.AutomorphicForms.RealGroupsLie

namespace GroundTheory.Automorphic

open Matrix

set_option linter.unusedSectionVars false

attribute [local instance 100] LieRing.ofAssociativeRing

section TraceForm

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (L : LieSubalgebra ℝ (Matrix ι ι 𝕜))

noncomputable def traceForm : LinearMap.BilinForm ℝ L :=
  LinearMap.mk₂ ℝ (fun X Y => RCLike.re (trace ((X : Matrix ι ι 𝕜) * (Y : Matrix ι ι 𝕜))))
    (fun X₁ X₂ Y => by simp [Matrix.add_mul, trace_add])
    (fun r X Y => by simp [trace_smul, RCLike.smul_re])
    (fun X Y₁ Y₂ => by simp [Matrix.mul_add, trace_add])
    (fun r X Y => by simp [trace_smul, RCLike.smul_re])

variable {L}

theorem traceForm_apply (X Y : L) :
    traceForm L X Y = RCLike.re (trace ((X : Matrix ι ι 𝕜) * (Y : Matrix ι ι 𝕜))) := rfl

theorem traceForm_symm (X Y : L) : traceForm L X Y = traceForm L Y X := by
  rw [traceForm_apply, traceForm_apply, trace_mul_comm]

theorem traceForm_lie (X Y Z : L) : traceForm L ⁅X, Y⁆ Z = -traceForm L Y ⁅X, Z⁆ := by
  rw [traceForm_apply, traceForm_apply, LieSubalgebra.coe_bracket, LieSubalgebra.coe_bracket,
    Ring.lie_def, Ring.lie_def]
  set x := (X : Matrix ι ι 𝕜)
  set y := (Y : Matrix ι ι 𝕜)
  set z := (Z : Matrix ι ι 𝕜)
  have e : trace (y * (z * x)) = trace (x * y * z) := by
    rw [← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  rw [Matrix.sub_mul, Matrix.mul_sub, trace_sub, trace_sub, e, Matrix.mul_assoc y x z,
    map_sub, map_sub]
  ring

end TraceForm

section Positivity

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem re_trace_conjTranspose_mul_self_pos {A : Matrix ι ι 𝕜} (hA : A ≠ 0) :
    0 < RCLike.re (trace (Aᴴ * A)) := by
  have e : RCLike.re (trace (Aᴴ * A)) = ∑ i, ∑ j, ‖A j i‖ ^ 2 := by
    simp only [trace, diag_apply, mul_apply, conjTranspose_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  rw [e]
  obtain ⟨j, i, hji⟩ : ∃ j i, A j i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hA (Matrix.ext hc)
  refine lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hji) 2) ?_
  calc ‖A j i‖ ^ 2 = ∑ j' ∈ {j}, ‖A j' i‖ ^ 2 := by simp
    _ ≤ ∑ j', ‖A j' i‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => sq_nonneg _
    _ = ∑ i' ∈ {i}, ∑ j', ‖A j' i'‖ ^ 2 := by simp
    _ ≤ ∑ i', ∑ j', ‖A j' i'‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ =>
          Finset.sum_nonneg fun _ _ => sq_nonneg _

end Positivity

section Cartan

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (L : LieSubalgebra ℝ (Matrix ι ι 𝕜))

def skewPart : Submodule ℝ L where
  carrier := {X | (X : Matrix ι ι 𝕜)ᴴ = -(X : Matrix ι ι 𝕜)}
  add_mem' {X Y} hX hY := by
    change ((X : Matrix ι ι 𝕜) + (Y : Matrix ι ι 𝕜))ᴴ = -((X : Matrix ι ι 𝕜) + (Y : Matrix ι ι 𝕜))
    rw [conjTranspose_add, hX, hY, neg_add]
  zero_mem' := by
    change (0 : Matrix ι ι 𝕜)ᴴ = -(0 : Matrix ι ι 𝕜)
    simp
  smul_mem' r X hX := by
    change (r • (X : Matrix ι ι 𝕜))ᴴ = -(r • (X : Matrix ι ι 𝕜))
    rw [conjTranspose_smul, star_trivial, hX, smul_neg]

def hermPart : Submodule ℝ L where
  carrier := {X | (X : Matrix ι ι 𝕜)ᴴ = (X : Matrix ι ι 𝕜)}
  add_mem' {X Y} hX hY := by
    change ((X : Matrix ι ι 𝕜) + (Y : Matrix ι ι 𝕜))ᴴ = ((X : Matrix ι ι 𝕜) + (Y : Matrix ι ι 𝕜))
    rw [conjTranspose_add, hX, hY]
  zero_mem' := by
    change (0 : Matrix ι ι 𝕜)ᴴ = (0 : Matrix ι ι 𝕜)
    simp
  smul_mem' r X hX := by
    change (r • (X : Matrix ι ι 𝕜))ᴴ = (r • (X : Matrix ι ι 𝕜))
    rw [conjTranspose_smul, star_trivial, hX]

variable {L}

theorem mem_skewPart {X : L} : X ∈ skewPart L ↔ (X : Matrix ι ι 𝕜)ᴴ = -(X : Matrix ι ι 𝕜) :=
  Iff.rfl

theorem mem_hermPart {X : L} : X ∈ hermPart L ↔ (X : Matrix ι ι 𝕜)ᴴ = (X : Matrix ι ι 𝕜) :=
  Iff.rfl

theorem isCompl_skewPart_hermPart (hstar : ∀ X ∈ L, Xᴴ ∈ L) :
    IsCompl (skewPart L) (hermPart L) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro X hk hp
    rw [mem_skewPart] at hk
    rw [mem_hermPart] at hp
    have h2 : (X : Matrix ι ι 𝕜) = -(X : Matrix ι ι 𝕜) := hp.symm.trans hk
    have h3 : (2 : ℝ) • (X : Matrix ι ι 𝕜) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h2]
      exact add_neg_cancel _
    exact Subtype.ext ((smul_eq_zero.1 h3).resolve_left two_ne_zero)
  · rw [codisjoint_iff, eq_top_iff]
    intro X _
    set Xs : L := ⟨(X : Matrix ι ι 𝕜)ᴴ, hstar _ X.2⟩
    refine Submodule.mem_sup.2 ⟨(1 / 2 : ℝ) • (X - Xs), ?_, (1 / 2 : ℝ) • (X + Xs), ?_, ?_⟩
    · rw [mem_skewPart]
      change ((1 / 2 : ℝ) • ((X : Matrix ι ι 𝕜) - (X : Matrix ι ι 𝕜)ᴴ))ᴴ =
        -((1 / 2 : ℝ) • ((X : Matrix ι ι 𝕜) - (X : Matrix ι ι 𝕜)ᴴ))
      rw [conjTranspose_smul, star_trivial, conjTranspose_sub, conjTranspose_conjTranspose,
        ← smul_neg, neg_sub]
    · rw [mem_hermPart]
      change ((1 / 2 : ℝ) • ((X : Matrix ι ι 𝕜) + (X : Matrix ι ι 𝕜)ᴴ))ᴴ =
        ((1 / 2 : ℝ) • ((X : Matrix ι ι 𝕜) + (X : Matrix ι ι 𝕜)ᴴ))
      rw [conjTranspose_smul, star_trivial, conjTranspose_add, conjTranspose_conjTranspose,
        add_comm]
    · apply Subtype.ext
      change (1 / 2 : ℝ) • ((X : Matrix ι ι 𝕜) - (X : Matrix ι ι 𝕜)ᴴ) +
        (1 / 2 : ℝ) • ((X : Matrix ι ι 𝕜) + (X : Matrix ι ι 𝕜)ᴴ) = X
      module

theorem traceForm_neg_of_mem_skewPart {X : L} (hX : X ∈ skewPart L) (h0 : X ≠ 0) :
    traceForm L X X < 0 := by
  rw [mem_skewPart] at hX
  have hX0 : (X : Matrix ι ι 𝕜) ≠ 0 := fun e => h0 (Subtype.ext e)
  have e : (X : Matrix ι ι 𝕜) * X = -((X : Matrix ι ι 𝕜)ᴴ * X) := by
    rw [hX, Matrix.neg_mul, neg_neg]
  rw [traceForm_apply, e, trace_neg, map_neg, neg_lt_zero]
  exact re_trace_conjTranspose_mul_self_pos hX0

theorem traceForm_pos_of_mem_hermPart {X : L} (hX : X ∈ hermPart L) (h0 : X ≠ 0) :
    0 < traceForm L X X := by
  rw [mem_hermPart] at hX
  have hX0 : (X : Matrix ι ι 𝕜) ≠ 0 := fun e => h0 (Subtype.ext e)
  rw [traceForm_apply]
  nth_rewrite 1 [← hX]
  exact re_trace_conjTranspose_mul_self_pos hX0

theorem traceForm_eq_zero_of_skew_herm {X Y : L} (hX : X ∈ skewPart L) (hY : Y ∈ hermPart L) :
    traceForm L X Y = 0 := by
  rw [mem_skewPart] at hX
  rw [mem_hermPart] at hY
  rw [traceForm_apply]
  set z := trace ((X : Matrix ι ι 𝕜) * (Y : Matrix ι ι 𝕜))
  have hz : star z = -z := by
    rw [← trace_conjTranspose, conjTranspose_mul, hX, hY, Matrix.mul_neg, trace_neg, trace_mul_comm]
  have h1 : RCLike.re (star z) = RCLike.re z := by
    rw [RCLike.star_def, RCLike.conj_re]
  rw [hz, map_neg] at h1
  linarith

theorem exists_signed_basis {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hB : ∀ x y, B x y = B y x) {s : ℝ} (hs : s * s = 1)
    (hpos : ∀ v : V, v ≠ 0 → 0 < s * B v v) :
    ∃ b : Module.Basis (Fin (Module.finrank ℝ V)) ℝ V,
      ∀ i j, B (b i) (b j) = if i = j then s else 0 := by
  have : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := B)
    ⟨fun x y => by rw [RingHom.id_apply]; exact hB x y⟩
  have hpos' : ∀ i, 0 < s * B (v i) (v i) := fun i => hpos _ (v.ne_zero i)
  set w : Fin (Module.finrank ℝ V) → ℝ := fun i => (Real.sqrt (s * B (v i) (v i)))⁻¹
  have hw : ∀ i, IsUnit (w i) := fun i =>
    (inv_ne_zero (Real.sqrt_pos.2 (hpos' i)).ne').isUnit
  refine ⟨v.isUnitSMul hw, fun i j => ?_⟩
  rw [Module.Basis.isUnitSMul_apply, Module.Basis.isUnitSMul_apply, map_smul, map_smul,
    LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
  split_ifs with hij
  · subst hij
    have hsq : Real.sqrt (s * B (v i) (v i)) ^ 2 = s * B (v i) (v i) := Real.sq_sqrt (hpos' i).le
    have hst : s * B (v i) (v i) ≠ 0 := (hpos' i).ne'
    have ht : B (v i) (v i) ≠ 0 := right_ne_zero_of_mul hst
    simp only [w]
    rw [← mul_assoc, ← sq, inv_pow, hsq, mul_inv, mul_assoc, inv_mul_cancel₀ ht, mul_one]
    exact inv_eq_of_mul_eq_one_right hs
  · rw [hv hij, mul_zero, mul_zero]

theorem exists_cartanBasis (hstar : ∀ X ∈ L, Xᴴ ∈ L) :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ L) (ε : Fin d → ℝ), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (∀ i j, traceForm L (b i) (b j) = if i = j then ε i else 0) ∧
      ∀ i, ε i = -1 → ((b i : Matrix ι ι 𝕜))ᴴ = -(b i : Matrix ι ι 𝕜) := by
  classical
  have : FiniteDimensional ℝ L := Module.Finite.of_injective
    ((L.incl : L →ₗ⁅ℝ⁆ Matrix ι ι 𝕜) : L →ₗ[ℝ] Matrix ι ι 𝕜) Subtype.val_injective
  have hc := isCompl_skewPart_hermPart hstar
  obtain ⟨bk, hbk⟩ := exists_signed_basis ((traceForm L).restrict (skewPart L))
    (fun x y => traceForm_symm (x : L) y) (s := -1) (by norm_num) (fun v hv => by
      have h0 : (v : L) ≠ 0 := fun e => hv (Subtype.ext e)
      have := traceForm_neg_of_mem_skewPart v.2 h0
      change 0 < _ * traceForm L (v : L) (v : L)
      linarith)
  obtain ⟨bp, hbp⟩ := exists_signed_basis ((traceForm L).restrict (hermPart L))
    (fun x y => traceForm_symm (x : L) y) (s := 1) (by norm_num) (fun v hv => by
      have h0 : (v : L) ≠ 0 := fun e => hv (Subtype.ext e)
      have := traceForm_pos_of_mem_hermPart v.2 h0
      change 0 < _ * traceForm L (v : L) (v : L)
      linarith)
  set e := Submodule.prodEquivOfIsCompl (skewPart L) (hermPart L) hc
  set b0 := (bk.prod bp).map e
  set f : Fin (Module.finrank ℝ (skewPart L)) ⊕ Fin (Module.finrank ℝ (hermPart L)) → L :=
    Sum.elim (fun i => (bk i : L)) (fun j => (bp j : L))
  have hb0 : ∀ x, b0 x = f x := by
    rintro (i | j)
    · simp [b0, e, f, Submodule.coe_prodEquivOfIsCompl']
    · simp [b0, e, f, Submodule.coe_prodEquivOfIsCompl']
  set ε0 : Fin (Module.finrank ℝ (skewPart L)) ⊕ Fin (Module.finrank ℝ (hermPart L)) → ℝ :=
    Sum.elim (fun _ => -1) (fun _ => 1)
  have horth : ∀ x y, traceForm L (b0 x) (b0 y) = if x = y then ε0 x else 0 := by
    intro x y
    rw [hb0, hb0]
    rcases x with i | i <;> rcases y with j | j
    · have := hbk i j
      change traceForm L _ _ = _ at this
      simp only [f, ε0, Sum.elim_inl, Sum.inl.injEq]
      exact this
    · simp only [f, ε0, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
      exact traceForm_eq_zero_of_skew_herm (bk i).2 (bp j).2
    · simp only [f, ε0, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
      rw [traceForm_symm]
      exact traceForm_eq_zero_of_skew_herm (bk j).2 (bp i).2
    · have := hbp i j
      change traceForm L _ _ = _ at this
      simp only [f, ε0, Sum.elim_inr, Sum.inr.injEq]
      exact this
  set σ := finSumFinEquiv (m := Module.finrank ℝ (skewPart L)) (n := Module.finrank ℝ (hermPart L))
  refine ⟨_, b0.reindex σ, ε0 ∘ σ.symm, fun i => ?_, fun i j => ?_, fun i hi => ?_⟩
  · rcases hx : σ.symm i with k | k <;> simp [ε0, hx]
  · rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, horth]
    simp only [Function.comp_apply, σ.symm.injective.eq_iff]
  · rw [Module.Basis.reindex_apply, hb0]
    simp only [Function.comp_apply] at hi
    rcases hx : σ.symm i with k | k
    · rw [hx] at hi
      simp only [f, Sum.elim_inl]
      exact (bk k).2
    · rw [hx] at hi
      simp [ε0] at hi
      norm_num at hi

end Cartan

section MaxCompact

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

def maxCompact (G : Subgroup (Matrix ι ι 𝕜)ˣ) : Subgroup G where
  carrier := {g | ((g : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) ∈ Matrix.unitaryGroup ι 𝕜}
  mul_mem' {a b} ha hb := by
    change ((a : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) * ((b : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) ∈
      Matrix.unitaryGroup ι 𝕜
    exact Submonoid.mul_mem _ ha hb
  one_mem' := by
    change ((1 : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) ∈ Matrix.unitaryGroup ι 𝕜
    rw [Units.val_one]
    exact Submonoid.one_mem _
  inv_mem' {a} ha := by
    change (((a : (Matrix ι ι 𝕜)ˣ)⁻¹ : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) ∈ Matrix.unitaryGroup ι 𝕜
    have hmul : ((a : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) *
        star ((a : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) = 1 := Matrix.mem_unitaryGroup_iff.1 ha
    rw [Units.inv_eq_of_mul_eq_one_right hmul]
    exact Unitary.star_mem ha

theorem mem_maxCompact {G : Subgroup (Matrix ι ι 𝕜)ˣ} {g : G} :
    g ∈ maxCompact G ↔ ((g : (Matrix ι ι 𝕜)ˣ) : Matrix ι ι 𝕜) ∈ Matrix.unitaryGroup ι 𝕜 :=
  Iff.rfl

theorem exp_mem_unitaryGroup {X : Matrix ι ι 𝕜} (hX : Xᴴ = -X) :
    NormedSpace.exp X ∈ Matrix.unitaryGroup ι 𝕜 := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hX,
    ← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl X)), neg_add_cancel,
    NormedSpace.exp_zero]

end MaxCompact

section Groups

open NormedSpace
open scoped Matrix.Norms.L2Operator

theorem isExpLieAlgebra_top {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] : IsExpLieAlgebra (⊤ : Subgroup 𝔸ˣ) (⊤ : Submodule ℝ 𝔸) where
  expUnit_mem _ _ := Subgroup.mem_top _
  exists_nhds := ⟨(expPartialHomeomorph ℝ 𝔸).source, (expPartialHomeomorph ℝ 𝔸).open_source,
    zero_mem_expPartialHomeomorph_source ℝ 𝔸, subset_rfl, fun _ _ _ => Submodule.mem_top⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem IsExpLieAlgebra.expG_smul_mem_maxCompact_real {G : Subgroup (Matrix ι ι ℝ)ˣ}
    {𝔤 : Submodule ℝ (Matrix ι ι ℝ)} (h : IsExpLieAlgebra G 𝔤) {X : 𝔤}
    (hX : (X : Matrix ι ι ℝ)ᴴ = -(X : Matrix ι ι ℝ)) (t : ℝ) :
    h.expG (t • X) ∈ maxCompact G := by
  rw [mem_maxCompact, IsExpLieAlgebra.coe_expG]
  apply exp_mem_unitaryGroup
  change (t • (X : Matrix ι ι ℝ))ᴴ = -(t • (X : Matrix ι ι ℝ))
  rw [conjTranspose_smul, star_trivial, hX, smul_neg]

theorem IsExpLieAlgebra.expG_smul_mem_maxCompact_complex {G : Subgroup (Matrix ι ι ℂ)ˣ}
    {𝔤 : Submodule ℝ (Matrix ι ι ℂ)} (h : IsExpLieAlgebra G 𝔤) {X : 𝔤}
    (hX : (X : Matrix ι ι ℂ)ᴴ = -(X : Matrix ι ι ℂ)) (t : ℝ) :
    h.expG (t • X) ∈ maxCompact G := by
  rw [mem_maxCompact, IsExpLieAlgebra.coe_expG]
  apply exp_mem_unitaryGroup
  change (t • (X : Matrix ι ι ℂ))ᴴ = -(t • (X : Matrix ι ι ℂ))
  rw [conjTranspose_smul, star_trivial, hX, smul_neg]

theorem IsExpLieAlgebra.exists_cartanData_real {G : Subgroup (Matrix ι ι ℝ)ˣ}
    {𝔤 : Submodule ℝ (Matrix ι ι ℝ)} (h : IsExpLieAlgebra G 𝔤) (hstar : ∀ X ∈ 𝔤, Xᴴ ∈ 𝔤) :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ h.lieSubalgebra) (ε : Fin d → ℝ),
      (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (∀ i j, traceForm h.lieSubalgebra (b i) (b j) = if i = j then ε i else 0) ∧
      ∀ i, ε i = -1 → ∀ t : ℝ, h.expG (t • h.ofLie (b i)) ∈ maxCompact G := by
  obtain ⟨d, b, ε, hε, horth, hskew⟩ := exists_cartanBasis (L := h.lieSubalgebra) hstar
  exact ⟨d, b, ε, hε, horth, fun i hi t => h.expG_smul_mem_maxCompact_real (hskew i hi) t⟩

theorem IsExpLieAlgebra.exists_cartanData_complex {G : Subgroup (Matrix ι ι ℂ)ˣ}
    {𝔤 : Submodule ℝ (Matrix ι ι ℂ)} (h : IsExpLieAlgebra G 𝔤) (hstar : ∀ X ∈ 𝔤, Xᴴ ∈ 𝔤) :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ h.lieSubalgebra) (ε : Fin d → ℝ),
      (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (∀ i j, traceForm h.lieSubalgebra (b i) (b j) = if i = j then ε i else 0) ∧
      ∀ i, ε i = -1 → ∀ t : ℝ, h.expG (t • h.ofLie (b i)) ∈ maxCompact G := by
  obtain ⟨d, b, ε, hε, horth, hskew⟩ := exists_cartanBasis (L := h.lieSubalgebra) hstar
  exact ⟨d, b, ε, hε, horth, fun i hi t => h.expG_smul_mem_maxCompact_complex (hskew i hi) t⟩

theorem conjTranspose_mem_indefiniteUnitaryLieAlgebra {p q : ℕ}
    {X : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hX : X ∈ indefiniteUnitaryLieAlgebra p q) :
    Xᴴ ∈ indefiniteUnitaryLieAlgebra p q := by
  rw [mem_indefiniteUnitaryLieAlgebra_iff] at hX ⊢
  have e : indefJ p q * (indefJ p q * X * indefJ p q) * indefJ p q = X := by
    simp only [← Matrix.mul_assoc, indefJ_mul_self, Matrix.one_mul]
    rw [Matrix.mul_assoc, indefJ_mul_self, Matrix.mul_one]
  rw [conjTranspose_conjTranspose, hX, Matrix.mul_neg, Matrix.neg_mul, neg_neg, e]

theorem mem_maxCompact_indefiniteUnitary {p q : ℕ} {g : indefiniteUnitaryGroup p q} :
    g ∈ maxCompact (indefiniteUnitaryGroup p q) ↔
      ((g : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) ∈
          Matrix.unitaryGroup (Fin p ⊕ Fin q) ℂ ∧
        ((g : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₂ = 0 ∧
        ((g : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₁ = 0 := by
  rw [mem_maxCompact]
  refine ⟨fun hu => ⟨hu, ?_⟩, fun h => h.1⟩
  set u := ((g : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
  have hG : uᴴ * indefJ p q * u = indefJ p q := g.2
  have h1 : u * uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.1 hu
  have hcomm : indefJ p q * u = u * indefJ p q := by
    calc indefJ p q * u = (u * uᴴ) * indefJ p q * u := by rw [h1, Matrix.one_mul]
      _ = u * (uᴴ * indefJ p q * u) := by simp only [Matrix.mul_assoc]
      _ = u * indefJ p q := by rw [hG]
  have hent : ∀ i j, indefJ p q i i * u i j = u i j * indefJ p q j j := by
    intro i j
    have := congrFun (congrFun hcomm i) j
    simpa [indefJ, diagonal_mul, mul_diagonal] using this
  refine ⟨?_, ?_⟩
  · ext i j
    have := hent (Sum.inl i) (Sum.inr j)
    simp only [indefJ, diagonal_apply_eq, Sum.elim_inl, Sum.elim_inr, one_mul, mul_neg,
      mul_one] at this
    simp only [toBlocks₁₂, of_apply, Matrix.zero_apply]
    linear_combination (1 / 2 : ℂ) * this
  · ext i j
    have := hent (Sum.inr i) (Sum.inl j)
    simp only [indefJ, diagonal_apply_eq, Sum.elim_inl, Sum.elim_inr, one_mul, neg_mul,
      mul_one] at this
    simp only [toBlocks₂₁, of_apply, Matrix.zero_apply]
    linear_combination (-1 / 2 : ℂ) * this

end Groups

end GroundTheory.Automorphic
