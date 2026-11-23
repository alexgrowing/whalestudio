import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStructure
import GroundTheory.AutomorphicForms.HarishChandraRegularity.CartanBasis

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace Matrix
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace AutomorphicForm

set_option linter.unusedSectionVars false

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

open scoped Classical

variable (K) in

def mixedTraceL : mixedSpace K →ₗ[ℝ] ℝ where
  toFun x := (∑ v, x.1 v) + ∑ v, (x.2 v).re
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Complex.add_re, Finset.sum_add_distrib]
    ring
  map_smul' r x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, Complex.real_smul,
      Complex.re_ofReal_mul, RingHom.id_apply, Finset.mul_sum, mul_add]

theorem mixedTraceL_apply (x : mixedSpace K) :
    mixedTraceL K x = (∑ v, x.1 v) + ∑ v, (x.2 v).re := rfl

theorem mixedTraceL_star (x : mixedSpace K) : mixedTraceL K (star x) = mixedTraceL K x := by
  simp [mixedTraceL_apply]

theorem mixedTraceL_star_mul_self (x : mixedSpace K) :
    mixedTraceL K (star x * x) = (∑ v, x.1 v ^ 2) + ∑ v, ‖x.2 v‖ ^ 2 := by
  simp only [mixedTraceL_apply, Prod.fst_mul, Prod.snd_mul, Prod.fst_star, Prod.snd_star,
    Pi.mul_apply, Pi.star_apply, star_trivial]
  congr 1
  · exact Finset.sum_congr rfl fun v _ => by ring
  · refine Finset.sum_congr rfl fun v _ => ?_
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]

theorem mixedTraceL_star_mul_self_nonneg (x : mixedSpace K) : 0 ≤ mixedTraceL K (star x * x) := by
  rw [mixedTraceL_star_mul_self]
  exact add_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem mixedTraceL_star_mul_self_pos {x : mixedSpace K} (hx : x ≠ 0) :
    0 < mixedTraceL K (star x * x) := by
  rw [mixedTraceL_star_mul_self]
  have p1 : 0 ≤ ∑ v, x.1 v ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have p2 : 0 ≤ ∑ v, ‖x.2 v‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_contra hle
  replace hle := not_lt.1 hle
  have h1 : (∑ v, x.1 v ^ 2) = 0 := by linarith
  have h2 : (∑ v, ‖x.2 v‖ ^ 2) = 0 := by linarith
  apply hx
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · have := (Finset.sum_eq_zero_iff_of_nonneg fun v (_ : v ∈ Finset.univ) => sq_nonneg (x.1 v)).1
      h1 v (Finset.mem_univ v)
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  · have := (Finset.sum_eq_zero_iff_of_nonneg fun v (_ : v ∈ Finset.univ) =>
      sq_nonneg ‖x.2 v‖).1 h2 v (Finset.mem_univ v)
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)

theorem mixedTraceL_trace_conjTranspose_mul_self_pos {A : Matrix (Fin n) (Fin n) (mixedSpace K)}
    (hA : A ≠ 0) : 0 < mixedTraceL K (trace (Aᴴ * A)) := by
  have e : mixedTraceL K (trace (Aᴴ * A)) = ∑ i, ∑ j, mixedTraceL K (star (A j i) * A j i) := by
    simp only [trace, diag_apply, mul_apply, conjTranspose_apply, map_sum]
  rw [e]
  obtain ⟨j, i, hji⟩ : ∃ j i, A j i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hA (Matrix.ext hc)
  refine lt_of_lt_of_le (mixedTraceL_star_mul_self_pos hji) ?_
  calc mixedTraceL K (star (A j i) * A j i)
      = ∑ j' ∈ {j}, mixedTraceL K (star (A j' i) * A j' i) := by simp
    _ ≤ ∑ j', mixedTraceL K (star (A j' i) * A j' i) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ =>
          mixedTraceL_star_mul_self_nonneg _
    _ = ∑ i' ∈ {i}, ∑ j', mixedTraceL K (star (A j' i') * A j' i') := by simp
    _ ≤ ∑ i', ∑ j', mixedTraceL K (star (A j' i') * A j' i') :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ =>
          Finset.sum_nonneg fun _ _ => mixedTraceL_star_mul_self_nonneg _

def mat (X : ArchMatrix K n) : Matrix (Fin n) (Fin n) (mixedSpace K) := X

@[simp] theorem mat_add (X Y : ArchMatrix K n) : mat (X + Y) = mat X + mat Y := rfl
@[simp] theorem mat_sub (X Y : ArchMatrix K n) : mat (X - Y) = mat X - mat Y := rfl
@[simp] theorem mat_neg (X : ArchMatrix K n) : mat (-X) = -mat X := rfl
@[simp] theorem mat_mul (X Y : ArchMatrix K n) : mat (X * Y) = mat X * mat Y := rfl
@[simp] theorem mat_smul (r : ℝ) (X : ArchMatrix K n) : mat (r • X) = r • mat X := rfl
@[simp] theorem mat_zero : mat (0 : ArchMatrix K n) = 0 := rfl
@[simp] theorem mat_one : mat (1 : ArchMatrix K n) = 1 := rfl

section Coe
variable (X Y : (isExpLieAlgebra K n).lieSubalgebra) (r : ℝ)
@[simp] theorem mat_coe_add : mat ((X + Y : (isExpLieAlgebra K n).lieSubalgebra) : ArchMatrix K n) =
    mat (X : ArchMatrix K n) + mat (Y : ArchMatrix K n) := rfl
@[simp] theorem mat_coe_sub : mat ((X - Y : (isExpLieAlgebra K n).lieSubalgebra) : ArchMatrix K n) =
    mat (X : ArchMatrix K n) - mat (Y : ArchMatrix K n) := rfl
@[simp] theorem mat_coe_smul : mat ((r • X : (isExpLieAlgebra K n).lieSubalgebra) : ArchMatrix K n) =
    r • mat (X : ArchMatrix K n) := rfl
@[simp] theorem mat_coe_zero :
    mat ((0 : (isExpLieAlgebra K n).lieSubalgebra) : ArchMatrix K n) = 0 := rfl
end Coe

theorem mat_injective : Function.Injective (mat : ArchMatrix K n → _) := fun _ _ h => h

theorem mem_lie (X : ArchMatrix K n) : X ∈ (isExpLieAlgebra K n).lieSubalgebra :=
  (isExpLieAlgebra K n).mem_lieSubalgebra.2 Submodule.mem_top

variable (K n) in

def archTraceForm : LinearMap.BilinForm ℝ (isExpLieAlgebra K n).lieSubalgebra :=
  LinearMap.mk₂ ℝ
    (fun X Y => mixedTraceL K (trace (mat (X : ArchMatrix K n) * mat (Y : ArchMatrix K n))))
    (fun X₁ X₂ Y => by simp [Matrix.add_mul, trace_add])
    (fun r X Y => by simp [trace_smul])
    (fun X Y₁ Y₂ => by simp [Matrix.mul_add, trace_add])
    (fun r X Y => by simp [trace_smul])

theorem archTraceForm_apply (X Y : (isExpLieAlgebra K n).lieSubalgebra) :
    archTraceForm K n X Y =
      mixedTraceL K (trace (mat (X : ArchMatrix K n) * mat (Y : ArchMatrix K n))) := rfl

theorem archTraceForm_symm (X Y : (isExpLieAlgebra K n).lieSubalgebra) :
    archTraceForm K n X Y = archTraceForm K n Y X := by
  rw [archTraceForm_apply, archTraceForm_apply, trace_mul_comm]

theorem mat_coe_bracket (X Y : (isExpLieAlgebra K n).lieSubalgebra) :
    mat ((⁅X, Y⁆ : (isExpLieAlgebra K n).lieSubalgebra) : ArchMatrix K n) =
      mat (X : ArchMatrix K n) * mat (Y : ArchMatrix K n) -
        mat (Y : ArchMatrix K n) * mat (X : ArchMatrix K n) := by
  rw [LieSubalgebra.coe_bracket, Ring.lie_def]
  rfl

theorem archTraceForm_lie (X Y Z : (isExpLieAlgebra K n).lieSubalgebra) :
    archTraceForm K n ⁅X, Y⁆ Z = -archTraceForm K n Y ⁅X, Z⁆ := by
  rw [archTraceForm_apply, archTraceForm_apply, mat_coe_bracket, mat_coe_bracket]
  set x := mat (X : ArchMatrix K n)
  set y := mat (Y : ArchMatrix K n)
  set z := mat (Z : ArchMatrix K n)
  have e : trace (y * (z * x)) = trace (x * y * z) := by
    rw [← Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc]
  rw [Matrix.sub_mul, Matrix.mul_sub, trace_sub, trace_sub, e, Matrix.mul_assoc y x z,
    map_sub, map_sub]
  ring

variable (K n) in

def archSkew : Submodule ℝ (isExpLieAlgebra K n).lieSubalgebra where
  carrier := {X | (mat (X : ArchMatrix K n))ᴴ = -mat (X : ArchMatrix K n)}
  add_mem' {X Y} hX hY := by
    simp only [Set.mem_ofPred_eq, mat_coe_add] at hX hY ⊢
    rw [conjTranspose_add, hX, hY, neg_add]
  zero_mem' := by simp
  smul_mem' r X hX := by
    simp only [Set.mem_ofPred_eq, mat_coe_smul] at hX ⊢
    rw [conjTranspose_smul, star_trivial, hX, smul_neg]

variable (K n) in

def archHerm : Submodule ℝ (isExpLieAlgebra K n).lieSubalgebra where
  carrier := {X | (mat (X : ArchMatrix K n))ᴴ = mat (X : ArchMatrix K n)}
  add_mem' {X Y} hX hY := by
    simp only [Set.mem_ofPred_eq, mat_coe_add] at hX hY ⊢
    rw [conjTranspose_add, hX, hY]
  zero_mem' := by simp
  smul_mem' r X hX := by
    simp only [Set.mem_ofPred_eq, mat_coe_smul] at hX ⊢
    rw [conjTranspose_smul, star_trivial, hX]

theorem mem_archSkew {X : (isExpLieAlgebra K n).lieSubalgebra} :
    X ∈ archSkew K n ↔ (mat (X : ArchMatrix K n))ᴴ = -mat (X : ArchMatrix K n) := Iff.rfl

theorem mem_archHerm {X : (isExpLieAlgebra K n).lieSubalgebra} :
    X ∈ archHerm K n ↔ (mat (X : ArchMatrix K n))ᴴ = mat (X : ArchMatrix K n) := Iff.rfl

def lieStar (X : (isExpLieAlgebra K n).lieSubalgebra) : (isExpLieAlgebra K n).lieSubalgebra :=
  ⟨(mat (X : ArchMatrix K n))ᴴ, mem_lie _⟩

@[simp] theorem mat_lieStar (X : (isExpLieAlgebra K n).lieSubalgebra) :
    mat ((lieStar X : (isExpLieAlgebra K n).lieSubalgebra) : ArchMatrix K n) =
      (mat (X : ArchMatrix K n))ᴴ := rfl

theorem isCompl_archSkew_archHerm : IsCompl (archSkew K n) (archHerm K n) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro X hk hp
    rw [mem_archSkew] at hk
    rw [mem_archHerm] at hp
    have h2 : mat (X : ArchMatrix K n) = -mat (X : ArchMatrix K n) := hp.symm.trans hk
    have h3 : (2 : ℝ) • mat (X : ArchMatrix K n) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h2]
      exact add_neg_cancel _
    exact Subtype.ext (mat_injective ((smul_eq_zero.1 h3).resolve_left two_ne_zero))
  · rw [codisjoint_iff, eq_top_iff]
    intro X _
    refine Submodule.mem_sup.2 ⟨(1 / 2 : ℝ) • (X - lieStar X), ?_, (1 / 2 : ℝ) • (X + lieStar X),
      ?_, ?_⟩
    · rw [mem_archSkew]
      simp only [mat_coe_smul, mat_coe_sub, mat_lieStar]
      rw [conjTranspose_smul, star_trivial, conjTranspose_sub, conjTranspose_conjTranspose,
        ← smul_neg, neg_sub]
    · rw [mem_archHerm]
      simp only [mat_coe_smul, mat_coe_add, mat_lieStar]
      rw [conjTranspose_smul, star_trivial, conjTranspose_add, conjTranspose_conjTranspose,
        add_comm]
    · apply Subtype.ext
      apply mat_injective
      simp only [mat_coe_add, mat_coe_smul, mat_coe_sub, mat_lieStar]
      module

theorem archTraceForm_neg_of_mem_archSkew {X : (isExpLieAlgebra K n).lieSubalgebra}
    (hX : X ∈ archSkew K n) (h0 : X ≠ 0) : archTraceForm K n X X < 0 := by
  rw [mem_archSkew] at hX
  have hX0 : mat (X : ArchMatrix K n) ≠ 0 := fun e => h0 (Subtype.ext (mat_injective e))
  have e : mat (X : ArchMatrix K n) * mat (X : ArchMatrix K n) =
      -((mat (X : ArchMatrix K n))ᴴ * mat (X : ArchMatrix K n)) := by
    rw [hX, Matrix.neg_mul, neg_neg]
  rw [archTraceForm_apply, e, trace_neg, map_neg, neg_lt_zero]
  exact mixedTraceL_trace_conjTranspose_mul_self_pos hX0

theorem archTraceForm_pos_of_mem_archHerm {X : (isExpLieAlgebra K n).lieSubalgebra}
    (hX : X ∈ archHerm K n) (h0 : X ≠ 0) : 0 < archTraceForm K n X X := by
  rw [mem_archHerm] at hX
  have hX0 : mat (X : ArchMatrix K n) ≠ 0 := fun e => h0 (Subtype.ext (mat_injective e))
  rw [archTraceForm_apply]
  nth_rewrite 1 [← hX]
  exact mixedTraceL_trace_conjTranspose_mul_self_pos hX0

theorem archTraceForm_eq_zero_of_skew_herm {X Y : (isExpLieAlgebra K n).lieSubalgebra}
    (hX : X ∈ archSkew K n) (hY : Y ∈ archHerm K n) : archTraceForm K n X Y = 0 := by
  rw [mem_archSkew] at hX
  rw [mem_archHerm] at hY
  rw [archTraceForm_apply]
  set z := trace (mat (X : ArchMatrix K n) * mat (Y : ArchMatrix K n))
  have hz : star z = -z := by
    rw [← trace_conjTranspose, conjTranspose_mul, hX, hY, Matrix.mul_neg, trace_neg,
      trace_mul_comm]
  have h1 : mixedTraceL K (star z) = mixedTraceL K z := mixedTraceL_star z
  rw [hz, map_neg] at h1
  linarith

theorem exists_archCartanBasis :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra) (ε : Fin d → ℝ),
      (∀ i, ε i = 1 ∨ ε i = -1) ∧
      (∀ i j, archTraceForm K n (b i) (b j) = if i = j then ε i else 0) ∧
      ∀ i, ε i = -1 → b i ∈ archSkew K n := by
  classical
  have : FiniteDimensional ℝ (isExpLieAlgebra K n).lieSubalgebra :=
    FiniteDimensional.finiteDimensional_submodule
      ((isExpLieAlgebra K n).lieSubalgebra.toSubmodule)
  have hc := isCompl_archSkew_archHerm (K := K) (n := n)
  obtain ⟨bk, hbk⟩ := exists_signed_basis ((archTraceForm K n).restrict (archSkew K n))
    (fun x y => archTraceForm_symm (x : (isExpLieAlgebra K n).lieSubalgebra) y) (s := -1)
    (by norm_num) (fun v hv => by
      have h0 : (v : (isExpLieAlgebra K n).lieSubalgebra) ≠ 0 := fun e => hv (Subtype.ext e)
      have := archTraceForm_neg_of_mem_archSkew v.2 h0
      change 0 < _ * archTraceForm K n (v : (isExpLieAlgebra K n).lieSubalgebra) v
      linarith)
  obtain ⟨bp, hbp⟩ := exists_signed_basis ((archTraceForm K n).restrict (archHerm K n))
    (fun x y => archTraceForm_symm (x : (isExpLieAlgebra K n).lieSubalgebra) y) (s := 1)
    (by norm_num) (fun v hv => by
      have h0 : (v : (isExpLieAlgebra K n).lieSubalgebra) ≠ 0 := fun e => hv (Subtype.ext e)
      have := archTraceForm_pos_of_mem_archHerm v.2 h0
      change 0 < _ * archTraceForm K n (v : (isExpLieAlgebra K n).lieSubalgebra) v
      linarith)
  set e := Submodule.prodEquivOfIsCompl (archSkew K n) (archHerm K n) hc
  set b0 := (bk.prod bp).map e
  set f : Fin (Module.finrank ℝ (archSkew K n)) ⊕ Fin (Module.finrank ℝ (archHerm K n)) →
      (isExpLieAlgebra K n).lieSubalgebra :=
    Sum.elim (fun i => (bk i : (isExpLieAlgebra K n).lieSubalgebra))
      (fun j => (bp j : (isExpLieAlgebra K n).lieSubalgebra))
  have hb0 : ∀ x, b0 x = f x := by
    rintro (i | j)
    · simp [b0, e, f, Submodule.coe_prodEquivOfIsCompl']
    · simp [b0, e, f, Submodule.coe_prodEquivOfIsCompl']
  set ε0 : Fin (Module.finrank ℝ (archSkew K n)) ⊕ Fin (Module.finrank ℝ (archHerm K n)) → ℝ :=
    Sum.elim (fun _ => -1) (fun _ => 1)
  have horth : ∀ x y, archTraceForm K n (b0 x) (b0 y) = if x = y then ε0 x else 0 := by
    intro x y
    rw [hb0, hb0]
    rcases x with i | i <;> rcases y with j | j
    · have := hbk i j
      change archTraceForm K n _ _ = _ at this
      simp only [f, ε0, Sum.elim_inl, Sum.inl.injEq]
      exact this
    · simp only [f, ε0, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
      exact archTraceForm_eq_zero_of_skew_herm (bk i).2 (bp j).2
    · simp only [f, ε0, Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
      rw [archTraceForm_symm]
      exact archTraceForm_eq_zero_of_skew_herm (bk j).2 (bp i).2
    · have := hbp i j
      change archTraceForm K n _ _ = _ at this
      simp only [f, ε0, Sum.elim_inr, Sum.inr.injEq]
      exact this
  set σ := finSumFinEquiv (m := Module.finrank ℝ (archSkew K n))
    (n := Module.finrank ℝ (archHerm K n))
  refine ⟨_, b0.reindex σ, ε0 ∘ σ.symm, fun i => ?_, fun i j => ?_, fun i hi => ?_⟩
  · rcases hx : σ.symm i with k | k <;> simp [ε0, hx]
  · rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, horth]
    simp only [Function.comp_apply, σ.symm.injective.eq_iff]
  · rw [Module.Basis.reindex_apply, hb0]
    simp only [Function.comp_apply] at hi
    rcases hx : σ.symm i with k | k
    · simp only [f, Sum.elim_inl]
      exact (bk k).2
    · rw [hx] at hi
      simp [ε0] at hi
      norm_num at hi

def matHom : ArchMatrix K n →+* Matrix (Fin n) (Fin n) (mixedSpace K) where
  toFun := mat
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem matHom_apply (X : ArchMatrix K n) : matHom X = mat X := rfl

theorem continuous_matHom : Continuous (matHom : ArchMatrix K n →+* _) := continuous_id

def realComp (v : {w : InfinitePlace K // IsReal w}) : mixedSpace K →+* ℝ :=
  (Pi.evalRingHom _ v).comp (RingHom.fst _ _)

def complexComp (v : {w : InfinitePlace K // IsComplex w}) : mixedSpace K →+* ℂ :=
  (Pi.evalRingHom _ v).comp (RingHom.snd _ _)

@[simp] theorem realComp_apply (v : {w : InfinitePlace K // IsReal w}) (x : mixedSpace K) :
    realComp v x = x.1 v := rfl

@[simp] theorem complexComp_apply (v : {w : InfinitePlace K // IsComplex w}) (x : mixedSpace K) :
    complexComp v x = x.2 v := rfl

theorem continuous_realComp (v : {w : InfinitePlace K // IsReal w}) :
    Continuous (realComp (K := K) v) := (continuous_apply v).comp continuous_fst

theorem continuous_complexComp (v : {w : InfinitePlace K // IsComplex w}) :
    Continuous (complexComp (K := K) v) := (continuous_apply v).comp continuous_snd

def realCompM (v : {w : InfinitePlace K // IsReal w}) : ArchMatrix K n →+* Matrix (Fin n) (Fin n) ℝ :=
  (RingHom.mapMatrix (realComp v)).comp matHom

def complexCompM (v : {w : InfinitePlace K // IsComplex w}) :
    ArchMatrix K n →+* Matrix (Fin n) (Fin n) ℂ :=
  (RingHom.mapMatrix (complexComp v)).comp matHom

@[simp] theorem realCompM_apply (v : {w : InfinitePlace K // IsReal w}) (X : ArchMatrix K n) :
    realCompM v X = (mat X).map (realComp v) := rfl

@[simp] theorem complexCompM_apply (v : {w : InfinitePlace K // IsComplex w}) (X : ArchMatrix K n) :
    complexCompM v X = (mat X).map (complexComp v) := rfl

theorem continuous_realCompM (v : {w : InfinitePlace K // IsReal w}) :
    Continuous (realCompM (K := K) (n := n) v) :=
  (continuous_id.matrix_map (continuous_realComp v)).comp continuous_matHom

theorem continuous_complexCompM (v : {w : InfinitePlace K // IsComplex w}) :
    Continuous (complexCompM (K := K) (n := n) v) :=
  (continuous_id.matrix_map (continuous_complexComp v)).comp continuous_matHom

theorem realCompM_smul (v : {w : InfinitePlace K // IsReal w}) (c : ℝ) (X : ArchMatrix K n) :
    realCompM v (c • X) = c • realCompM v X := by
  ext i j
  rfl

theorem complexCompM_smul (v : {w : InfinitePlace K // IsComplex w}) (c : ℝ) (X : ArchMatrix K n) :
    complexCompM v (c • X) = c • complexCompM v X := by
  ext i j
  rfl

theorem realCompM_exp (v : {w : InfinitePlace K // IsReal w}) (Y : ArchMatrix K n) :
    realCompM v (NormedSpace.exp Y) = NormedSpace.exp (realCompM v Y) := by
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) Y).map (realCompM v)
    (continuous_realCompM v)
  rw [congrFun (NormedSpace.exp_eq_tsum (𝔸 := Matrix (Fin n) (Fin n) ℝ) ℝ) (realCompM v Y)]
  refine (HasSum.tsum_eq ?_).symm
  have e : (⇑(realCompM v) ∘ fun k : ℕ => ((k.factorial : ℝ))⁻¹ • Y ^ k) =
      fun k : ℕ => ((k.factorial : ℝ))⁻¹ • realCompM v Y ^ k := by
    funext k
    simp only [Function.comp_apply, realCompM_smul, map_pow]
  rw [e] at h
  exact h

theorem complexCompM_exp (v : {w : InfinitePlace K // IsComplex w}) (Y : ArchMatrix K n) :
    complexCompM v (NormedSpace.exp Y) = NormedSpace.exp (complexCompM v Y) := by
  have h := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) Y).map (complexCompM v)
    (continuous_complexCompM v)
  rw [congrFun (NormedSpace.exp_eq_tsum (𝔸 := Matrix (Fin n) (Fin n) ℂ) ℝ) (complexCompM v Y)]
  refine (HasSum.tsum_eq ?_).symm
  have e : (⇑(complexCompM v) ∘ fun k : ℕ => ((k.factorial : ℝ))⁻¹ • Y ^ k) =
      fun k : ℕ => ((k.factorial : ℝ))⁻¹ • complexCompM v Y ^ k := by
    funext k
    simp only [Function.comp_apply, complexCompM_smul, map_pow]
  rw [e] at h
  exact h

theorem realCompM_exp_mem_unitaryGroup {Y : ArchMatrix K n} (hY : (mat Y)ᴴ = -mat Y)
    (v : {w : InfinitePlace K // IsReal w}) :
    realCompM v (NormedSpace.exp Y) ∈ unitaryGroup (Fin n) ℝ := by
  rw [realCompM_exp]
  apply exp_mem_unitaryGroup
  rw [realCompM_apply, ← conjTranspose_map (⇑(realComp v)) (fun x => rfl), hY,
    Matrix.map_neg _ (fun a => map_neg _ a)]

theorem complexCompM_exp_mem_unitaryGroup {Y : ArchMatrix K n} (hY : (mat Y)ᴴ = -mat Y)
    (v : {w : InfinitePlace K // IsComplex w}) :
    complexCompM v (NormedSpace.exp Y) ∈ unitaryGroup (Fin n) ℂ := by
  rw [complexCompM_exp]
  apply exp_mem_unitaryGroup
  rw [complexCompM_apply, ← conjTranspose_map (⇑(complexComp v)) (fun x => rfl), hY,
    Matrix.map_neg _ (fun a => map_neg _ a)]

theorem infAt_infEmb_apply (x : archGroup K n) (w : InfinitePlace K) (a b : Fin n) :
    Reduction.infAt w (infEmb K n x) a b =
      (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
        (mat ((x : (ArchMatrix K n)ˣ) : ArchMatrix K n) a b) w := by
  show (AdelicGLn.infiniteEquiv K n (AdelicGLn.prodEquiv K n (infEmb K n x)).1) w a b = _
  rw [prodEquiv_infEmb]
  rfl

theorem extensionEmbeddingOfIsReal_symm (z : mixedSpace K) {w : InfinitePlace K} (hw : IsReal w) :
    InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z w) = z.1 ⟨w, hw⟩ := by
  have := InfiniteAdeleRing.ringEquiv_mixedSpace_apply K
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z)
  rw [RingEquiv.apply_symm_apply] at this
  exact (congrArg (fun p : mixedSpace K => p.1 ⟨w, hw⟩) this).symm

theorem extensionEmbedding_symm (z : mixedSpace K) {w : InfinitePlace K} (hw : IsComplex w) :
    InfinitePlace.Completion.extensionEmbedding w
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z w) = z.2 ⟨w, hw⟩ := by
  have := InfiniteAdeleRing.ringEquiv_mixedSpace_apply K
    ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm z)
  rw [RingEquiv.apply_symm_apply] at this
  exact (congrArg (fun p : mixedSpace K => p.2 ⟨w, hw⟩) this).symm

open Reduction in

theorem expG_mem_archCompact_of_skew (Z : archLie K n)
    (hZ : (mat (Z : ArchMatrix K n))ᴴ = -mat (Z : ArchMatrix K n)) :
    (isExpLieAlgebra K n).expG Z ∈ archCompact K n := by
  set x := (isExpLieAlgebra K n).expG Z
  have hx : ((x : (ArchMatrix K n)ˣ) : ArchMatrix K n) = NormedSpace.exp (Z : ArchMatrix K n) :=
    IsExpLieAlgebra.coe_expG _ Z
  show infEmb K n x ∈ Reduction.maxCompact (K := K) (n := n)
  refine ⟨fun w => ?_, fun v => ?_⟩
  · intro y
    by_cases hw : w.IsReal
    · set ψ := InfinitePlace.Completion.extensionEmbeddingOfIsReal hw
      have hψ : ∀ z, ‖ψ z‖ = ‖z‖ := fun z =>
        (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
          (map_zero _) z
      have hU := realCompM_exp_mem_unitaryGroup hZ ⟨w, hw⟩
      rw [← hx] at hU
      rw [← euclidNorm_map ψ hψ, ← euclidNorm_map ψ hψ y]
      have e : (fun i => ψ ((y ᵥ* (infAt w (infEmb K n x) :
          Matrix (Fin n) (Fin n) w.Completion)) i)) =
          (fun i => ψ (y i)) ᵥ* realCompM ⟨w, hw⟩ ((x : (ArchMatrix K n)ˣ) : ArchMatrix K n) := by
        ext j
        simp only [vecMul, dotProduct, map_sum, map_mul, realCompM_apply, Matrix.map_apply,
          realComp_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [infAt_infEmb_apply, extensionEmbeddingOfIsReal_symm]
      rw [e, euclidNorm_vecMul_unitary hU]
    · have hc := InfinitePlace.not_isReal_iff_isComplex.1 hw
      set ψ := InfinitePlace.Completion.extensionEmbedding w
      have hψ : ∀ z, ‖ψ z‖ = ‖z‖ := fun z =>
        (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
          (map_zero _) z
      have hU := complexCompM_exp_mem_unitaryGroup hZ ⟨w, hc⟩
      rw [← hx] at hU
      rw [← euclidNorm_map ψ hψ, ← euclidNorm_map ψ hψ y]
      have e : (fun i => ψ ((y ᵥ* (infAt w (infEmb K n x) :
          Matrix (Fin n) (Fin n) w.Completion)) i)) =
          (fun i => ψ (y i)) ᵥ* complexCompM ⟨w, hc⟩ ((x : (ArchMatrix K n)ˣ) : ArchMatrix K n) := by
        ext j
        simp only [vecMul, dotProduct, map_sum, map_mul, complexCompM_apply, Matrix.map_apply,
          complexComp_apply]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [infAt_infEmb_apply, extensionEmbedding_symm _ hc]
      rw [e, euclidNorm_vecMul_unitary hU]
  · have : finAt v (infEmb K n x) = 1 := by
      show (AdelicGLn.finiteRestrictedEquiv K n (AdelicGLn.prodEquiv K n (infEmb K n x)).2) v = 1
      rw [prodEquiv_infEmb, map_one]
      rfl
    rw [this]
    exact one_mem _

variable (K n) in

theorem exists_archCartanData :
    ∃ (d : ℕ) (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra) (ε : Fin d → ℝ)
      (B : LinearMap.BilinForm ℝ (isExpLieAlgebra K n).lieSubalgebra),
      (∀ i, ε i = 1 ∨ ε i = -1) ∧ (∀ i j, B (b i) (b j) = if i = j then ε i else 0) ∧
      (∀ X Y : (isExpLieAlgebra K n).lieSubalgebra, B X Y = B Y X) ∧
      (∀ X Y Z : (isExpLieAlgebra K n).lieSubalgebra, B ⁅X, Y⁆ Z = -B Y ⁅X, Z⁆) ∧
      ∀ i, ε i = -1 → ∀ t : ℝ,
        (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie (b i)) ∈ archCompact K n := by
  obtain ⟨d, b, ε, hε, horth, hskew⟩ := exists_archCartanBasis (K := K) (n := n)
  refine ⟨d, b, ε, archTraceForm K n, hε, horth, archTraceForm_symm, archTraceForm_lie,
    fun i hi t => expG_mem_archCompact_of_skew _ ?_⟩
  have h := hskew i hi
  rw [mem_archSkew] at h
  show (t • mat (b i : ArchMatrix K n))ᴴ = -(t • mat (b i : ArchMatrix K n))
  rw [conjTranspose_smul, star_trivial, h, smul_neg]

end AutomorphicForm

end

end GroundTheory.Automorphic
