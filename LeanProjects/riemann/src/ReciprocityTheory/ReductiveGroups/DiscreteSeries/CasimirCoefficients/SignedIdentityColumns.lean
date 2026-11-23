import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedEmbeddingToM

noncomputable section

open Finset MeasureTheory Matrix Topology Metric Kronecker
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

abbrev SgIxV (ε : Fin n → Bool) (s : Bool) : Type := {a : Fin n // ε a = s}

lemma hs_contVG : Continuous (hs : Matrix (Fin n) (Fin n) ℂ → ℝ) := by
  unfold hs
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    (continuous_id.matrix_elem i j).norm.pow 2

lemma hs_nonnegVG (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs A := by
  unfold hs
  positivity

lemma hs_entry_leVG (g : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖g i j‖ ^ 2 ≤ hs g := by
  unfold hs
  calc ‖g i j‖ ^ 2 ≤ ∑ j', ‖g i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖g i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖g i' j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖g i' j'‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ i)

lemma hs_oneVG (n : ℕ) : hs (1 : Matrix (Fin n) (Fin n) ℂ) = n := by
  simp [hs, Matrix.one_apply, apply_ite]

lemma toM_mulVG {ε : Fin n → Bool} (g h : UJ ε) : toM (g * h) = toM g * toM h := rfl

lemma toM_mul_invVG {ε : Fin n → Bool} (g : UJ ε) : toM g * toM g⁻¹ = 1 := by
  unfold toM
  rw [Subgroup.coe_inv, Units.mul_inv]

private lemma Jm_mul_self_eq_one' (ε : Fin n → Bool) : Jm ε * Jm ε = 1 := by
  unfold Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

lemma gJgH_VG {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : g * Jm ε * gᴴ = Jm ε := by
  have hJ := Jm_mul_self_eq_one' ε
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have h1 : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', hJ]
  have h2 : g * (Jm ε * gᴴ * Jm ε) = 1 := mul_eq_one_comm.mp h1
  calc g * Jm ε * gᴴ = g * (Jm ε * gᴴ * Jm ε) * Jm ε := by
        simp only [Matrix.mul_assoc, hJ, Matrix.mul_one]
    _ = Jm ε := by rw [h2, Matrix.one_mul]

lemma normSq_detVG {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    Complex.normSq g.det = 1 := by
  have hJ := Jm_mul_self_eq_one' ε
  have hJ0 : (Jm ε).det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hJ
    rw [Matrix.det_mul, Matrix.det_one, h0, zero_mul] at h1
    exact zero_ne_one h1
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hdet := congrArg Matrix.det hg'
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at hdet
  have h2 : star g.det * g.det = 1 := by
    apply mul_right_cancel₀ hJ0
    calc star g.det * g.det * (Jm ε).det = star g.det * (Jm ε).det * g.det := by ring
      _ = (Jm ε).det := hdet
      _ = 1 * (Jm ε).det := by ring
  have h3 : ((Complex.normSq g.det : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    exact h2
  exact_mod_cast h3

section supnorm
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

lemma ballFiniteVG (ε : Fin n → Bool) (ν : Measure (UJ ε)) [ν.IsHaarMeasure] (R : ℝ) :
    ν {g | hs (toM g) ≤ R} < ⊤ := by
  classical
  have hJ := Jm_mul_self_eq_one' ε
  let K : Set (Matrix (Fin n) (Fin n) ℂ) := {M | inUJ ε M ∧ hs M ≤ R}
  have hKc : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · apply IsClosed.inter
      · exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
          continuous_id) continuous_const
      · exact isClosed_le hs_contVG continuous_const
    · rw [isBounded_iff_forall_norm_le]
      refine ⟨max 1 R, fun M hM => ?_⟩
      rw [Matrix.norm_le_iff (le_trans zero_le_one (le_max_left _ _))]
      intro i j
      have h1 := le_trans (hs_entry_leVG M i j) hM.2
      have h0 := norm_nonneg (M i j)
      by_cases hc : ‖M i j‖ ≤ 1
      · exact le_trans hc (le_max_left _ _)
      · push_neg at hc
        have : ‖M i j‖ ≤ ‖M i j‖ ^ 2 := by nlinarith
        exact le_trans (le_trans this h1) (le_max_right _ _)
  let e : UJ ε → Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    fun g => Units.embedProduct _ (g : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  have he : Topology.IsInducing e :=
    Units.isEmbedding_embedProduct.isInducing.comp Topology.IsInducing.subtypeVal
  let ψ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    fun M => (M, MulOpposite.op (Jm ε * Mᴴ * Jm ε))
  have hψ : Continuous ψ :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))
  have hinv : ∀ M : Matrix (Fin n) (Fin n) ℂ, inUJ ε M →
      (Jm ε * Mᴴ * Jm ε) * M = 1 ∧ M * (Jm ε * Mᴴ * Jm ε) = 1 := by
    intro M hM
    have hM' : Mᴴ * Jm ε * M = Jm ε := hM
    have h1 : (Jm ε * Mᴴ * Jm ε) * M = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM', hJ]
    exact ⟨h1, mul_eq_one_comm.mp h1⟩
  have himg : e '' {g | hs (toM g) ≤ R} = ψ '' K := by
    ext p
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨toM g, ⟨g.2, hg⟩, ?_⟩
      have hinvg : (((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
          Matrix (Fin n) (Fin n) ℂ) = Jm ε * (toM g)ᴴ * Jm ε :=
        Units.inv_eq_of_mul_eq_one_right (hinv (toM g) g.2).2
      simp only [ψ, e, Units.embedProduct_apply, hinvg]
    · rintro ⟨M, ⟨hM, hR⟩, rfl⟩
      let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨M, Jm ε * Mᴴ * Jm ε, (hinv M hM).2, (hinv M hM).1⟩
      refine ⟨⟨u, hM⟩, hR, ?_⟩
      simp only [ψ, e, Units.embedProduct_apply]
      rfl
  have hS : IsCompact {g : UJ ε | hs (toM g) ≤ R} := by
    rw [he.isCompact_iff, himg]
    exact hKc.image hψ
  exact hS.measure_lt_top

end supnorm

def hsRV {Q : Type} [Fintype Q] (x : Matrix (Fin n) Q ℂ) : ℝ := ∑ i, ∑ j, ‖x i j‖ ^ 2

def signedIdentityColumns (ε : Fin n → Bool) (s : Bool) : Matrix (Fin n) (SgIxV ε s) ℂ := fun a b => if a = b.1 then 1 else 0

lemma hsRV_cont {Q : Type} [Fintype Q] : Continuous (hsRV : Matrix (Fin n) Q ℂ → ℝ) := by
  unfold hsRV
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    (continuous_id.matrix_elem i j).norm.pow 2

lemma hsRV_entry_le {Q : Type} [Fintype Q] (g : Matrix (Fin n) Q ℂ) (i : Fin n) (j : Q) : ‖g i j‖ ^ 2 ≤ hsRV g := by
  unfold hsRV
  calc ‖g i j‖ ^ 2 ≤ ∑ j', ‖g i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖g i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖g i' j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j', ‖g i' j'‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ i)

lemma mul_P0V_apply (ε : Fin n → Bool) (s : Bool) (g : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (b : SgIxV ε s) :
    (g * signedIdentityColumns ε s) i b = g i b.1 := by
  simp [Matrix.mul_apply, signedIdentityColumns]

lemma sum_SgIxV (ε : Fin n → Bool) (s : Bool) (f : Fin n → ℝ) :
    ∑ b : SgIxV ε s, f b.1 = ∑ j, if ε j = s then f j else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter fun j => ε j = s) (fun x => by simp) f).symm

lemma hsRV_P0V_le (ε : Fin n → Bool) (s : Bool) : hsRV (signedIdentityColumns ε s) ≤ n := by
  have h1 : hsRV (signedIdentityColumns ε s) = Fintype.card (SgIxV ε s) := by
    unfold hsRV signedIdentityColumns
    rw [Finset.sum_comm]
    simp [apply_ite]
  rw [h1]
  have h2 := Fintype.card_subtype_le (fun a : Fin n => ε a = s)
  have h3 : ((Fintype.card (SgIxV ε s) : ℕ) : ℝ) ≤ ((Fintype.card (Fin n) : ℕ) : ℝ) := by
    exact_mod_cast h2
  simpa using h3

lemma hs_le_colsV {ε : Fin n → Bool} (s : Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    hs g ≤ n + 2 * hsRV (g * signedIdentityColumns ε s) := by
  have h := gJgH_VG hg
  let σ : Fin n → ℝ := fun a => if ε a then 1 else -1
  have hJσ : Jm ε = Matrix.diagonal fun a => ((σ a : ℝ) : ℂ) := by
    unfold Jm
    congr 1
    funext a
    simp only [σ]
    split_ifs <;> simp
  have hterm : ∀ i j, g i j * ((σ j : ℝ) : ℂ) * star (g i j) = ((σ j * ‖g i j‖ ^ 2 : ℝ) : ℂ) := by
    intro i j
    rw [mul_comm (g i j), mul_assoc, Complex.star_def, Complex.mul_conj']
    push_cast
    ring
  have hrow : ∀ i, ∑ j, σ j * ‖g i j‖ ^ 2 = σ i := by
    intro i
    have h1 := congrFun (congrFun h i) i
    rw [hJσ, Matrix.mul_apply] at h1
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq, hterm] at h1
    exact_mod_cast h1
  have hcols : hsRV (g * signedIdentityColumns ε s) = ∑ i, ∑ j, if ε j = s then ‖g i j‖ ^ 2 else 0 := by
    unfold hsRV
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [mul_P0V_apply]
    exact sum_SgIxV ε s (fun j => ‖g i j‖ ^ 2)
  have hpt : ∀ i j, ‖g i j‖ ^ 2 = (if s then -1 else 1) * (σ j * ‖g i j‖ ^ 2) +
      2 * (if ε j = s then ‖g i j‖ ^ 2 else 0) := by
    intro i j
    by_cases h1 : ε j = true <;> cases s <;> simp [σ, h1] <;> ring
  have hσ : ∀ i, (if s then (-1:ℝ) else 1) * σ i ≤ 1 := by
    intro i
    by_cases h1 : ε i = true <;> cases s <;> simp [σ, h1]
  unfold hs
  rw [hcols]
  calc ∑ i, ∑ j, ‖g i j‖ ^ 2
      = ∑ i, ((if s then -1 else 1) * σ i + 2 * ∑ j, if ε j = s then ‖g i j‖ ^ 2 else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_congr rfl fun j _ => hpt i j, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, hrow i]
    _ ≤ ∑ i : Fin n, (1 + 2 * ∑ j, if ε j = s then ‖g i j‖ ^ 2 else 0) :=
        Finset.sum_le_sum fun i _ => by linarith [hσ i]
    _ = n + 2 * ∑ i, ∑ j, if ε j = s then ‖g i j‖ ^ 2 else 0 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
        simp

def LcV {Q : Type} [Fintype Q] (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) Q ℂ →ₗ[ℂ] Matrix (Fin n) Q ℂ where
  toFun x := g * x
  map_add' := Matrix.mul_add g
  map_smul' c x := by simp

lemma stdBasis_reprV {Q : Type} [Fintype Q] [DecidableEq Q] (x : Matrix (Fin n) Q ℂ) (i : Fin n) (j : Q) :
    (Matrix.stdBasis ℂ (Fin n) Q).repr x (i, j) = x i j := by
  first
    | rfl
    | (simp [Matrix.stdBasis]; done)
    | (simp [Matrix.stdBasis, Basis.reindex_repr, Pi.basis_repr]; done)

lemma LcV_det {Q : Type} [Fintype Q] [DecidableEq Q] (g : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det (LcV (Q := Q) g) = g.det ^ Fintype.card Q := by
  rw [← LinearMap.det_toMatrix (Matrix.stdBasis ℂ (Fin n) Q)]
  have h : LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin n) Q) (Matrix.stdBasis ℂ (Fin n) Q) (LcV (Q := Q) g) =
      Matrix.kroneckerMap (fun x1 x2 => x1 * x2) g (1 : Matrix Q Q ℂ) := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rw [LinearMap.toMatrix_apply, stdBasis_reprV, Matrix.stdBasis_eq_single]
    simp [LcV, Matrix.mul_apply, Matrix.single_apply, Matrix.one_apply]
    by_cases hlj : l = j
    · subst hlj
      simp
    · simp [hlj, Ne.symm hlj]
  rw [h, Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one]

abbrev REV (n : ℕ) (Q : Type) := Fin n → Q → ℂ

def ReV (n : ℕ) (Q : Type) : REV n Q ≃ₗ[ℝ] Matrix (Fin n) Q ℂ := Matrix.ofLinearEquiv ℝ

def RLV {Q : Type} [Fintype Q] (g : Matrix (Fin n) (Fin n) ℂ) : REV n Q →ₗ[ℝ] REV n Q :=
  ((ReV n Q).symm : Matrix (Fin n) Q ℂ →ₗ[ℝ] REV n Q) ∘ₗ ((LcV (Q := Q) g).restrictScalars ℝ) ∘ₗ
    ((ReV n Q : REV n Q ≃ₗ[ℝ] Matrix (Fin n) Q ℂ) : REV n Q →ₗ[ℝ] Matrix (Fin n) Q ℂ)

lemma RLV_apply {Q : Type} [Fintype Q] (g : Matrix (Fin n) (Fin n) ℂ) (x : REV n Q) :
    RLV g x = Matrix.of.symm (g * Matrix.of x) := rfl

lemma of_RLV {Q : Type} [Fintype Q] (A : Matrix (Fin n) (Fin n) ℂ) (x : REV n Q) :
    Matrix.of (RLV A x) = A * Matrix.of x := by
  rw [RLV_apply]
  exact Matrix.of.apply_symm_apply _

lemma RLV_det {Q : Type} [Fintype Q] [DecidableEq Q] {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : inUJ ε g) : LinearMap.det (RLV (Q := Q) g) = 1 := by
  have h1 : RLV (Q := Q) g = ((ReV n Q).symm : Matrix (Fin n) Q ℂ →ₗ[ℝ] REV n Q) ∘ₗ
      ((LcV (Q := Q) g).restrictScalars ℝ) ∘ₗ
      (((ReV n Q).symm).symm : REV n Q →ₗ[ℝ] Matrix (Fin n) Q ℂ) := rfl
  rw [h1, LinearMap.det_conj, LinearMap.det_restrictScalars, LcV_det, Algebra.norm_complex_apply, map_pow,
    normSq_detVG hg, one_pow]

section frob
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

lemma hs_eq_frobVG (A : Matrix (Fin n) (Fin n) ℂ) : hs A = ‖A‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  unfold hs
  simp only [Real.rpow_two]

lemma hsRV_eq {Q : Type} [Fintype Q] (A : Matrix (Fin n) Q ℂ) : hsRV A = ‖A‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  unfold hsRV
  simp only [Real.rpow_two]

lemma norm_P0V_le (ε : Fin n → Bool) (s : Bool) : ‖signedIdentityColumns ε s‖ ≤ Real.sqrt n := by
  exact le_trans (le_abs_self _) (Real.abs_le_sqrt (by rw [← hsRV_eq]; exact hsRV_P0V_le ε s))

lemma normRV_lt {Q : Type} [Fintype Q] {u : Matrix (Fin n) Q ℂ} (hu : hsRV u < 1 / 16) : ‖u‖ < 1 / 4 := by
  rw [hsRV_eq] at hu
  nlinarith [norm_nonneg u]

lemma normRV_u {ε : Fin n → Bool} {s : Bool} {u : Matrix (Fin n) (SgIxV ε s) ℂ} (hu : hsRV (u - signedIdentityColumns ε s) < 1 / 16) :
    ‖u‖ ≤ Real.sqrt n + 1 / 4 := by
  have h1 := normRV_lt hu
  have h2 := norm_P0V_le ε s
  calc ‖u‖ = ‖signedIdentityColumns ε s + (u - signedIdentityColumns ε s)‖ := by rw [add_sub_cancel]
    _ ≤ ‖signedIdentityColumns ε s‖ + ‖u - signedIdentityColumns ε s‖ := norm_add_le _ _
    _ ≤ Real.sqrt n + 1 / 4 := by linarith

lemma smallRV {ε : Fin n → Bool} {s : Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    {u v : Matrix (Fin n) (SgIxV ε s) ℂ} (hu : hsRV (u - signedIdentityColumns ε s) < 1 / 16) (hv : hsRV (v - signedIdentityColumns ε s) < 1 / 16)
    (h : k * u = v) : hs k ≤ n + 2 * (5 / 2 * Real.sqrt n + 1 / 2) ^ 2 := by
  have hk' := hs_le_colsV s hk
  have hw := normRV_lt hu
  have hvn := normRV_u hv
  have hr0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hr2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have e1 : k * signedIdentityColumns ε s = v - k * (u - signedIdentityColumns ε s) := by
    rw [Matrix.mul_sub, h]
    abel
  have ha : ‖k * signedIdentityColumns ε s‖ ≤ ‖v‖ + ‖k‖ * ‖u - signedIdentityColumns ε s‖ := by
    have m1 : ‖k * (u - signedIdentityColumns ε s)‖ ≤ ‖k‖ * ‖u - signedIdentityColumns ε s‖ := Matrix.frobenius_norm_mul k (u - signedIdentityColumns ε s)
    have m2 := norm_sub_le v (k * (u - signedIdentityColumns ε s))
    rw [e1]
    linarith
  have hK : ‖k‖ ^ 2 ≤ n + 2 * ‖k * signedIdentityColumns ε s‖ ^ 2 := by
    have h0 := hk'
    rw [hs_eq_frobVG k, hsRV_eq (k * signedIdentityColumns ε s)] at h0
    exact h0
  have hKn := norm_nonneg k
  have han := norm_nonneg (k * signedIdentityColumns ε s)
  have hKw : ‖k‖ * ‖u - signedIdentityColumns ε s‖ ≤ ‖k‖ * (1 / 4) := mul_le_mul_of_nonneg_left hw.le hKn
  have hb : ‖k * signedIdentityColumns ε s‖ ≤ 5 / 2 * Real.sqrt n + 1 / 2 := by
    by_contra hc
    push_neg at hc
    have h1 : ‖k * signedIdentityColumns ε s‖ ≤ Real.sqrt n + 1 / 4 + ‖k‖ / 4 := by linarith
    have h4 : 0 ≤ 4 * (‖k * signedIdentityColumns ε s‖ - (Real.sqrt n + 1 / 4)) := by linarith
    have h5 : 4 * (‖k * signedIdentityColumns ε s‖ - (Real.sqrt n + 1 / 4)) ≤ ‖k‖ := by linarith
    have h16 := mul_le_mul h5 h5 h4 hKn
    have hd : 0 ≤ ‖k * signedIdentityColumns ε s‖ - (5 / 2 * Real.sqrt n + 1 / 2) := by linarith
    nlinarith [sq_nonneg (‖k * signedIdentityColumns ε s‖ - (5 / 2 * Real.sqrt n + 1 / 2)), mul_nonneg hd hr0, sq_nonneg (Real.sqrt n)]
  rw [hsRV_eq (k * signedIdentityColumns ε s)] at hk'
  have hb2 : ‖k * signedIdentityColumns ε s‖ ^ 2 ≤ (5 / 2 * Real.sqrt n + 1 / 2) ^ 2 := pow_le_pow_left₀ han hb 2
  linarith

lemma entryRV {ε : Fin n → Bool} {s : Bool} {g : Matrix (Fin n) (Fin n) ℂ} {u : Matrix (Fin n) (SgIxV ε s) ℂ}
    {R : ℝ} (hR : 0 ≤ R) (hg : hs g ≤ R ^ 2) (hu : hsRV (u - signedIdentityColumns ε s) < 1 / 16) (i : Fin n) (j : SgIxV ε s) :
    ‖(g * u) i j‖ ≤ R * (Real.sqrt n + 1) := by
  have hw := normRV_u hu
  have hg' : ‖g‖ ≤ R := by
    rw [hs_eq_frobVG] at hg
    exact le_of_pow_le_pow_left₀ two_ne_zero hR hg
  have h1 : ‖(g * u) i j‖ ≤ ‖g * u‖ := by
    have h0 := hsRV_entry_le (g * u) i j
    rw [hsRV_eq] at h0
    exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) h0
  have h2 : ‖g * u‖ ≤ ‖g‖ * ‖u‖ := Matrix.frobenius_norm_mul _ _
  have h3 : ‖g‖ * ‖u‖ ≤ R * (Real.sqrt n + 1) := mul_le_mul hg' (by linarith) (norm_nonneg _) hR
  linarith

end frob

lemma O_bddRV {ε : Fin n → Bool} {s : Bool} {x : REV n (SgIxV ε s)} (hx : hsRV (Matrix.of x - signedIdentityColumns ε s) < 1 / 16) :
    x ∈ closedBall (0 : REV n (SgIxV ε s)) 2 := by
  rw [mem_closedBall_zero_iff]
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun j => ?_
  have h1 := hsRV_entry_le (Matrix.of x - signedIdentityColumns ε s) i j
  have h2 : ‖(Matrix.of x - signedIdentityColumns ε s) i j‖ < 1 / 4 := by
    nlinarith [norm_nonneg ((Matrix.of x - signedIdentityColumns ε s) i j)]
  have h3 : ‖signedIdentityColumns ε s i j‖ ≤ 1 := by
    simp only [signedIdentityColumns]
    split_ifs <;> simp
  have e : x i j = (Matrix.of x - signedIdentityColumns ε s) i j + signedIdentityColumns ε s i j := by simp
  rw [e]
  linarith [norm_add_le ((Matrix.of x - signedIdentityColumns ε s) i j) (signedIdentityColumns ε s i j)]

end ReciprocityTheory.ChartRestriction.DS.S7
