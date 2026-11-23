import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FrobeniusBoundOfMulNearOne
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose
import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.LeadingMinorEqDetSubmatrix

open MeasureTheory Matrix Topology Metric Kronecker

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.REAL

namespace L1

section Growth

variable {n : ℕ}

abbrev SgIx (ε : Fin n → Bool) (s : Bool) : Type := {a : Fin n // ε a = s}

def hsR {Q : Type} [Fintype Q] (x : Matrix (Fin n) Q ℂ) : ℝ := ∑ i, ∑ j, ‖x i j‖ ^ 2

def P0 (ε : Fin n → Bool) (s : Bool) : Matrix (Fin n) (SgIx ε s) ℂ := fun a b => if a = b.1 then 1 else 0

lemma hsR_cont {Q : Type} [Fintype Q] : Continuous (hsR : Matrix (Fin n) Q ℂ → ℝ) :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    ((continuous_id.matrix_elem i j).norm).pow 2

lemma hsR_entry_le {Q : Type} [Fintype Q] (g : Matrix (Fin n) Q ℂ) (i : Fin n) (j : Q) : ‖g i j‖ ^ 2 ≤ hsR g := by
  unfold hsR
  calc ‖g i j‖ ^ 2 ≤ ∑ j', ‖g i j'‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖g i j'‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑ j', ‖g i' j'‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

lemma mul_sign_projection_apply (ε : Fin n → Bool) (s : Bool) (g : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (b : SgIx ε s) :
    (g * P0 ε s) i b = g i b.1 := by
  simp [Matrix.mul_apply, P0]

lemma sum_SgIx (ε : Fin n → Bool) (s : Bool) (f : Fin n → ℝ) :
    ∑ b : SgIx ε s, f b.1 = ∑ j, if ε j = s then f j else 0 := by
  rw [← Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter (fun a => ε a = s)) (by simp) f).symm

lemma hilbert_schmidt_sign_projection_le (ε : Fin n → Bool) (s : Bool) : hsR (P0 ε s) ≤ n := by
  have h : hsR (P0 ε s) = hsR ((1 : Matrix (Fin n) (Fin n) ℂ) * P0 ε s) := by rw [Matrix.one_mul]
  rw [h]
  unfold hsR
  simp only [mul_sign_projection_apply]
  calc ∑ i, ∑ b : SgIx ε s, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i b.1‖ ^ 2
      = ∑ i, ∑ j, if ε j = s then ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 else 0 :=
        Finset.sum_congr rfl fun i _ => sum_SgIx ε s (fun j => ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2)
    _ ≤ ∑ i, ∑ j, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          split_ifs
          · exact le_rfl
          · positivity
    _ = n := f1auxiliary_hs_one n

lemma hs_le_cols {ε : Fin n → Bool} (s : Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    hs g ≤ n + 2 * hsR (g * P0 ε s) := by
  have h := (indefinite_unitary_preserves_form hg).1
  let sg : Fin n → ℝ := fun j => if ε j then 1 else -1
  have hrow : ∀ i, ∑ j, sg j * ‖g i j‖ ^ 2 = sg i := by
    intro i
    have hi := congrFun (congrFun h i) i
    have hre := congrArg Complex.re hi
    have e1 : (g * Jm ε * gᴴ) i i = ∑ j, ((sg j * ‖g i j‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      have : (g * Jm ε) i j = g i j * ((sg j : ℝ) : ℂ) := by
        unfold Jm
        rw [Matrix.mul_diagonal]
        congr 1
        simp only [sg]
        split_ifs <;> simp
      rw [this, Matrix.conjTranspose_apply, Complex.star_def]
      have h2 : g i j * (starRingEnd ℂ) (g i j) = ((‖g i j‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      calc g i j * ((sg j : ℝ) : ℂ) * (starRingEnd ℂ) (g i j)
          = ((sg j : ℝ) : ℂ) * (g i j * (starRingEnd ℂ) (g i j)) := by ring
        _ = _ := by rw [h2]; push_cast; ring
    have e2 : (Jm ε) i i = ((sg i : ℝ) : ℂ) := by
      unfold Jm
      rw [Matrix.diagonal_apply_eq]
      simp only [sg]
      split_ifs <;> simp
    rw [e1, e2, ← Complex.ofReal_sum] at hi
    exact_mod_cast hi
  let c : ℝ := if s then 1 else -1
  have hc : ∀ j, (if ε j = s then (2 : ℝ) else 0) = 1 + c * sg j := by
    intro j
    simp only [c, sg]
    cases s <;> cases ε j <;> norm_num
  have e3 : 2 * hsR (g * P0 ε s) = hs g + c * ∑ i, sg i := by
    unfold hsR hs
    simp only [mul_sign_projection_apply]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_SgIx ε s (fun j => ‖g i j‖ ^ 2), ← hrow i, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := hc j
    split_ifs at this ⊢ with hj
    · linear_combination (‖g i j‖ ^ 2) * this
    · linear_combination (‖g i j‖ ^ 2) * this
  have e4 : |c * ∑ i, sg i| ≤ n := by
    rw [abs_mul]
    have h1 : |c| = 1 := by simp only [c]; split_ifs <;> simp
    rw [h1, one_mul]
    calc |∑ i, sg i| ≤ ∑ i, |sg i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ _i : Fin n, (1 : ℝ) := Finset.sum_congr rfl fun i _ => by simp only [sg]; split_ifs <;> simp
      _ = n := by simp
  have := (abs_le.1 e4).1
  linarith

def Lc {Q : Type} [Fintype Q] (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) Q ℂ →ₗ[ℂ] Matrix (Fin n) Q ℂ where
  toFun x := g * x
  map_add' := Matrix.mul_add g
  map_smul' c x := by simp

lemma stdBasis_repr' {Q : Type} [Fintype Q] [DecidableEq Q] (x : Matrix (Fin n) Q ℂ) (i : Fin n) (j : Q) :
    (Matrix.stdBasis ℂ (Fin n) Q).repr x (i, j) = x i j := by
  simp [Matrix.stdBasis, Module.Basis.map_repr, Pi.basis_repr, Pi.basisFun_repr]

lemma Lc_det {Q : Type} [Fintype Q] [DecidableEq Q] (g : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det (Lc (Q := Q) g) = g.det ^ Fintype.card Q := by
  classical
  rw [← LinearMap.det_toMatrix (Matrix.stdBasis ℂ (Fin n) Q)]
  have : LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin n) Q) (Matrix.stdBasis ℂ (Fin n) Q)
      (Lc (Q := Q) g) = g ⊗ₖ (1 : Matrix Q Q ℂ) := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rw [LinearMap.toMatrix_apply, stdBasis_repr']
    simp only [Matrix.stdBasis_eq_single, Matrix.kroneckerMap_apply, Matrix.one_apply,
      Lc, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply, Matrix.single_apply]
    by_cases h : j = l
    · subst h; simp
    · simp [h, Ne.symm h]
  rw [this, Matrix.det_kronecker]
  simp

abbrev RE (n : ℕ) (Q : Type) := Fin n → Q → ℂ

def Re_ (n : ℕ) (Q : Type) : RE n Q ≃ₗ[ℝ] Matrix (Fin n) Q ℂ := Matrix.ofLinearEquiv ℝ

def RL {Q : Type} [Fintype Q] (g : Matrix (Fin n) (Fin n) ℂ) : RE n Q →ₗ[ℝ] RE n Q :=
  ((Re_ n Q).symm : Matrix (Fin n) Q ℂ →ₗ[ℝ] RE n Q) ∘ₗ ((Lc (Q := Q) g).restrictScalars ℝ) ∘ₗ
    ((Re_ n Q : RE n Q ≃ₗ[ℝ] Matrix (Fin n) Q ℂ) : RE n Q →ₗ[ℝ] Matrix (Fin n) Q ℂ)

lemma RL_apply {Q : Type} [Fintype Q] (g : Matrix (Fin n) (Fin n) ℂ) (x : RE n Q) :
    RL g x = Matrix.of.symm (g * Matrix.of x) := rfl

lemma of_RL {Q : Type} [Fintype Q] (A : Matrix (Fin n) (Fin n) ℂ) (x : RE n Q) :
    Matrix.of (RL A x) = A * Matrix.of x := by
  rw [RL_apply, Equiv.apply_symm_apply]

lemma RL_det {Q : Type} [Fintype Q] [DecidableEq Q] {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : inUJ ε g) : LinearMap.det (RL (Q := Q) g) = 1 := by
  unfold RL
  have := LinearMap.det_conj ((Lc (Q := Q) g).restrictScalars ℝ) (Re_ n Q).symm
  rw [LinearEquiv.symm_symm] at this
  rw [this, LinearMap.det_restrictScalars, Lc_det, map_pow, Algebra.norm_complex_apply, normSq_det_indefinite_unitary hg, one_pow]

section frob
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

lemma hsR_eq {Q : Type} [Fintype Q] (A : Matrix (Fin n) Q ℂ) : hsR A = ‖A‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num [hsR]

lemma norm_poincareLift_sq_le (ε : Fin n → Bool) (s : Bool) : ‖P0 ε s‖ ≤ Real.sqrt n := by
  have h := hilbert_schmidt_sign_projection_le ε s
  rw [hsR_eq] at h
  exact Real.le_sqrt_of_sq_le h

lemma normR_lt {Q : Type} [Fintype Q] {u : Matrix (Fin n) Q ℂ} (hu : hsR u < 1 / 16) : ‖u‖ < 1 / 4 := by
  rw [hsR_eq] at hu
  nlinarith [norm_nonneg u]

lemma normR_u {ε : Fin n → Bool} {s : Bool} {u : Matrix (Fin n) (SgIx ε s) ℂ} (hu : hsR (u - P0 ε s) < 1 / 16) :
    ‖u‖ ≤ Real.sqrt n + 1 / 4 := by
  have h1 := normR_lt hu
  have h2 : ‖u‖ ≤ ‖P0 ε s‖ + ‖u - P0 ε s‖ := by
    calc ‖u‖ = ‖P0 ε s + (u - P0 ε s)‖ := by rw [add_sub_cancel]
      _ ≤ _ := norm_add_le _ _
  have := norm_poincareLift_sq_le ε s
  linarith

lemma smallR {ε : Fin n → Bool} {s : Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    {u v : Matrix (Fin n) (SgIx ε s) ℂ} (hu : hsR (u - P0 ε s) < 1 / 16) (hv : hsR (v - P0 ε s) < 1 / 16)
    (h : k * u = v) : hs k ≤ n + 2 * (5 / 2 * Real.sqrt n + 1 / 2) ^ 2 := by
  have e : k * P0 ε s = v + k * (P0 ε s - u) := by rw [Matrix.mul_sub, h]; abel
  have h1 : ‖k * P0 ε s‖ ≤ ‖v‖ + ‖k‖ * ‖P0 ε s - u‖ := by
    calc ‖k * P0 ε s‖ = ‖v + k * (P0 ε s - u)‖ := by rw [← e]
      _ ≤ ‖v‖ + ‖k * (P0 ε s - u)‖ := norm_add_le _ _
      _ ≤ _ := by gcongr; exact Matrix.frobenius_norm_mul _ _
  rw [norm_sub_rev] at h1
  have h2 := normR_lt hu
  have h3 := normR_u hv
  have h4 := hs_le_cols s hk
  rw [hsR_eq, frobenius_eq_norm_sq] at h4
  have hs0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  have h5 : ‖k‖ ≤ Real.sqrt n + 2 * ‖k * P0 ε s‖ := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    nlinarith [norm_nonneg (k * P0 ε s)]
  have h6 : ‖k * P0 ε s‖ ≤ 5 / 2 * Real.sqrt n + 1 / 2 := by
    nlinarith [norm_nonneg k, norm_nonneg (u - P0 ε s), norm_nonneg (k * P0 ε s)]
  rw [frobenius_eq_norm_sq]
  have h7 : ‖k * P0 ε s‖ ^ 2 ≤ (5 / 2 * Real.sqrt n + 1 / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h6 2
  linarith

lemma entryR {ε : Fin n → Bool} {s : Bool} {g : Matrix (Fin n) (Fin n) ℂ} {u : Matrix (Fin n) (SgIx ε s) ℂ} {R : ℝ}
    (hR : 0 ≤ R) (hg : hs g ≤ R ^ 2) (hu : hsR (u - P0 ε s) < 1 / 16) (i : Fin n) (j : SgIx ε s) :
    ‖(g * u) i j‖ ≤ R * (Real.sqrt n + 1) := by
  have hg' : ‖g‖ ≤ R := by
    rw [frobenius_eq_norm_sq] at hg
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).1 hg
  have hu' := normR_u hu
  have he : ‖(g * u) i j‖ ≤ ‖g * u‖ := by
    have := hsR_entry_le (g * u) i j
    rw [hsR_eq] at this
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  calc ‖(g * u) i j‖ ≤ ‖g * u‖ := he
    _ ≤ ‖g‖ * ‖u‖ := Matrix.frobenius_norm_mul _ _
    _ ≤ R * (Real.sqrt n + 1 / 4) := by gcongr
    _ ≤ R * (Real.sqrt n + 1) := by gcongr; norm_num

end frob

lemma O_bddR {ε : Fin n → Bool} {s : Bool} {x : RE n (SgIx ε s)} (hx : hsR (Matrix.of x - P0 ε s) < 1 / 16) :
    x ∈ closedBall (0 : RE n (SgIx ε s)) 2 := by
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro j
  have h1 := (hsR_entry_le (Matrix.of x - P0 ε s) i j).trans_lt hx
  have h2 : ‖(Matrix.of x - P0 ε s) i j‖ < 1 / 4 := by nlinarith [norm_nonneg ((Matrix.of x - P0 ε s) i j)]
  have h3 : ‖(P0 ε s) i j‖ ≤ 1 := by
    unfold P0; split_ifs <;> simp
  have h4 : x i j = (Matrix.of x - P0 ε s) i j + (P0 ε s) i j := by
    simp [Matrix.sub_apply]
  rw [h4]
  calc _ ≤ ‖(Matrix.of x - P0 ε s) i j‖ + ‖(P0 ε s) i j‖ := norm_add_le _ _
    _ ≤ 2 := by linarith

theorem volGrowthR {n : ℕ} (ε : Fin n → Bool) (s : Bool) : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
    muG ε {g | hsG g ≤ R ^ 2} ≤ ENNReal.ofReal (C * R ^ (2 * (n * Fintype.card (SgIx ε s)))) := by
  classical
  let Q := SgIx ε s
  let μ : Measure (UJ ε) := muG ε
  let lam : Measure (RE n Q) := Measure.addHaar
  let O : Set (RE n Q) := {x | hsR (Matrix.of x - P0 ε s) < 1 / 16}
  let r0 : ℝ := n + 2 * (5 / 2 * Real.sqrt n + 1 / 2) ^ 2
  let W : Set (UJ ε) := {k | hsG k ≤ r0}
  let N : ℕ := 2 * (n * Fintype.card Q)
  have hof : Continuous (fun x : RE n Q => (Matrix.of x : Matrix (Fin n) Q ℂ)) := continuous_id
  have hofs : Continuous (fun x : Matrix (Fin n) Q ℂ => (Matrix.of.symm x : RE n Q)) := continuous_id
  have hO_open : IsOpen O :=
    isOpen_lt (hsR_cont.comp (hof.sub continuous_const)) continuous_const
  have hO_pos : 0 < lam O := hO_open.measure_pos lam ⟨Matrix.of.symm (P0 ε s), by simp [O, hsR]⟩
  have hO_fin : lam O < ⊤ :=
    (measure_mono (fun x hx => O_bddR hx)).trans_lt measure_closedBall_lt_top
  have hW_fin : μ W < ⊤ := ball_finite_measure_holds n ε r0
  have hB_fin : lam (ball 0 1) < ⊤ := measure_ball_lt_top
  set K : ENNReal := μ W * lam (ball 0 1) / lam O with hK
  have hK_fin : K ≠ ⊤ := by
    rw [hK]
    exact ENNReal.div_ne_top (ENNReal.mul_ne_top hW_fin.ne hB_fin.ne) hO_pos.ne'
  refine ⟨K.toReal * (Real.sqrt n + 1) ^ N, by positivity, fun R hR => ?_⟩
  have hR0 : 0 ≤ R := by linarith
  set ρ : ℝ := R * (Real.sqrt n + 1) with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  set S : Set (UJ ε) := {g | hsG g ≤ R ^ 2} with hS
  have hS_meas : MeasurableSet S :=
    (isClosed_le (continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)) continuous_const).measurableSet
  let Φ : UJ ε × RE n Q → RE n Q := fun p => RL (coeMatrixAlt ε p.1⁻¹) p.2
  have hΦ : Continuous Φ := by
    show Continuous fun p : UJ ε × RE n Q =>
      (Matrix.of.symm (coeMatrixAlt ε p.1⁻¹ * Matrix.of p.2) : RE n Q)
    exact hofs.comp (((continuous_coeMatrix ε).comp (continuous_inv.comp continuous_fst)).matrix_mul
      (hof.comp continuous_snd))
  let T : Set (UJ ε × RE n Q) := {p | hsG p.1 ≤ R ^ 2} ∩ Φ ⁻¹' O
  have hT : MeasurableSet T :=
    (isClosed_le ((continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)).comp continuous_fst)
      continuous_const).measurableSet.inter (hO_open.preimage hΦ).measurableSet
  have h1 : (μ.prod lam) T = μ S * lam O := by
    rw [Measure.prod_apply hT]
    have : ∀ g, lam (Prod.mk g ⁻¹' T) = S.indicator (fun _ => lam O) g := by
      intro g
      by_cases hg : g ∈ S
      · rw [Set.indicator_of_mem hg]
        have hdet : LinearMap.det (RL (Q := Q) (coeMatrixAlt ε g⁻¹)) = 1 := RL_det (g⁻¹).2
        have e : Prod.mk g ⁻¹' T = RL (Q := Q) (coeMatrixAlt ε g⁻¹) ⁻¹' O := by
          ext x
          simp only [T, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq, Φ]
          exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
        rw [e, Measure.addHaar_preimage_linearMap lam (by rw [hdet]; exact one_ne_zero), hdet]
        simp
      · rw [Set.indicator_of_notMem hg]
        have e : Prod.mk g ⁻¹' T = ∅ := by
          ext x
          simp only [T, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq,
            Set.mem_empty_iff_false, iff_false, not_and]
          exact fun h => absurd h hg
        rw [e, measure_empty]
    simp_rw [this]
    rw [lintegral_indicator_const hS_meas, mul_comm]
  have h2 : (μ.prod lam) T ≤ μ W * lam (closedBall 0 ρ) := by
    rw [Measure.prod_apply_symm hT]
    calc ∫⁻ x, μ ((fun g => (g, x)) ⁻¹' T) ∂lam
        ≤ ∫⁻ x, (closedBall (0 : RE n Q) ρ).indicator (fun _ => μ W) x ∂lam := by
          refine lintegral_mono fun x => ?_
          by_cases hne : ((fun g => (g, x)) ⁻¹' T).Nonempty
          · obtain ⟨h, hh⟩ := hne
            have hh1 : hsG h ≤ R ^ 2 := hh.1
            have hh2 : hsR (Matrix.of (RL (coeMatrixAlt ε h⁻¹) x) - P0 ε s) < 1 / 16 := hh.2
            rw [of_RL] at hh2
            have hx : x ∈ closedBall (0 : RE n Q) ρ := by
              rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hρ0]
              intro i
              rw [pi_norm_le_iff_of_nonneg hρ0]
              intro j
              have := entryR (g := coeMatrixAlt ε h) hR0 hh1 hh2 i j
              rw [← Matrix.mul_assoc, determinant_character_mul_inv, Matrix.one_mul] at this
              exact this
            rw [Set.indicator_of_mem hx]
            calc μ ((fun g => (g, x)) ⁻¹' T) ≤ μ ((fun g => h⁻¹ * g) ⁻¹' W) := by
                  refine measure_mono fun g hg => ?_
                  have hg2 : hsR (Matrix.of (RL (coeMatrixAlt ε g⁻¹) x) - P0 ε s) < 1 / 16 := hg.2
                  rw [of_RL] at hg2
                  show hs (coeMatrixAlt ε (h⁻¹ * g)) ≤ r0
                  refine smallR (h⁻¹ * g).2 hg2 hh2 ?_
                  rw [determinant_character_mul, ← Matrix.mul_assoc, Matrix.mul_assoc (coeMatrixAlt ε h⁻¹),
                    determinant_character_mul_inv, Matrix.mul_one]
              _ = μ W := measure_preimage_mul μ h⁻¹ W
          · rw [Set.not_nonempty_iff_eq_empty.1 hne, measure_empty]
            exact bot_le
      _ = μ W * lam (closedBall 0 ρ) := lintegral_indicator_const measurableSet_closedBall _
  have hfr : Module.finrank ℝ (RE n Q) = N := by
    simp [RE, N, Module.finrank_pi_fintype, Complex.finrank_real_complex]; ring
  have h3 : lam (closedBall 0 ρ) = ENNReal.ofReal (ρ ^ N) * lam (ball 0 1) := by
    rw [Measure.addHaar_closedBall lam _ hρ0, hfr]
  have h4 : μ S * lam O ≤ K * ENNReal.ofReal (ρ ^ N) * lam O := by
    rw [← h1]
    refine h2.trans (le_of_eq ?_)
    rw [h3, hK, div_eq_mul_inv]
    have : (lam O)⁻¹ * lam O = 1 := ENNReal.inv_mul_cancel hO_pos.ne' hO_fin.ne
    calc μ W * (ENNReal.ofReal (ρ ^ N) * lam (ball 0 1))
        = μ W * (ENNReal.ofReal (ρ ^ N) * lam (ball 0 1)) * ((lam O)⁻¹ * lam O) := by
          rw [this, mul_one]
      _ = _ := by ring
  have h5 : μ S ≤ K * ENNReal.ofReal (ρ ^ N) :=
    (ENNReal.mul_le_mul_iff_left hO_pos.ne' hO_fin.ne).1 h4
  refine h5.trans (le_of_eq ?_)
  rw [hρ, mul_pow, ← ENNReal.ofReal_toReal hK_fin, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
  congr 1
  ring

end Growth

section ExpB

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

lemma norm_exp_frob {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖NormedSpace.exp X‖ ≤ Real.sqrt n * Real.exp ‖X‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : NormedSpace.exp X = 0 := Subsingleton.elim _ _
    rw [this]; simp
  have h1 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]; exact_mod_cast hn
  have hsum := NormedSpace.norm_expSeries_summable' (𝕂 := ℂ) X
  have hr : Summable fun k : ℕ => Real.sqrt n * (‖X‖ ^ k / (k.factorial : ℝ)) :=
    (Real.summable_pow_div_factorial ‖X‖).mul_left _
  rw [NormedSpace.exp_eq_tsum ℂ]
  calc ‖∑' k : ℕ, ((k.factorial : ℂ)⁻¹) • X ^ k‖ ≤ ∑' k : ℕ, ‖((k.factorial : ℂ)⁻¹) • X ^ k‖ :=
        norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' k : ℕ, Real.sqrt n * (‖X‖ ^ k / (k.factorial : ℝ)) := by
        refine hsum.tsum_le_tsum (fun k => ?_) hr
        rw [norm_smul, norm_inv, Complex.norm_natCast]
        have hk : ‖X ^ k‖ ≤ Real.sqrt n * ‖X‖ ^ k := by
          rcases Nat.eq_zero_or_pos k with rfl | hk
          · rw [pow_zero, pow_zero, mul_one, ← sqrt_frobenius_eq_norm, f1auxiliary_hs_one]
          · calc ‖X ^ k‖ ≤ ‖X‖ ^ k := norm_pow_le' X hk
              _ ≤ Real.sqrt n * ‖X‖ ^ k := le_mul_of_one_le_left (by positivity) h1
        calc ((k.factorial : ℝ))⁻¹ * ‖X ^ k‖ ≤ ((k.factorial : ℝ))⁻¹ * (Real.sqrt n * ‖X‖ ^ k) := by gcongr
          _ = _ := by ring
    _ = Real.sqrt n * Real.exp ‖X‖ := by
        rw [tsum_mul_left, Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

end ExpB

lemma hs_exp_le {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    hs (NormedSpace.exp X) ≤ n * Real.exp (2 * Real.sqrt (hs X)) := by
  have h := norm_exp_frob X
  rw [← sqrt_frobenius_eq_norm, ← sqrt_frobenius_eq_norm] at h
  have h0 : 0 ≤ hs (NormedSpace.exp X) := by unfold hs; positivity
  calc hs (NormedSpace.exp X) = Real.sqrt (hs (NormedSpace.exp X)) ^ 2 := (Real.sq_sqrt h0).symm
    _ ≤ (Real.sqrt n * Real.exp (Real.sqrt (hs X))) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    _ = _ := by
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n), ← Real.exp_nat_mul]
        norm_num

section Decay

open scoped ENNReal

theorem integrable_of_decay {n : ℕ} (ε : Fin n → Bool) (s : Bool) (f : UJ ε → ℂ) (hf : Continuous f)
    (h1 : ∀ g, ‖f g‖ ≤ 1) (a : ℝ) (ha : ((2 * (n * Fintype.card (SgIx ε s)) : ℕ) : ℝ) < a)
    (hdec : ∀ g, (n : ℝ) * Real.exp 2 + 1 < hsG g →
      ∃ t : ℝ, hsG g ≤ n * Real.exp (2 * t) ∧ ‖f g‖ ≤ Real.exp (-(a * t))) :
    Integrable f (muG ε) := by
  obtain ⟨C, hC0, hC⟩ := volGrowthR ε s
  set N : ℕ := 2 * (n * Fintype.card (SgIx ε s)) with hN
  have ha0 : 0 < a := lt_of_le_of_lt (Nat.cast_nonneg N) ha
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  let A0 : ℝ := Real.exp (a * Real.log n / 2)
  let y : ℝ := Real.exp (-(a * Real.log 2))
  let r : ℝ := 2 ^ N * y
  have hy0 : 0 < y := Real.exp_pos _
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    have e : (2 : ℝ) ^ N = Real.exp (N * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log two_pos]
    show 2 ^ N * Real.exp (-(a * Real.log 2)) < 1
    rw [e, ← Real.exp_add, Real.exp_lt_one_iff]
    nlinarith
  let B0 : Set (UJ ε) := {g | hsG g ≤ (n : ℝ) * Real.exp 2 + 1}
  let S : ℕ → Set (UJ ε) := fun j => {g | hsG g ≤ ((2 : ℝ) ^ j) ^ 2}
  have hcont : Continuous (hsG : UJ ε → ℝ) := continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)
  have hB0m : MeasurableSet B0 := (isClosed_le hcont continuous_const).measurableSet
  have hSm : ∀ j, MeasurableSet (S j) := fun j => (isClosed_le hcont continuous_const).measurableSet
  let c : ℕ → ℝ≥0∞ := fun j => ENNReal.ofReal (A0 * y ^ j)
  let F : UJ ε → ℝ≥0∞ := fun g => B0.indicator (fun _ => 1) g + ∑' j, (S (j + 1)).indicator (fun _ => c j) g
  have hpt : ∀ g, ‖f g‖ₑ ≤ F g := by
    intro g
    by_cases hg : g ∈ B0
    · calc ‖f g‖ₑ ≤ 1 := by
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_one.2 (h1 g)
        _ = B0.indicator (fun _ => (1 : ℝ≥0∞)) g := (Set.indicator_of_mem hg (fun _ => (1 : ℝ≥0∞))).symm
        _ ≤ F g := le_self_add
    · have hg' : (n : ℝ) * Real.exp 2 + 1 < hsG g := not_le.1 hg
      obtain ⟨t, ht1, ht2⟩ := hdec g hg'
      have hpos : (1 : ℝ) ≤ hsG g := by
        have : 0 ≤ (n : ℝ) * Real.exp 2 := by positivity
        linarith
      obtain ⟨j, hj1, hj2⟩ := exists_nat_pow_near hpos (show (1 : ℝ) < 4 by norm_num)
      have hn0 : (0 : ℝ) < n := by
        by_contra hcon
        have : (n : ℝ) = 0 := le_antisymm (not_lt.1 hcon) (Nat.cast_nonneg n)
        rw [this, zero_mul] at ht1
        linarith
      have hmem : g ∈ S (j + 1) := by
        show hsG g ≤ ((2 : ℝ) ^ (j + 1)) ^ 2
        have : ((2 : ℝ) ^ (j + 1)) ^ 2 = 4 ^ (j + 1) := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [this]; exact hj2.le
      have hlog : (j : ℝ) * Real.log 2 - Real.log n / 2 ≤ t := by
        have h4 : (4 : ℝ) ^ j ≤ n * Real.exp (2 * t) := hj1.trans ht1
        have h5 := Real.log_le_log (by positivity) h4
        rw [Real.log_pow, Real.log_mul hn0.ne' (Real.exp_pos _).ne', Real.log_exp] at h5
        have h6 : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        rw [h6] at h5
        linarith
      have hb : ‖f g‖ ≤ A0 * y ^ j := by
        refine ht2.trans ?_
        show Real.exp (-(a * t)) ≤ Real.exp (a * Real.log n / 2) * Real.exp (-(a * Real.log 2)) ^ j
        rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
        nlinarith
      calc ‖f g‖ₑ ≤ c j := by
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal hb
        _ = (S (j + 1)).indicator (fun _ => c j) g := (Set.indicator_of_mem hmem (fun _ => c j)).symm
        _ ≤ ∑' j, (S (j + 1)).indicator (fun _ => c j) g :=
            ENNReal.le_tsum (f := fun j => (S (j + 1)).indicator (fun _ => c j) g) j
        _ ≤ F g := le_add_self
  have hterm : ∀ j, c j * muG ε (S (j + 1)) ≤ ENNReal.ofReal (A0 * C * 2 ^ N * r ^ j) := by
    intro j
    have h2 : (1 : ℝ) ≤ 2 ^ (j + 1) := one_le_pow₀ (by norm_num)
    calc c j * muG ε (S (j + 1)) ≤ c j * ENNReal.ofReal (C * (2 ^ (j + 1)) ^ N) := by
          gcongr
          exact hC _ h2
      _ = ENNReal.ofReal (A0 * y ^ j * (C * (2 ^ (j + 1)) ^ N)) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ = ENNReal.ofReal (A0 * C * 2 ^ N * r ^ j) := by
          congr 1
          show A0 * y ^ j * (C * (2 ^ (j + 1)) ^ N) = A0 * C * 2 ^ N * (2 ^ N * y) ^ j
          rw [mul_pow]
          ring
  have hFint : ∫⁻ g, F g ∂(muG ε) < ⊤ := by
    have e1 : ∫⁻ g, F g ∂(muG ε) = muG ε B0 + ∑' j, c j * muG ε (S (j + 1)) := by
      show ∫⁻ g, (B0.indicator (fun _ => 1) g + ∑' j, (S (j + 1)).indicator (fun _ => c j) g) ∂(muG ε) = _
      rw [lintegral_add_left (measurable_const.indicator hB0m), lintegral_indicator_const hB0m, one_mul,
        lintegral_tsum (fun j => (measurable_const.indicator (hSm (j + 1))).aemeasurable)]
      congr 1
      exact tsum_congr fun j => lintegral_indicator_const (hSm (j + 1)) _
    rw [e1]
    refine ENNReal.add_lt_top.2 ⟨ball_finite_measure_holds n ε _, ?_⟩
    have hsum : Summable fun j : ℕ => A0 * C * 2 ^ N * r ^ j :=
      (summable_geometric_of_lt_one hr0 hr1).mul_left _
    calc ∑' j, c j * muG ε (S (j + 1)) ≤ ∑' j, ENNReal.ofReal (A0 * C * 2 ^ N * r ^ j) :=
          ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal (∑' j, A0 * C * 2 ^ N * r ^ j) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsum).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  exact ⟨hf.aestronglyMeasurable, lt_of_le_of_lt (lintegral_mono hpt) hFint⟩

end Decay

section Rep

open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData
open scoped InnerProductSpace

lemma card_SgIx_true {n : ℕ} (ε : Fin n → Bool) : Fintype.card (SgIx ε true) = pOf ε := by
  unfold pOf; exact Fintype.card_subtype _

lemma card_SgIx_false {n : ℕ} (ε : Fin n → Bool) : Fintype.card (SgIx ε false) = qOf ε := by
  unfold qOf; exact Fintype.card_subtype _

lemma exists_sign {n : ℕ} (ε : Fin n → Bool) : ∃ s : Bool, Fintype.card (SgIx ε s) = min (pOf ε) (qOf ε) := by
  rcases le_total (pOf ε) (qOf ε) with h | h
  · exact ⟨true, by rw [card_SgIx_true, min_eq_left h]⟩
  · exact ⟨false, by rw [card_SgIx_false, min_eq_right h]⟩

lemma card_SgIx_le {n : ℕ} (ε : Fin n → Bool) (s : Bool) : Fintype.card (SgIx ε s) ≤ n := by
  have := Fintype.card_subtype_le (fun a : Fin n => ε a = s)
  simpa using this

lemma rate_lt {n q : ℕ} {h : ℝ} (hn : 1 ≤ n) (hq : 1 ≤ q)
    (hh : 120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ h) :
    ((2 * (n * q) : ℕ) : ℝ) < h / 8 / Real.sqrt (2 * (q : ℝ)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : (q : ℝ) ^ ((3 : ℝ) / 2) = q * Real.sqrt q := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hq0, Real.rpow_one, Real.sqrt_eq_rpow]
  have e2 : Real.sqrt (2 * (q : ℝ)) = Real.sqrt 2 * Real.sqrt q := Real.sqrt_mul (by norm_num) _
  have h2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [lt_div_iff₀ (by rw [e2]; positivity), e2]
  rw [e1] at hh
  push_cast
  have h3 : 0 < (n : ℝ) * q * Real.sqrt q := by positivity
  nlinarith

end Rep

end L1

open L1

section Rep

open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData
open scoped InnerProductSpace

def LowestKTypeProjectorExists : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
      ∃ E : H →L[ℂ] H, IsOrthProjOnto E (lowKSub ε lam σ)

theorem lowest_K_type_projector_of_mult_one (D : Formalism.BasicNotions.D7) (h2 : adm2 D) : LowestKTypeProjectorExists := by
  intro n ε lam hlam H _ _ _ σ hσ
  have hK := (h2 n ε lam hlam H σ hσ).1
  have : FiniteDimensional ℂ (lowKSub ε lam σ) := hK.1
  exact ⟨(lowKSub ε lam σ).starProjection, (lowKSub ε lam σ).isIdempotentElem_starProjection,
    fun x y => Submodule.inner_starProjection_left_eq_right _ x y, Submodule.range_starProjection _⟩

lemma coef_le_compressed_norm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {E A : H →L[ℂ] H}
    {S : Submodule ℂ H} (hE : IsOrthProjOnto E S) {w : H} (hw : w ∈ S) (hw1 : ‖w‖ = 1) :
    ‖⟪w, A w⟫_ℂ‖ ≤ ‖E.comp (A.comp E)‖ := by
  have hEw : E w = w := by
    rw [← hE.2.2] at hw
    obtain ⟨v, rfl⟩ := hw
    exact congrArg (fun T : H →L[ℂ] H => T v) hE.1
  have e : ⟪w, A w⟫_ℂ = ⟪w, (E.comp (A.comp E)) w⟫_ℂ := by
    simp only [ContinuousLinearMap.comp_apply]
    rw [← hE.2.1, hEw]
  rw [e]
  calc ‖⟪w, (E.comp (A.comp E)) w⟫_ℂ‖ ≤ ‖w‖ * ‖(E.comp (A.comp E)) w‖ := norm_inner_le_norm _ _
    _ ≤ ‖w‖ * (‖E.comp (A.comp E)‖ * ‖w‖) := by gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ = _ := by rw [hw1]; ring

theorem lowest_K_type_decay (D : Formalism.BasicNotions.D7) (hDec : DiscreteSeriesDecayBound D) {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ}
    (hlam : Formalism.QuantumDeterminants.IsHCParam lam) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsDS ε lam σ) {E : H →L[ℂ] H}
    (hE : IsOrthProjOnto E (lowKSub ε lam σ)) {w : H} (hw : IsLowUnit ε lam σ w) {h : ℝ}
    (hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam h)
    (hh : 120 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h)
    (hpos : 1 ≤ min (pOf ε) (qOf ε)) (g : UJ ε) (hg : (n : ℝ) * Real.exp 2 + 1 < hsG g) :
    ∃ t : ℝ, hsG g ≤ n * Real.exp (2 * t) ∧
      ‖coefOn σ w w g‖ ≤ Real.exp (-(h / 8 / Real.sqrt (2 * ((min (pOf ε) (qOf ε) : ℕ) : ℝ)) * t)) := by
  obtain ⟨s, hcs⟩ := exists_sign ε
  set q0 : ℕ := min (pOf ε) (qOf ε) with hq0
  have hn1 : 1 ≤ n := le_trans hpos (hcs ▸ card_SgIx_le ε s)
  have hh0 : 0 ≤ h := le_trans (by positivity) hh
  obtain ⟨k, X, hk, hX, hgk⟩ := (polar_decomposition_holds n ε).1 (umat g) g.2
  have hsg : hs (umat g) ≤ n * Real.exp (2 * Real.sqrt (hs X)) := by
    rw [hgk, ((hermitian_small_ball n ε).2 (NormedSpace.exp X) k hk).2]
    exact hs_exp_le X
  refine ⟨Real.sqrt (hs X), hsg, ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have ht1 : 1 ≤ Real.sqrt (hs X) := by
    have h7 : (n : ℝ) * Real.exp 2 < n * Real.exp (2 * Real.sqrt (hs X)) := by
      have : (n : ℝ) * Real.exp 2 + 1 < hs (umat g) := hg
      linarith
    have h8 := Real.exp_lt_exp.1 (lt_of_mul_lt_mul_left h7 hn0.le)
    linarith
  have hX0 : 0 ≤ hs X := by unfold hs; positivity
  have hd := hDec n ε lam hlam H σ hσ E hE h hgap hh k X hk hX
  have hq1 : (1 : ℝ) ≤ Real.sqrt (2 * (q0 : ℝ)) := by
    rw [Real.one_le_sqrt]
    have : (1 : ℝ) ≤ q0 := by exact_mod_cast hpos
    linarith
  have hmin : Real.sqrt (hs X) / Real.sqrt (2 * (q0 : ℝ)) ≤
      min (hs X) (Real.sqrt (hs X) / Real.sqrt (2 * (q0 : ℝ))) := by
    refine le_min ?_ le_rfl
    calc Real.sqrt (hs X) / Real.sqrt (2 * (q0 : ℝ)) ≤ Real.sqrt (hs X) :=
          div_le_self (Real.sqrt_nonneg _) hq1
      _ ≤ Real.sqrt (hs X) * Real.sqrt (hs X) := le_mul_of_one_le_left (Real.sqrt_nonneg _) ht1
      _ = hs X := Real.mul_self_sqrt hX0
  have hc : ‖coefOn σ w w g‖ ≤ ‖E.comp ((σ (k * NormedSpace.exp X)).comp E)‖ := by
    show ‖⟪w, σ (umat g) w⟫_ℂ‖ ≤ _
    rw [hgk]
    exact coef_le_compressed_norm hE hw.2 hw.1
  refine hc.trans (hd.trans ?_)
  unfold decBound
  rw [Real.exp_le_exp]
  have h9 : h / 8 * (Real.sqrt (hs X) / Real.sqrt (2 * (q0 : ℝ))) ≤
      h / 8 * min (hs X) (Real.sqrt (hs X) / Real.sqrt (2 * (q0 : ℝ))) :=
    mul_le_mul_of_nonneg_left hmin (by positivity)
  have e9 : h / 8 / Real.sqrt (2 * (q0 : ℝ)) * Real.sqrt (hs X) =
      h / 8 * (Real.sqrt (hs X) / Real.sqrt (2 * (q0 : ℝ))) := by ring
  rw [e9]
  linarith

theorem spherical_L1_of_projector (D : Formalism.BasicNotions.D7) (hP : LowestKTypeProjectorExists) (hDec : DiscreteSeriesDecayBound D) : MatrixCoefficientIntegrable D := by
  intro n ε lam hlam H _ _ _ σ hσ w hw h hgap hh
  obtain ⟨E, hE⟩ := hP n ε lam hlam H σ hσ
  have hU := hσ.2.2.1
  obtain ⟨s, hcs⟩ := exists_sign ε
  set q0 : ℕ := min (pOf ε) (qOf ε) with hq0
  let f : UJ ε → ℂ := fun g => star (coefOn σ w w g)
  have hcont : Continuous f := by
    have h1 : Continuous fun g : UJ ε => σ (umat g) w :=
      (hU.2.2 w).comp_continuous (continuous_coeMatrix ε) (fun g => g.2)
    exact continuous_star.comp (continuous_const.inner h1)
  have hone : ∀ g, ‖f g‖ ≤ 1 := by
    intro g
    show ‖star (⟪w, σ (umat g) w⟫_ℂ)‖ ≤ 1
    rw [norm_star]
    calc ‖⟪w, σ (umat g) w⟫_ℂ‖ ≤ ‖w‖ * ‖σ (umat g) w‖ := norm_inner_le_norm _ _
      _ = 1 := by rw [hU.2.1 _ g.2 w, hw.1, mul_one]
  have hint : Integrable f (muG ε) := by
    rcases Nat.eq_zero_or_pos q0 with hz | hpos
    · refine integrable_of_decay ε s f hcont hone 1 (by rw [hcs, hz]; norm_num) (fun g hg => ?_)
      exfalso
      have h3 := hs_le_cols s g.2
      have : IsEmpty (SgIx ε s) := Fintype.card_eq_zero_iff.1 (by rw [hcs, hz])
      have h4 : hsR (umat g * P0 ε s) = 0 := by
        simp [hsR]
      rw [h4] at h3
      have h5 : (n : ℝ) ≤ n * Real.exp 2 :=
        le_mul_of_one_le_right (Nat.cast_nonneg n) (Real.one_le_exp (by norm_num))
      have h6 : hsG g ≤ n + 2 * 0 := h3
      linarith
    · have hn1 : 1 ≤ n := le_trans hpos (hcs ▸ card_SgIx_le ε s)
      have hrate := rate_lt hn1 hpos hh
      refine integrable_of_decay ε s f hcont hone (h / 8 / Real.sqrt (2 * (q0 : ℝ))) (by rw [hcs]; exact hrate)
        (fun g hg => ?_)
      obtain ⟨t, ht1, ht2⟩ := lowest_K_type_decay D hDec hlam hσ hE hw hgap hh hpos g hg
      exact ⟨t, ht1, by show ‖star (coefOn σ w w g)‖ ≤ _; rw [norm_star]; exact ht2⟩
  exact hint.const_mul _

theorem spherical_L1_of_lowest_K_decay (D : Formalism.BasicNotions.D7) (h2 : adm2 D) (hDec : DiscreteSeriesDecayBound D) : MatrixCoefficientIntegrable D :=
  spherical_L1_of_projector D (lowest_K_type_projector_of_mult_one D h2) hDec

theorem family_spherical_L1_statement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h2 : admF2 Fm) : FamilyIntegrabilityOfDecay Fm :=
  fun h x i => spherical_L1_of_lowest_K_decay _ (h2 x i) (h x i)

end Rep

section Pos

open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData
open scoped InnerProductSpace ComplexOrder ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

end Pos

section F

open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData
open scoped InnerProductSpace ComplexOrder

def FormulaWithoutPositivity (_D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
      ∀ E : H →L[ℂ] H, IsOrthProjOnto E (lowKSub ε lam σ) →
      ∀ w : H, IsHighestUnit ε lam σ w →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
        120 * (n : ℝ) * ((min (pOf ε) (qOf ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h →
      ∀ X : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inP ε X →
        E ∘L σ (NormedSpace.exp X) ∘L E =
          ((Module.finrank ℂ (lowKSub ε lam σ) : ℕ) : ℂ) •
            ∫ kk : Formalism.REAL.KG ε, ((wtF lam X (Formalism.REAL.toMK kk) : ℝ) : ℂ) • rank1 (σ (Formalism.REAL.toMK kk) w)
              ∂(Formalism.REAL.muK ε)

end F

end Formalism.MainNotions.BridgeLemma

end
