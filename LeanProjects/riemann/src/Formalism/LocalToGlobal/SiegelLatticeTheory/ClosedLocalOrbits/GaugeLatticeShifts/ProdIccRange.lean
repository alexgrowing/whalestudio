import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacExGoodOfN

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.CoordinateScalingProducts

open Formalism.L2.SG.RealObj

theorem prod_Icc_range (y : ℕ → ℝ) : ∀ r : ℕ,
    ∏ l ∈ Finset.Icc 1 r, ∏ i ∈ Finset.range l, y i = ∏ i ∈ Finset.range r, y i ^ (r - i)
  | 0 => by simp
  | r + 1 => by
    rw [Finset.prod_Icc_succ_top (by omega), prod_Icc_range y r,
      Finset.prod_range_succ (fun i => y i ^ (r + 1 - i)), Finset.prod_range_succ]
    have h : ∀ i ∈ Finset.range r, y i ^ (r + 1 - i) = y i ^ (r - i) * y i := fun i hi => by
      rw [← pow_succ]; congr 1; have := Finset.mem_range.1 hi; omega
    rw [Finset.prod_congr rfl h, Finset.prod_mul_distrib, show r + 1 - r = 1 by omega, pow_one]
    ring

def lam (r : ℕ) (sc : ℝ) (a : Fin r) : ℂ := (((sc : ℂ) ^ (r - a.1))⁻¹) ^ 2

theorem coordSc_cs {r : ℕ} (sc : ℝ) (q : (Fin r → ℂ) × ℂ) (a : Fin r) :
    coordSc r sc q a.castSucc = lam r sc a * q.1 a := by
  simp [coordSc, lam]

theorem coordSc_last {r : ℕ} (sc : ℝ) (q : (Fin r → ℂ) × ℂ) : coordSc r sc q (Fin.last r) = q.2 := by
  simp [coordSc]

theorem dl_diag {r : ℕ} (c : Fin (r + 1) → ℂ) (l : ℕ) (hl : l ≤ r + 1) :
    Dl (Matrix.diagonal c) l = ∏ i : Fin l, c (Fin.castLE hl i) := by
  rw [Dl, dif_pos hl, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective hl), Matrix.det_diagonal]
  rfl

theorem gv_cs {r : ℕ} (T T' sc : ℝ) (q : (Fin r → ℂ) × ℂ) :
    Gv T T' (Matrix.diagonal (coordSc r sc q)) =
      (∏ a : Fin r, ‖lam r sc a * q.1 a‖ ^ 2) * (Complex.normSq q.2 - T * T') := by
  have h1 : ∀ i : Fin (r + 1), Fin.castLE le_rfl i = i := fun i => Fin.ext rfl
  have h2 : ∀ i : Fin r, Fin.castLE (Nat.le_succ r) i = i.castSucc := fun i => Fin.ext rfl
  rw [Gv, dl_diag _ (r + 1) le_rfl, dl_diag _ r (Nat.le_succ r)]
  simp only [h1, h2]
  rw [Fin.prod_univ_castSucc, coordSc_last]
  simp only [coordSc_cs]
  rw [norm_mul, norm_prod, Complex.normSq_eq_norm_sq, Finset.prod_pow]
  ring

theorem jac_cs {r : ℕ} (sc : ℝ) (q : (Fin r → ℂ) × ℂ) :
    JacV (Matrix.diagonal (coordSc r sc q)) = ∏ a : Fin r, (‖lam r sc a * q.1 a‖ ^ 4) ^ (r - a.1) := by
  let y : ℕ → ℝ := fun i => if h : i < r then ‖lam r sc ⟨i, h⟩ * q.1 ⟨i, h⟩‖ ^ 4 else 0
  have hl : ∀ l ∈ Finset.Icc 1 r,
      modC (Dl (Matrix.diagonal (coordSc r sc q)) l) ^ 2 = ∏ i ∈ Finset.range l, y i := by
    intro l hl
    have hlr : l ≤ r := (Finset.mem_Icc.1 hl).2
    have hl1 : l ≤ r + 1 := by omega
    rw [dl_diag _ l hl1, modC, norm_prod, ← Finset.prod_pow, ← Finset.prod_pow,
      ← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi : i.1 < r := lt_of_lt_of_le i.2 hlr
    have hc : Fin.castLE hl1 i = (⟨i.1, hi⟩ : Fin r).castSucc := Fin.ext rfl
    rw [hc, coordSc_cs]
    simp only [y, dif_pos hi]
    ring
  rw [JacV, Finset.prod_congr rfl hl, prod_Icc_range y r,
    ← Fin.prod_univ_eq_prod_range (fun i => y i ^ (r - i)) r]
  refine Finset.prod_congr rfl fun a _ => ?_
  simp only [y, dif_pos a.2]

def lamW (r k : ℕ) (sc : ℝ) : ℝ := ∏ a : Fin r, ‖lam r sc a‖ ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2))

theorem wt_cs {r k : ℕ} (hk : 1 ≤ k) (T T' sc : ℝ) (q : (Fin r → ℂ) × ℂ) :
    wtLoc k T T' (coordSc r sc q) = lamW r k sc *
      ((∏ a : Fin r, ‖q.1 a‖ ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2))) * (Complex.normSq q.2 - T * T') ^ (k - 1)) := by
  rw [wtLoc, gv_cs, jac_cs, lamW, mul_pow, ← Finset.prod_pow]
  have h : ∀ a ∈ (Finset.univ : Finset (Fin r)),
      (‖lam r sc a * q.1 a‖ ^ 2) ^ (k - 1) * (‖lam r sc a * q.1 a‖ ^ 4) ^ (r - a.1) =
        ‖lam r sc a‖ ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2)) * ‖q.1 a‖ ^ (2 * (Formalism.QuantumDeterminants.Mdim k r a - 2)) := by
    intro a _
    have e : 2 * (Formalism.QuantumDeterminants.Mdim k r a - 2) = 2 * (k - 1) + 4 * (r - a.1) := by
      unfold Formalism.QuantumDeterminants.Mdim
      omega
    rw [e, norm_mul]
    ring
  have hp := Finset.prod_congr rfl h
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at hp
  linear_combination (Complex.normSq q.2 - T * T') ^ (k - 1) * hp

def Gi (r k : ℕ) (T T' : ℝ) (F : (Fin (r + 1) → ℂ) → ℝ≥0∞) : (Fin (r + 1) → ℂ) → ℝ≥0∞ :=
  (GoodLoc (r := r) T T').indicator fun c => ENNReal.ofReal (wtLoc k T T' c) * F c

def nrm (r : ℕ) (sc : ℝ) : ℝ := Complex.normSq (∏ a, lam r sc a)

theorem lam_ne {r : ℕ} {sc : ℝ} (hsc : 0 < sc) (a : Fin r) : lam r sc a ≠ 0 := by
  unfold lam
  exact pow_ne_zero _ (inv_ne_zero (pow_ne_zero _ (by exact_mod_cast hsc.ne')))

def Lsc (r : ℕ) (sc : ℝ) (hsc : 0 < sc) : (Fin r → ℂ) ≃ᵐ (Fin r → ℂ) where
  toFun v a := lam r sc a * v a
  invFun v a := (lam r sc a)⁻¹ * v a
  left_inv v := funext fun a => inv_mul_cancel_left₀ (lam_ne hsc a) (v a)
  right_inv v := funext fun a => mul_inv_cancel_left₀ (lam_ne hsc a) (v a)
  measurable_toFun := by
    show Measurable fun v : Fin r → ℂ => fun a => lam r sc a * v a
    fun_prop
  measurable_invFun := by
    show Measurable fun v : Fin r → ℂ => fun a => (lam r sc a)⁻¹ * v a
    fun_prop

def Phe (r : ℕ) (sc : ℝ) (hsc : 0 < sc) : ((Fin r → ℂ) × ℂ) ≃ᵐ (Fin (r + 1) → ℂ) :=
  ((MeasurableEquiv.prodCongr (Lsc r sc hsc) (MeasurableEquiv.refl ℂ)).trans MeasurableEquiv.prodComm).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (r + 1) => ℂ) (Fin.last r)).symm

theorem phe_apply {r : ℕ} {sc : ℝ} (hsc : 0 < sc) (q : (Fin r → ℂ) × ℂ) : Phe r sc hsc q = coordSc r sc q := by
  funext i
  simp [Phe, Lsc, coordSc, MeasurableEquiv.piFinSuccAbove_symm_apply, lam]
  rfl

theorem map_Lsc {r : ℕ} {sc : ℝ} (hsc : 0 < sc) :
    (volume : Measure (Fin r → ℂ)).map (Lsc r sc hsc) = ENNReal.ofReal (nrm r sc)⁻¹ • volume := by
  have hnrm : 0 < nrm r sc :=
    Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => lam_ne hsc a)
  let f : (Fin r → ℂ) →ₗ[ℝ] (Fin r → ℂ) :=
    LinearMap.pi fun a => (Algebra.lmul ℝ ℂ (lam r sc a)).comp (LinearMap.proj a)
  have hf : ⇑(Lsc r sc hsc) = ⇑f := by
    funext v
    rfl
  have hdet : LinearMap.det f = nrm r sc := by
    rw [LinearMap.det_pi]
    simp_rw [← Algebra.norm_apply, Algebra.norm_complex_apply]
    rw [nrm, map_prod]
  rw [hf, Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hdet]; exact hnrm.ne'), hdet,
    abs_of_pos (inv_pos.2 hnrm)]

theorem map_Phe {r : ℕ} {sc : ℝ} (hsc : 0 < sc) :
    (volume : Measure ((Fin r → ℂ) × ℂ)).map (Phe r sc hsc) = ENNReal.ofReal (nrm r sc)⁻¹ • volume := by
  have e1 : (volume : Measure ((Fin r → ℂ) × ℂ)).map
      (MeasurableEquiv.prodCongr (Lsc r sc hsc) (MeasurableEquiv.refl ℂ)) =
        ENNReal.ofReal (nrm r sc)⁻¹ • volume := by
    have hc : ⇑(MeasurableEquiv.prodCongr (Lsc r sc hsc) (MeasurableEquiv.refl ℂ)) =
        Prod.map (Lsc r sc hsc) id := rfl
    rw [Measure.volume_eq_prod, hc, ← Measure.map_prod_map _ _ (Lsc r sc hsc).measurable measurable_id,
      map_Lsc hsc, Measure.map_id, Measure.prod_smul_left]
  have e2 := Measure.measurePreserving_swap (μ := (volume : Measure (Fin r → ℂ))) (ν := (volume : Measure ℂ))
  have e3 := (measurePreserving_piFinSuccAbove (fun _ : Fin (r + 1) => (volume : Measure ℂ)) (Fin.last r)).symm
  have hs : ⇑(MeasurableEquiv.prodComm : ((Fin r → ℂ) × ℂ) ≃ᵐ (ℂ × (Fin r → ℂ))) = Prod.swap := rfl
  unfold Phe
  rw [MeasurableEquiv.coe_trans, MeasurableEquiv.coe_trans, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) (by fun_prop), e1, Measure.map_smul, Measure.map_smul, hs,
    Measure.volume_eq_prod, e2.map_eq]
  congr 1
  exact e3.map_eq

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL.CoordinateScalingProducts

namespace Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL

open Formalism.L2.SG.RealObj CoordinateScalingProducts

private theorem dcLoc_eq_formula (r : ℕ) :
    dcLoc (r := r) = (2 : ℝ≥0∞) ^ (r + 1) • (volume : Measure (Fin (r + 1) → ℂ)) := by
  unfold dcLoc
  have : SigmaFinite ((2 : ℝ≥0∞) • (volume : Measure ℂ)) := by
    have h2 : (2 : ℝ≥0∞) = ((2 : NNReal) : ℝ≥0∞) := rfl
    rw [h2, ← ENNReal.smul_def]
    infer_instance
  refine Measure.pi_eq fun s _ => ?_
  rw [Measure.smul_apply, volume_pi, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

private theorem measurableSet_goodLoc' (r : ℕ) (T T' : ℝ) : MeasurableSet (GoodLoc (r := r) T T') := by
  have hc : Continuous fun c : Fin (r + 1) → ℂ => Gv T T' (Matrix.diagonal c) := by
    simp only [Gv, dl_diag _ (r + 1) le_rfl, dl_diag _ r (Nat.le_succ r)]
    fun_prop
  rw [GoodLoc, Set.ofPred_and, Set.ofPred_forall]
  refine (MeasurableSet.iInter fun l => ?_).inter (measurableSet_lt measurable_const hc.measurable)
  exact (measurable_pi_apply l) (measurableSet_singleton 0).compl

private theorem volume_normSq_snd_eq_const_eq_zero {r : ℕ} {T T' : ℝ} :
    (volume : Measure ((Fin r → ℂ) × ℂ)) {q | Complex.normSq q.2 = T * T'} = 0 := by
  have hS : {z : ℂ | Complex.normSq z = T * T'} ⊆ Metric.sphere 0 (Real.sqrt (T * T')) := by
    intro z hz
    simp only [Set.mem_ofPred_eq] at hz
    rw [mem_sphere_zero_iff_norm, ← hz, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have h0 : (volume : Measure ℂ) {z : ℂ | Complex.normSq z = T * T'} = 0 :=
    measure_mono_null hS (Measure.addHaar_sphere volume 0 _)
  have he : {q : (Fin r → ℂ) × ℂ | Complex.normSq q.2 = T * T'} =
      Set.univ ×ˢ {z : ℂ | Complex.normSq z = T * T'} := by
    ext q
    simp
  rw [he, Measure.volume_eq_prod, Measure.prod_prod, h0, mul_zero]

theorem coordW_holds : CoordW := by
  intro r k T T' sc hk hT hT' hsc
  have hnrm : 0 < nrm r sc :=
    Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => lam_ne hsc a)
  have hlamW : 0 < lamW r k sc :=
    Finset.prod_pos fun a _ => pow_pos (norm_pos_iff.2 (lam_ne hsc a)) _
  have hTT : 0 < T * T' := mul_pos hT hT'
  set C : ℝ := 2 ^ (r + 1) * nrm r sc * lamW r k sc with hC
  have hCpos : 0 < C := by positivity
  refine ⟨C⁻¹, inv_pos.2 hCpos, fun F => ?_⟩
  have hae : (fun q => (GoodLoc (r := r) T T').indicator
      (fun c => ENNReal.ofReal (wtLoc k T T' c) * F c) (Phe r sc hsc q)) =ᵐ[volume]
      fun q => ENNReal.ofReal (lamW r k sc) *
        (ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r sc q)) := by
    have hq : ∀ᵐ q : (Fin r → ℂ) × ℂ ∂volume, Complex.normSq q.2 ≠ T * T' := by
      rw [ae_iff]
      simpa using volume_normSq_snd_eq_const_eq_zero (r := r) (T := T) (T' := T')
    filter_upwards [hq] with q hq
    rw [phe_apply]
    by_cases hg : coordSc r sc q ∈ GoodLoc (r := r) T T'
    · rw [Set.indicator_of_mem hg, wt_cs hk, ENNReal.ofReal_mul hlamW.le, mul_assoc]
      have hG := hg.2
      rw [gv_cs] at hG
      have hp : 0 ≤ ∏ a : Fin r, ‖lam r sc a * q.1 a‖ ^ 2 :=
        Finset.prod_nonneg fun _ _ => by positivity
      have hN : T * T' < Complex.normSq q.2 := by
        by_contra h
        rw [not_lt] at h
        have := mul_nonpos_of_nonneg_of_nonpos hp (by linarith : Complex.normSq q.2 - T * T' ≤ 0)
        linarith
      unfold Formalism.QuantumDeterminants.bcWeight
      rw [if_pos hN.le]
    · rw [Set.indicator_of_notMem hg]
      have hb : Formalism.QuantumDeterminants.bcWeight k r T T' q = 0 := by
        unfold Formalism.QuantumDeterminants.bcWeight
        split_ifs with hle
        · have hlt : T * T' < Complex.normSq q.2 := lt_of_le_of_ne hle (Ne.symm hq)
          by_cases hall : ∀ a, q.1 a ≠ 0
          · exfalso
            apply hg
            refine ⟨fun l => ?_, ?_⟩
            · induction l using Fin.lastCases with
              | last =>
                rw [coordSc_last]
                intro h0
                rw [h0, map_zero] at hlt
                linarith
              | cast a =>
                rw [coordSc_cs]
                exact mul_ne_zero (lam_ne hsc a) (hall a)
            · rw [gv_cs]
              exact mul_pos (Finset.prod_pos fun a _ =>
                pow_pos (norm_pos_iff.2 (mul_ne_zero (lam_ne hsc a) (hall a))) 2) (by linarith)
          · simp only [not_forall, not_not] at hall
            obtain ⟨a, ha⟩ := hall
            rw [Finset.prod_eq_zero (Finset.mem_univ a), zero_mul]
            rw [ha, norm_zero]
            apply zero_pow
            unfold Formalism.QuantumDeterminants.Mdim
            omega
        · rfl
      rw [hb]
      simp
  have key : ∫⁻ c in GoodLoc (r := r) T T', ENNReal.ofReal (wtLoc k T T' c) * F c ∂(dcLoc (r := r)) =
      ENNReal.ofReal C * ∫⁻ q : (Fin r → ℂ) × ℂ,
        ENNReal.ofReal (Formalism.QuantumDeterminants.bcWeight k r T T' q) * F (coordSc r sc q) := by
    rw [dcLoc_eq_formula, Measure.restrict_smul, lintegral_smul_measure,
      ← lintegral_indicator (measurableSet_goodLoc' r T T')]
    have hvol : (volume : Measure (Fin (r + 1) → ℂ)) =
        ENNReal.ofReal (nrm r sc) • (volume.map (Phe r sc hsc)) := by
      rw [map_Phe hsc, smul_smul, ← ENNReal.ofReal_mul hnrm.le, mul_inv_cancel₀ hnrm.ne',
        ENNReal.ofReal_one, one_smul]
    rw [hvol, lintegral_smul_measure, lintegral_map_equiv, lintegral_congr_ae hae,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hC, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
    simp only [smul_eq_mul, ENNReal.ofReal_ofNat]
    ring
  rw [key, ← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.2 hCpos).le, inv_mul_cancel₀ hCpos.ne',
    ENNReal.ofReal_one, one_mul]

end Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.JL
