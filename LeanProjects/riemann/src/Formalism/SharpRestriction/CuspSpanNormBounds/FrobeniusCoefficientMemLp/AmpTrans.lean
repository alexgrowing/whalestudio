import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpRootCut
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.LowestKTypeMultiplicity

open MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpTrans

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

theorem quot_meas_not_mem_UH_eq_zero {μG μS ν : Measure (Mt k r)} (hG : IsHaarOn (UH (Hpk k r)) μG) (hS0 : μS ≠ 0)
    (hSc : μS {x | Matrix.of x ∉ UH (Hpk k r)} = 0) (hq : IsQuotMeas μG μS ν) :
    ν {x | Matrix.of x ∉ UH (Hpk k r)} = 0 := by
  have hA : MeasurableSet {x : Mt k r | Matrix.of x ∈ UH (Hpk k r)} := by
    have hc : IsClosed {x : Mt k r | (Matrix.of x)ᴴ * Hpk k r * Matrix.of x = Hpk k r} := by
      apply isClosed_eq
      · exact ((Continuous.matrix_conjTranspose continuous_id).matrix_mul continuous_const).matrix_mul continuous_id
      · exact continuous_const
    exact hc.measurableSet
  have hN : MeasurableSet {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)} := hA.compl
  have hint := hq ({x : Mt k r | Matrix.of x ∉ UH (Hpk k r)}.indicator 1) (measurable_one.indicator hN)
  rw [lintegral_indicator_one hN, hG.2.2.1] at hint
  have hmass : μS Set.univ ≠ 0 := fun h => hS0 (Measure.measure_univ_eq_zero.mp h)
  have hSc' : μS {s : Mt k r | Matrix.of s ∈ UH (Hpk k r)}ᶜ = 0 := hSc
  have hlow : ∀ x ∈ {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)}, μS Set.univ ≤
      ∫⁻ s, {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)}.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS := by
    intro x hx
    have hsub : ∀ s ∈ {s : Mt k r | Matrix.of s ∈ UH (Hpk k r)},
        (fun i j => (Matrix.of s * Matrix.of x) i j) ∈ {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)} := by
      intro s hs hsx
      apply hx
      have e1 : (Matrix.of s * Matrix.of x)ᴴ * Hpk k r * (Matrix.of s * Matrix.of x) = Hpk k r := hsx
      have e2 : (Matrix.of s)ᴴ * Hpk k r * Matrix.of s = Hpk k r := hs
      show (Matrix.of x)ᴴ * Hpk k r * Matrix.of x = Hpk k r
      calc (Matrix.of x)ᴴ * Hpk k r * Matrix.of x
          = (Matrix.of x)ᴴ * ((Matrix.of s)ᴴ * Hpk k r * Matrix.of s) * Matrix.of x := by rw [e2]
        _ = (Matrix.of s * Matrix.of x)ᴴ * Hpk k r * (Matrix.of s * Matrix.of x) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = Hpk k r := e1
    calc μS Set.univ = μS ({s : Mt k r | Matrix.of s ∈ UH (Hpk k r)} ∪ {s : Mt k r | Matrix.of s ∈ UH (Hpk k r)}ᶜ) := by
          rw [Set.union_compl_self]
      _ ≤ μS {s : Mt k r | Matrix.of s ∈ UH (Hpk k r)} + μS {s : Mt k r | Matrix.of s ∈ UH (Hpk k r)}ᶜ :=
          measure_union_le _ _
      _ = μS {s : Mt k r | Matrix.of s ∈ UH (Hpk k r)} := by rw [hSc', add_zero]
      _ = ∫⁻ s, {s : Mt k r | Matrix.of s ∈ UH (Hpk k r)}.indicator 1 s ∂μS := (lintegral_indicator_one hA).symm
      _ ≤ _ := lintegral_mono (fun s => by
            by_cases hs : s ∈ {s : Mt k r | Matrix.of s ∈ UH (Hpk k r)}
            · rw [Set.indicator_of_mem hs, Set.indicator_of_mem (hsub s hs)]; exact le_rfl
            · rw [Set.indicator_of_notMem hs]; exact zero_le)
  have hge : μS Set.univ * ν {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)} ≤
      ∫⁻ x, ∫⁻ s, {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)}.indicator 1
        (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ∂ν := by
    rw [← lintegral_indicator_const hN]
    exact lintegral_mono (fun x => by
      by_cases hx : x ∈ {x : Mt k r | Matrix.of x ∉ UH (Hpk k r)}
      · rw [Set.indicator_of_mem hx]; exact hlow x hx
      · rw [Set.indicator_of_notMem hx]; exact zero_le)
  rw [← hint] at hge
  rcases mul_eq_zero.mp (le_zero_iff.mp hge) with h | h
  · exact absurd h hmass
  · exact h

def lmulE (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ha : IsUnit a.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := fun i j => (a * Matrix.of x) i j
  invFun x := fun i j => (a⁻¹ * Matrix.of x) i j
  left_inv x := by
    funext i j
    show (a⁻¹ * (a * Matrix.of x)) i j = x i j
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul]; rfl
  right_inv x := by
    funext i j
    show (a * (a⁻¹ * Matrix.of x)) i j = x i j
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul]; rfl
  measurable_toFun := by
    apply Continuous.measurable
    exact continuous_pi fun i => continuous_pi fun j => (continuous_const.matrix_mul continuous_id).matrix_elem i j
  measurable_invFun := by
    apply Continuous.measurable
    exact continuous_pi fun i => continuous_pi fun j => (continuous_const.matrix_mul continuous_id).matrix_elem i j

def conjE (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ha : IsUnit a.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := fun i j => (a⁻¹ * Matrix.of x * a) i j
  invFun x := fun i j => (a * Matrix.of x * a⁻¹) i j
  left_inv x := by
    funext i j
    show (a * (a⁻¹ * Matrix.of x * a) * a⁻¹) i j = x i j
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ ha, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul]; rfl
  right_inv x := by
    funext i j
    show (a⁻¹ * (a * Matrix.of x * a⁻¹) * a) i j = x i j
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ ha, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ha, Matrix.one_mul]; rfl
  measurable_toFun := Formalism.MainNotions.S.Pv.LemmaJ.measurable_conjL _ _
  measurable_invFun := Formalism.MainNotions.S.Pv.LemmaJ.measurable_conjL _ _

theorem quot_transport {μG μ₀ νR : Measure (Mt k r)} (hG : IsHaarOn (UH (Hpk k r)) μG)
    {n' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hn' : n' ∈ UH (Hpk k r)) (θ' : ℝ)
    (hq : IsQuotMeas μG (ENNReal.ofReal θ' • μ₀.map (fun x => fun i j => (n'⁻¹ * Matrix.of x * n') i j)) νR) :
    IsQuotMeas μG μ₀ (ENNReal.ofReal θ' • νR.map (fun x => fun i j => (n' * Matrix.of x) i j)) := by
  intro f hf
  have hH : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  have hn'' : n'ᴴ * Hpk k r * n' = Hpk k r := hn'
  have hleft : (Hpk k r * n'ᴴ * Hpk k r) * n' = 1 := by
    simp only [Matrix.mul_assoc] at hn'' ⊢
    rw [hn'', hH]
  have ha : IsUnit n'.det := Matrix.isUnit_det_of_left_inverse hleft
  have hc : ENNReal.ofReal θ' ≠ ⊤ := ENNReal.ofReal_ne_top
  have hinv : μG.map (lmulE n' ha) = μG := hG.2.2.2 n' hn'
  have hL : νR.map (fun x => fun i j => (n' * Matrix.of x) i j) = νR.map (lmulE n' ha) := rfl
  calc ∫⁻ x, f x ∂μG = ∫⁻ x, f (lmulE n' ha x) ∂μG := by
        conv_lhs => rw [← hinv]
        exact lintegral_map_equiv _ _
    _ = ∫⁻ x, ∫⁻ s, f (lmulE n' ha (fun i j => (Matrix.of s * Matrix.of x) i j))
          ∂(ENNReal.ofReal θ' • μ₀.map (conjE n' ha)) ∂νR :=
        hq _ (hf.comp (lmulE n' ha).measurable)
    _ = ∫⁻ x, ENNReal.ofReal θ' * ∫⁻ s, f (lmulE n' ha
          (fun i j => (Matrix.of (conjE n' ha s) * Matrix.of x) i j)) ∂μ₀ ∂νR := by
        simp_rw [lintegral_smul_measure, smul_eq_mul, lintegral_map_equiv]
    _ = ENNReal.ofReal θ' * ∫⁻ x, ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of (lmulE n' ha x)) i j) ∂μ₀ ∂νR := by
        rw [lintegral_const_mul' _ _ hc]
        congr 1
        refine lintegral_congr (fun x => lintegral_congr (fun s => ?_))
        congr 1
        funext i j
        show (n' * (n'⁻¹ * Matrix.of s * n' * Matrix.of x)) i j = (Matrix.of s * (n' * Matrix.of x)) i j
        simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ha, Matrix.one_mul]
    _ = _ := by
        rw [lintegral_smul_measure, smul_eq_mul, hL, lintegral_map_equiv]

theorem norm_psi (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ‖psi k r z c g‖ = 1 := by
  unfold psi
  rw [mul_comm Complex.I]
  exact Complex.norm_exp_ofReal_mul_I _

theorem smulRight_smul_smul {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F]
    [NormedSpace ℂ F] (a b : ℂ) (u : E) (v : F) :
    (innerSL ℂ (a • u)).smulRight (b • v) = (star a * b) • (innerSL ℂ u).smulRight v := by
  ext x
  rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    smul_smul, smul_smul]
  congr 1
  have h1 : (innerSL ℂ (a • u)) x = star a * (innerSL ℂ u) x := by
    simp [inner_smul_left, Complex.star_def]
  rw [h1]
  ring

theorem amplitude_transport : Formalism.MainNotions.S.Pv.LemmaJ.AmpTransport := by
  intro D τ w w' θ W hW lam' A hA hT hT' n n' g₀ hn hn' hg₀ θ' hθ' μ₀ νR hμ₀ hq
  have hG : IsHaarOn (UH (Hpk D.R.k D.R.rS)) W.μG := hW.2.2.2.2.2.2.1
  refine ⟨quot_transport hG hn'.1 θ' hq, ?_⟩
  have hH : Hpk D.R.k D.R.rS * Hpk D.R.k D.R.rS = 1 := (hpkFacts D.R.k D.R.rS).2.1
  have hHdet : IsUnit (Hpk D.R.k D.R.rS).det := Matrix.isUnit_det_of_left_inverse hH
  have hUH := uHGroup _ (Hpk D.R.k D.R.rS) hHdet
  have hn'U : n' ∈ UH (Hpk D.R.k D.R.rS) := hn'.1
  have hnU : n ∈ UH (Hpk D.R.k D.R.rS) := hn.1
  have ha : IsUnit n'.det := (hUH.2.2 n' hn'U).1
  have hn'inv : n'⁻¹ ∈ UH (Hpk D.R.k D.R.rS) := (hUH.2.2 n' hn'U).2
  set μS := ENNReal.ofReal θ' • μ₀.map (fun x => fun i j => (n'⁻¹ * Matrix.of x * n') i j) with hμS
  have hS0 : μS ≠ 0 := by
    intro h0
    have h1 := hq (fun _ => 1) measurable_const
    rw [h0] at h1
    simp at h1
    exact hG.2.1 h1
  have hSc : μS {x | Matrix.of x ∉ UH (Hpk D.R.k D.R.rS)} = 0 := by
    rw [hμS, Measure.smul_apply, smul_eq_mul,
      show (fun x : Mt D.R.k D.R.rS => fun i j => (n'⁻¹ * Matrix.of x * n') i j) = ⇑(conjE n' ha) from rfl,
      MeasurableEquiv.map_apply]
    refine mul_eq_zero_of_right _ (measure_mono_null ?_ hμ₀)
    intro x hx hR
    apply hx
    have hxU : Matrix.of x ∈ UH (Hpk D.R.k D.R.rS) := hR.1.1
    show n'⁻¹ * Matrix.of x * n' ∈ UH (Hpk D.R.k D.R.rS)
    exact hUH.2.1 _ (hUH.2.1 _ hn'inv _ hxU) _ hn'U
  have hνUH : ∀ᵐ x ∂νR, Matrix.of x ∈ UH (Hpk D.R.k D.R.rS) :=
    ae_iff.2 (quot_meas_not_mem_UH_eq_zero hG hS0 hSc hq)
  have hσ := Formalism.MainNotions.LowestKTypeMultiplicity.urep_of_DS hA.2.1
  have hv0 := hA.2.2.2.2.1
  have hπ1 : W.π 1 = 1 := (Formalism.MainNotions.LowestKTypeMultiplicity.rp_repOfHC _ _ _ _ _ _ hW.2.2.1
    (by rw [hW.2.2.2.2.1]; exact hT) hW.1).1.1
  have hπ'1 : W.π' 1 = 1 := (Formalism.MainNotions.LowestKTypeMultiplicity.rp_repOfHC _ _ _ _ _ _ hW.2.2.2.1
    (by rw [hW.2.2.2.2.2.1]; exact hT') hW.2.1).1.1
  have h1W : ∀ z : Fin (2 * D.R.rS + D.R.k + 1) → ℂ,
      (1 : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) ∈
        UWset D.R.k D.R.rS z := by
    intro z
    exact ⟨hUH.1, fun a => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩
  have hΦ : ∀ g ∈ UH (Hpk D.R.k D.R.rS), A.Φ (n * g) = psiS D W.z n • A.Φ g := by
    intro g hg
    have h2 := hA.2.2.1.2.2.1 1 (h1W W.z) n hn (A.σ g A.v0)
      (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hv0 hg)
    rw [one_mul, hπ1, ContinuousLinearMap.one_apply] at h2
    simp only [LocS.Φ]
    rw [hσ.1.2 n hnU g hg, ContinuousLinearMap.comp_apply]
    exact h2
  have hΦ' : ∀ g ∈ UH (Hpk D.R.k D.R.rS), A.Φ' (n' * g) = psiS D W.z' n' • A.Φ' g := by
    intro g hg
    have h2 := hA.2.2.2.1.2.2.1 1 (h1W W.z') n' hn' (A.σ g A.v0)
      (Formalism.MainNotions.LowestKTypeMultiplicity.smooth_orbit hσ hv0 hg)
    rw [one_mul, hπ'1, ContinuousLinearMap.one_apply] at h2
    simp only [LocS.Φ']
    rw [hσ.1.2 n' hn'U g hg, ContinuousLinearMap.comp_apply]
    exact h2
  set K : W.Wq →L[ℂ] W.Wp := ((A.cN : ℂ))⁻¹ • ∫ x, (innerSL ℂ (A.Φ' (Matrix.of x))).smulRight
    (A.Φ (g₀ * (n' * Matrix.of x))) ∂νR with hKdef
  have hL : A.J νR (n * g₀ * n') = psiS D W.z n • K := by
    simp only [LocS.J, ampJ, hKdef]
    rw [smul_comm (psiS D W.z n), ← integral_smul (psiS D W.z n)]
    congr 1
    refine integral_congr_ae (hνUH.mono fun x hx => ?_)
    simp only
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hΦ _ (hUH.2.1 _ hg₀ _ (hUH.2.1 _ hn'U _ hx))]
    have h := smulRight_smul_smul (1 : ℂ) (psiS D W.z n) (A.Φ' (Matrix.of x))
      (A.Φ (g₀ * (n' * Matrix.of x)))
    rw [one_smul, star_one, one_mul] at h
    exact h
  have hR : A.J (ENNReal.ofReal θ' • νR.map (fun x => fun i j => (n' * Matrix.of x) i j)) g₀ =
      ((θ' : ℂ) * star (psiS D W.z' n')) • K := by
    simp only [LocS.J, ampJ, hKdef]
    rw [integral_smul_measure,
      show (fun x : Mt D.R.k D.R.rS => fun i j => (n' * Matrix.of x) i j) = ⇑(lmulE n' ha) from rfl,
      integral_map_equiv, ENNReal.toReal_ofReal hθ'.le]
    have hI : ∫ x, (innerSL ℂ (A.Φ' (Matrix.of (lmulE n' ha x)))).smulRight
        (A.Φ (g₀ * Matrix.of (lmulE n' ha x))) ∂νR =
        star (psiS D W.z' n') • ∫ x, (innerSL ℂ (A.Φ' (Matrix.of x))).smulRight
          (A.Φ (g₀ * (n' * Matrix.of x))) ∂νR := by
      rw [← integral_smul (star (psiS D W.z' n'))]
      refine integral_congr_ae (hνUH.mono fun x hx => ?_)
      show (innerSL ℂ (A.Φ' (n' * Matrix.of x))).smulRight (A.Φ (g₀ * (n' * Matrix.of x))) = _
      rw [hΦ' _ hx]
      have h := smulRight_smul_smul (psiS D W.z' n') (1 : ℂ) (A.Φ' (Matrix.of x))
        (A.Φ (g₀ * (n' * Matrix.of x)))
      rw [one_smul, mul_one] at h
      exact h
    rw [hI, ← Complex.coe_smul]
    simp only [smul_smul]
    congr 1
    ring
  rw [hL, hR, Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_smul (psiS D W.z n) K,
    Formalism.MainNotions.BesselShellMomentBounds.hsNormSq_smul ((θ' : ℂ) * star (psiS D W.z' n')) K]
  have hψ : ‖psiS D W.z n‖ = 1 := by
    unfold psiS
    exact norm_psi _ _ _
  have hψ' : ‖(θ' : ℂ) * star (psiS D W.z' n')‖ = θ' := by
    have h1 : ‖psiS D W.z' n'‖ = 1 := by
      unfold psiS
      exact norm_psi _ _ _
    rw [norm_mul, norm_star, h1, mul_one, Complex.norm_real, Real.norm_of_nonneg hθ'.le]
  rw [hψ, hψ', ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [one_pow, one_mul, _root_.zpow_neg, zpow_ofNat, ← mul_assoc,
    inv_mul_cancel₀ (by positivity), one_mul]

end Formalism.MainNotions.S.Pv.AmpTrans
