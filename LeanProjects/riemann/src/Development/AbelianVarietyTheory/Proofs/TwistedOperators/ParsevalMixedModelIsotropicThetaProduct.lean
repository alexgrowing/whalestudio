import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesSummableOnCovolumeDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertie
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicDualMiddlePartsSymplecticOrthogonal

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixParsevalPoint

variable {D : D7}

private theorem heisO_apply (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (w : WO S T) (g : WO S T → ℂ)
    (z : WO S T) : heisO ψ S T w g z = ψ (symplOH S T z w) * g (z + w) := by
  simp only [heisO]

private theorem symplOH_zero_left_twisted_operators (S T : HSp D) (p : WO S T) : symplOH S T 0 p = 0 := by
  have h := GlobalTheory.OrientedHeis.symplOH_add_left (0 : WO S T) 0 p
  rw [zero_add] at h
  linear_combination -h

private theorem mul_mul_conj_mul_eq_of_mul_conj_eq_one (p a b : ℂ) (hp : p * starRingEnd ℂ p = 1) :
    p * a * starRingEnd ℂ (p * b) = a * starRingEnd ℂ b := by
  rw [map_mul]
  linear_combination (a * starRingEnd ℂ b) * hp

theorem psi_mul_conj {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    ψ a * starRingEnd ℂ (ψ a) = 1 := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
  norm_num

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (a : AF D.host.F) :
    starRingEnd ℂ (ψ a) = ψ (-a) := by
  have h1 : ‖ψ a‖ = 1 := hψ.1.2.1 a
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, h1]
  norm_num

theorem symplOH_eq (S T : HSp D) (a b : WO S T) :
    symplOH S T a b = algebraMap D.host.F (AF D.host.F) (1 / 2) * symplO S T a b := rfl

private theorem heisO_isoPart_incA_add_apply_eq_psi_mul {V V' W : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    (h2 : adj D C' * V.gram * C' = 0) (h3 : adj D C' * V.gram * B = 0) (ψ : AddChar (AF D.host.F) ℂ)
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (x : WO V' W) (u : Mx D W.rank r)
    (ξ : Matrix (Fin W.rank) (Fin r) D.host.E) (y : Mx D W.rank r) :
    heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f (isoPart V W C y + midPart V V' W B x) =
      ψ (symplO V W (isoPart V W C y) (isoPart V W C' (ξ.map (incA D)))) *
        heisO ψ V W (isoPart V W C' u) f (isoPart V W C y + midPart V V' W B x) := by
  have orth := GlobalTheory.TwistFormsOrth.orthogonal D V V' W r C B hs C' h1 h2 h3
  have hrat : isoPart V W C' (ξ.map (incA D)) ∈ ratL W V := GlobalTheory.TowerRestrict.isoPart_rat C' ⟨ξ, rfl⟩
  have eXU : symplOH V W (isoPart V W C' (ξ.map (incA D))) (isoPart V W C' u) = 0 := by
    rw [symplOH_eq, orth.2.2.2 _ _, mul_zero]
  have e1 := GlobalTheory.OrientedHeis.heisO_heisO (ψ := ψ) (isoPart V W C' (ξ.map (incA D))) (isoPart V W C' u) f
  rw [eXU, AddChar.map_zero_eq_one, one_smul, ← GlobalTheory.TowerRestrict.isoPart_add C'] at e1
  rw [← e1, heisO_apply ψ (isoPart V W C' (ξ.map (incA D))) (heisO ψ V W (isoPart V W C' u) f),
    add_comm (isoPart V W C y + midPart V V' W B x) _, GlobalTheory.HeisOrtho.heisO_quasi hf _ _ hrat, ← mul_assoc,
    ← AddChar.map_add_eq_mul]
  congr 2
  rw [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right]
  have s1 := GlobalTheory.TwFour.symplOH_sub V W (isoPart V W C y) (isoPart V W C' (ξ.map (incA D)))
  have s2 := GlobalTheory.TwFour.symplOH_sub V W (midPart V V' W B x) (isoPart V W C' (ξ.map (incA D)))
  have s3 := GlobalTheory.OrientedHeis.symplO_skew (isoPart V W C' (ξ.map (incA D))) (midPart V V' W B x)
  rw [orth.2.2.1 _ _, neg_zero] at s3
  rw [s3] at s2
  linear_combination s1 + s2

theorem coef_eq {V V' W : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    (h2 : adj D C' * V.gram * C' = 0) (h3 : adj D C' * V.gram * B = 0) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (x : WO V' W) (u : Mx D W.rank r) (ξ : Matrix (Fin W.rank) (Fin r) D.host.E) :
    res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f) x =
      ∫ y in 𝓨, ψ (symplO V W (isoPart V W C y) (isoPart V W C' (ξ.map (incA D)))) *
        heisO ψ V W (isoPart V W C' u) f (isoPart V W C y + midPart V V' W B x) ∂μ := by
  simp only [res]
  exact MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun y => heisO_isoPart_incA_add_apply_eq_psi_mul hs h1 h2 h3 ψ hf x u ξ y)

theorem res_smul {V V' W : HSp D} {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r))
    (c : ℂ) (g : WO V W → ℂ) (x : WO V' W) : res V V' W C B μ 𝓨 (c • g) x = c * res V V' W C B μ 𝓨 g x := by
  simp only [res, Pi.smul_apply, smul_eq_mul]
  exact MeasureTheory.integral_const_mul c _

theorem expand {V V' W : HSp D} {r : ℕ} {C C' : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    (h2 : adj D C' * V.gram * C' = 0) (h3 : adj D C' * V.gram * B = 0) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (hcov : IsCovolOne (ratMx D W.rank r) μ 𝓨) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (x : WO V' W) (u y₀ : Mx D W.rank r) :
    Summable (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E =>
      ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f) x‖) ∧
    HasSum (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E =>
      ψ (symplO V W (isoPart V W C' (ξ.map (incA D))) (isoPart V W C y₀)) *
        res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f) x)
      (heisO ψ V W (isoPart V W C' u) f (isoPart V W C y₀ + midPart V V' W B x)) := by
  have orth := GlobalTheory.TwistFormsOrth.orthogonal D V V' W r C B hs C' h1 h2 h3
  have hUf : IsThetaFunO ψ V W (heisO ψ V W (isoPart V W C' u) f) :=
    GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _
  have hMf : IsThetaFunO ψ V W (heisO ψ V W (midPart V V' W B x) (heisO ψ V W (isoPart V W C' u) f)) :=
    GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hUf _
  have hF := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hMf (isoPart V W C y₀)
  obtain ⟨hs1, hs2⟩ := GlobalTheory.TwFour.value_zero_eq_sum_restrictions D V V' W r C C' B hs h1 h2 h3 ψ hψ μ 𝓨 hcov _ hF
  have key : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E,
      res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D)))
        (heisO ψ V W (isoPart V W C y₀) (heisO ψ V W (midPart V V' W B x) (heisO ψ V W (isoPart V W C' u) f)))) 0 =
        ψ (symplO V W (isoPart V W C' (ξ.map (incA D))) (isoPart V W C y₀)) *
          res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f) x := by
    intro ξ
    have eXM : symplO V W (isoPart V W C' (ξ.map (incA D))) (midPart V V' W B x) = 0 := orth.2.2.1 _ _
    have eXU : symplOH V W (isoPart V W C' (ξ.map (incA D))) (isoPart V W C' u) = 0 := by
      rw [symplOH_eq, orth.2.2.2 _ _, mul_zero]
    have hG : IsThetaFunO ψ V W (heisO ψ V W (midPart V V' W B x) (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f)) :=
      GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _) _
    rw [GlobalTheory.TwFour.heisO_comm (isoPart V W C' (ξ.map (incA D))) (isoPart V W C y₀),
      GlobalTheory.TwFour.heisO_comm (isoPart V W C' (ξ.map (incA D))) (midPart V V' W B x), eXM, AddChar.map_zero_eq_one,
      one_smul, GlobalTheory.OrientedHeis.heisO_heisO (ψ := ψ) (isoPart V W C' (ξ.map (incA D))) (isoPart V W C' u) f, eXU,
      AddChar.map_zero_eq_one, one_smul, ← GlobalTheory.TowerRestrict.isoPart_add C', res_smul,
      GlobalTheory.TowerRestrict.res_heis_iso hs hcov hG, GlobalTheory.TowerRestrict.res_heis_mid hs, heisO_apply,
      symplOH_zero_left_twisted_operators, AddChar.map_zero_eq_one, one_mul, zero_add]
  have hAM : symplOH V W (isoPart V W C y₀) (midPart V V' W B x) = 0 := by
    rw [symplOH_eq, orth.2.1 _ _, mul_zero]
  have F0 : heisO ψ V W (isoPart V W C y₀) (heisO ψ V W (midPart V V' W B x) (heisO ψ V W (isoPart V W C' u) f)) 0 =
      heisO ψ V W (isoPart V W C' u) f (isoPart V W C y₀ + midPart V V' W B x) := by
    rw [heisO_apply, heisO_apply ψ (midPart V V' W B x), symplOH_zero_left_twisted_operators, zero_add, hAM,
      AddChar.map_zero_eq_one, one_mul, one_mul]
  refine ⟨hs1.congr fun ξ => ?_, ?_⟩
  · rw [key ξ, norm_mul, hψ.1.2.1, one_mul]
  · rw [← F0]
    convert hs2 using 1
    funext ξ
    exact (key ξ).symm

theorem parseval_point : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C * V.gram * C' = 1 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * C' = 0 → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj D C' * V.gram * B = 0 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ f₁ f₂, IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ → ∀ (x : WO V' W) (u : Mx D W.rank r), Summable (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => ‖GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' (ξ.map (incA D) + u)) f₁) x * starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' (ξ.map (incA D) + u)) f₂) x)‖) ∧ HasSum (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' (ξ.map (incA D) + u)) f₁) x * starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (heisO ψ V W (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' (ξ.map (incA D) + u)) f₂) x)) (∫ y in 𝓨, f₁ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u) * starRingEnd ℂ (f₂ (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C y + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.midPart V V' W B x + GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.isoPart V W C' u)) ∂μ) := by
  intro D V V' W r C B hs C' h1 h2 h3 ψ hψ μ 𝓨 hcov f₁ f₂ hf₁ hf₂ x u
  have hU₂ := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₂ (isoPart V W C' u)
  obtain ⟨K, hK⟩ := GlobalTheory.WeilVacMove.exists_bound hψ hU₂
  have hμ1 : μ 𝓨 = 1 := hcov.2.2
  have : IsFiniteMeasure (μ.restrict 𝓨) := ⟨by rw [Measure.restrict_apply_univ, hμ1]; exact ENNReal.one_lt_top⟩
  have : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  have : Countable (Matrix (Fin W.rank) (Fin r) D.host.E) := inferInstanceAs (Countable (Fin W.rank → Fin r → D.host.E))
  have hc₂ : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E,
      ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f₂) x‖ ≤
        K * (μ.restrict 𝓨).real Set.univ := by
    intro ξ
    rw [coef_eq hs h1 h2 h3 ψ μ 𝓨 hf₂ x u ξ]
    refine MeasureTheory.norm_integral_le_of_norm_le_const (MeasureTheory.ae_of_all _ fun y => ?_)
    rw [norm_mul, hψ.1.2.1, one_mul]
    exact hK _
  have hsum₁ := (expand hs h1 h2 h3 hψ hcov hf₁ x u 0).1
  have hcont₂ : Continuous fun y => heisO ψ V W (isoPart V W C' u) f₂ (isoPart V W C y + midPart V V' W B x) :=
    hU₂.3.comp ((GlobalTheory.TowerRestrict.continuous_isoPart C).add continuous_const)
  have hmain : HasSum (fun ξ : Matrix (Fin W.rank) (Fin r) D.host.E => ∫ y in 𝓨,
      res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f₁) x *
        starRingEnd ℂ (ψ (symplO V W (isoPart V W C y) (isoPart V W C' (ξ.map (incA D)))) *
          heisO ψ V W (isoPart V W C' u) f₂ (isoPart V W C y + midPart V V' W B x)) ∂μ)
      (∫ y in 𝓨, heisO ψ V W (isoPart V W C' u) f₁ (isoPart V W C y + midPart V V' W B x) *
        starRingEnd ℂ (heisO ψ V W (isoPart V W C' u) f₂ (isoPart V W C y + midPart V V' W B x)) ∂μ) := by
    refine MeasureTheory.hasSum_integral_of_dominated_convergence
      (fun ξ _ => ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f₁) x‖ * K)
      (fun ξ => ?_) (fun ξ => MeasureTheory.ae_of_all _ fun y => ?_) (MeasureTheory.ae_of_all _ fun y => hsum₁.mul_right K)
      (MeasureTheory.integrable_const _) (MeasureTheory.ae_of_all _ fun y => ?_)
    · have hI := GlobalTheory.TowerRestrict.integrable_res (C := C) (B := B) hψ hcov
        (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₂ (isoPart V W C' (ξ.map (incA D) + u))) x
      have hm : MeasureTheory.AEStronglyMeasurable (fun y => ψ (symplO V W (isoPart V W C y) (isoPart V W C' (ξ.map (incA D)))) *
          heisO ψ V W (isoPart V W C' u) f₂ (isoPart V W C y + midPart V V' W B x)) (μ.restrict 𝓨) :=
        hI.aestronglyMeasurable.congr (MeasureTheory.ae_of_all _ fun y => heisO_isoPart_incA_add_apply_eq_psi_mul hs h1 h2 h3 ψ hf₂ x u ξ y)
      exact (Complex.continuous_conj.comp_aestronglyMeasurable hm).const_mul _
    · rw [norm_mul, RCLike.norm_conj, norm_mul, hψ.1.2.1, one_mul]
      exact mul_le_mul_of_nonneg_left (hK _) (norm_nonneg _)
    · have hE := ((expand hs h1 h2 h3 hψ hcov hf₁ x u y).2).mul_right
        (starRingEnd ℂ (heisO ψ V W (isoPart V W C' u) f₂ (isoPart V W C y + midPart V V' W B x)))
      convert hE using 1
      all_goals try rfl
      funext ξ
      rw [map_mul, GlobalTheory.OrientedHeis.symplO_skew (isoPart V W C' (ξ.map (incA D))) (isoPart V W C y), conj_psi hψ, neg_neg]
      ring
  have hterm : ∀ ξ : Matrix (Fin W.rank) (Fin r) D.host.E, (∫ y in 𝓨,
      res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f₁) x *
        starRingEnd ℂ (ψ (symplO V W (isoPart V W C y) (isoPart V W C' (ξ.map (incA D)))) *
          heisO ψ V W (isoPart V W C' u) f₂ (isoPart V W C y + midPart V V' W B x)) ∂μ) =
      res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f₁) x *
        starRingEnd ℂ (res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (ξ.map (incA D) + u)) f₂) x) := by
    intro ξ
    rw [MeasureTheory.integral_const_mul, integral_conj, ← coef_eq hs h1 h2 h3 ψ μ 𝓨 hf₂ x u ξ]
  refine ⟨Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => ?_)
    (hsum₁.mul_right (K * (μ.restrict 𝓨).real Set.univ)), ?_⟩
  · rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_left (hc₂ ξ) (norm_nonneg _)
  · convert hmain using 1
    · funext ξ
      exact (hterm ξ).symm
    · refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ fun y => ?_)
      dsimp only
      rw [heisO_apply, heisO_apply]
      exact (mul_mul_conj_mul_eq_of_mul_conj_eq_one _ _ _ (psi_mul_conj hψ _)).symm

end GlobalTheory.MixParsevalPoint

end
