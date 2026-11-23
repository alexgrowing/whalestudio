import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.WeilVacMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

theorem actO_two_nsmul (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g h (2 • x) = 2 • actO S T g h x := by
  rw [two_nsmul, two_nsmul, actO_add]

theorem actO_inv_actO (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
  unfold actO
  rw [inv_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul,
    Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.mul_one]

theorem isHalf_actO (e : AE D) (g : GA D S) (h : GA D T) {x : WO S T} (hx : IsHalf e x) :
    IsHalf e (actO S T g h x) := by
  have e1 : e • x = x := Matrix.ext hx
  have e2 : e • actO S T g h x = actO S T g h x := by
    unfold actO
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, e1]
  exact fun i j => congrFun (congrFun e2 i) j

theorem sqNormIntegralFundamentalDomain_eq_l2Norm_sq (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) {f : WO S T → ℂ} (hf : Continuous f) :
    nrm2 μ 𝓕 f = (∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ).toReal := by
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  unfold nrm2
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => sq_nonneg _)
    (hf.norm.pow 2).measurable.aestronglyMeasurable]
  congr 1
  refine lintegral_congr fun w => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem isVacO_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS sS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT sT' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS LS' : Set (Fin S.rank → D.host.E)) (LT LT' : Set (Fin T.rank → D.host.E)) (g : GA D S) (h : GA D T), (∀ τ, sS' τ * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS τ) → (∀ τ, sT' τ * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT τ) → (∀ u : WO S T, u ∈ (latO S T LS' LT' fun _ => True) ↔ ∃ u₀ ∈ (latO S T LS LT fun _ => True), u = actO S T g h u₀) → ∀ f, IsVacO ψ θ S T sS sT LS LT f → IsVacO ψ θ S T sS' sT' LS' LT' (om (g, h) f) := by
  intro D ψ θ S T χS χT om hW hθ sS sS' sT sT' LS LS' LT LT' g h hS hT hΛ f hf
  obtain ⟨hψ, -, hth, hlat, hfock, hnorm⟩ := hf
  refine ⟨hψ, hθ, hW.om_pres _ _ hth, ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩, fun τ z => ?_, hnorm.1, fun p hp => ?_⟩
  · obtain ⟨u₀, hu₀, rfl⟩ := (hΛ u).1 hu
    rw [← actO_two_nsmul, ← hW.om_heis g h _ f hth, hlat.1 u₀ hu₀]
  · obtain ⟨u₀, hu₀, rfl⟩ := (hΛ u).1 hu
    have h0 : IsHalf e u₀ := by
      have := isHalf_actO e g⁻¹ h⁻¹ hh
      rwa [actO_inv_actO] at this
    rw [← hW.om_heis g h _ f hth, hlat.2 e he u₀ hu₀ h0]
  · obtain ⟨z₀, rfl⟩ : ∃ z₀ : Matrix (Fin T.rank) (Fin S.rank) ℂ, z = compAt θ τ (mt T h) * z₀ * compAt θ τ (mt S g⁻¹) := by
      refine ⟨compAt θ τ (mt T h⁻¹) * z * compAt θ τ (mt S g), ?_⟩
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, compAt_mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
        compAt_mt_mul_inv, Matrix.mul_one]
    have h0 := congrArg (om (g, h)) (hfock τ z₀)
    unfold annih at h0 ⊢
    rw [map_add, map_smul, map_zero, om_dRho hW hθ g h τ _ hth, om_dRho hW hθ g h τ _ hth] at h0
    rw [cplxO_move θ τ g h (hS τ) (hT τ)]
    exact h0
  · show nrm2 p.1 p.2 (om (g, h) f) = 1
    rw [sqNormIntegralFundamentalDomain_eq_l2Norm_sq _ _ (hW.om_pres _ _ hth).cont, hW.om_unit p.1 p.2 hp.1 hp.2.1 _ f hth, ← sqNormIntegralFundamentalDomain_eq_l2Norm_sq _ _ hth.cont]
    exact hnorm.2 p hp

end GlobalTheory.WeilVacMove

end
