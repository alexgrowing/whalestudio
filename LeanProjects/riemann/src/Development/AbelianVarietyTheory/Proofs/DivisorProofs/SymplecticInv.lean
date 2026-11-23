import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapMoebiusDenomUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodVectorMoebiusTransformStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainSymplecticPreimageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSymplecticPreimageEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiberConjugationStripInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodDatumCurvatureIntegralChangeStatement

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory Set
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

namespace GlobalTheory.TorsionForm

theorem symplecticInv : SymplecticInv := by
  unfold SymplecticInv
  intro E _ _ _ g n B τ M γ j h hτ hD β b hb T hT
  obtain ⟨F, hH, hM⟩ := hT
  obtain ⟨D₁, hD₁, hK⟩ := hH
  have hu : IsUnit (den γ (τ b)) := GlobalTheory.T.period_map_moebius_denom_unit B τ γ hD.1 b hb
  refine ⟨F, ⟨_, GlobalTheory.T.fundamental_domain_symplectic_preimage M γ D₁ hD₁, fun u hu' => ?_⟩, hM⟩
  obtain ⟨K, hKK, hF⟩ := hK u hu'
  refine ⟨kerConj n (den γ (τ b)) K, GlobalTheory.T.period_datum_curvature_integral_change B τ M γ j h β b u D₁ K hτ hD hb hKK, ?_⟩
  rw [hF]
  refine congrArg phi ?_
  rw [← GlobalTheory.T.integral_symplectic_preimage_eq γ D₁]
  refine congrArg (fun f : Fl g → Ext (n + n) => ∫ x in (fun x : Fl g => x ᵥ* (γ⁻¹).mat) ⁻¹' D₁, f x)
    (funext fun x => ?_)
  have hc : (den γ (τ b))ᴴ * ((den γ (τ b))⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hu),
      Matrix.conjTranspose_one]
  show _ = strN (m := n + n) (kerConj n (den γ (τ b)) K 1 (per (τ b) x) (per (τ b) x))
  rw [kerConj, GlobalTheory.T.period_vector_moebius_transform γ (τ b) x hu]
  exact (GlobalTheory.T.fiber_conjugation_strip_invariant _ _ hc _).symm

end GlobalTheory.TorsionForm
