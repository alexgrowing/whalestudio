import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWNStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
import Formalism.FormalDegreeBessel.FinalG
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.SInt

theorem sint_eq_inner_be : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ v ∈ DD σ w, ∀ ξ : Wp, ∫ t, ⟪v, σ (Matrix.of t)⁻¹ v⟫_ℂ * ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ ∂μS = ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide v hv ξ
  have hURep : IsURepOn (GG k r) σ := hStd.2.1
  have hDecay : Decay σ (DD σ w : Set H) a := hStd.2.2.2.2.2.2.2.1
  obtain ⟨hz, hT, hπ, hHaar, -⟩ := id hSide
  have hstab : ∀ g ∈ GG k r, ∀ u ∈ (DD σ w : Set H), σ g u ∈ (DD σ w : Set H) :=
    (GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hURep).1
  have hint := (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w) hstab hDecay v hv v hv).1
  let f : Mt k r → (Wp →L[ℂ] Wp) := fun s =>
    coef σ v v (Matrix.of s) • PiS (psiGen k r z c) π (Matrix.of s)⁻¹
  let L : (Wp →L[ℂ] Wp) →L[ℂ] ℂ := (innerSL ℂ ξ).comp (ContinuousLinearMap.apply ℂ Wp ξ)
  have hL : ∀ A, L A = ⟪ξ, A ξ⟫_ℂ := fun A => rfl
  have hRHS : ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ = ∫ s, L (f s) ∂μS := by
    rw [← hL]; exact (L.integral_comp_comm hint).symm
  have hunim : μS.map invM = μS := ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μS).1 hHaar).2
  have hmeas : AEStronglyMeasurable (fun s => L (f s)) μS :=
    L.continuous.comp_aestronglyMeasurable hint.aestronglyMeasurable
  have hsub : ∀ᵐ t ∂μS, Matrix.of t ∈ Sset k r z := ae_iff.2 hHaar.2.2.1
  have hchange : ∫ s, L (f s) ∂μS = ∫ t, L (f (invM t)) ∂μS := by
    conv_lhs => rw [← hunim]
    exact integral_map measurable_invM.aemeasurable (by rw [hunim]; exact hmeas)
  rw [hRHS, hchange]
  refine integral_congr_ae ?_
  filter_upwards [hsub] with t ht
  have hGG : Matrix.of t ∈ GG k r := (GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT).2.2.2.1.1 ht
  have hu : IsUnit (Matrix.of t : Mat k r).det :=
    ((uHGroup _ (Hpk k r) (Matrix.isUnit_det_of_left_inverse (hpkFacts k r).2.1)).2.2 _ hGG).1
  have hadj := ((GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hz hT hπ).2.2.1 _ ht).2
  simp only [hL, f, coef, of_invM, Matrix.nonsing_inv_nonsing_inv _ hu,
    ContinuousLinearMap.smul_apply, inner_smul_right]
  rw [← hadj, ContinuousLinearMap.adjoint_inner_left]

end GlobalTheory.SgInf.SInt
