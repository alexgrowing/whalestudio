import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem afun_inner_eq_integral : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ x : Mt k r, Matrix.of x ∈ GG k r → ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ = ∫ s, coef σ u v (Matrix.of (lmulM (Matrix.of s) x)) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of (lmulM (Matrix.of s) x)), ξ⟫_ℂ ∂μS := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ x hx
  have hσ : IsURepOn (GG k r) σ := hStd.2.1
  have hDec : Decay σ (DD σ w) a := hStd.2.2.2.2.2.2.2.1
  have hzb : inWb k r z := hSide.1
  have hTz : 0 < Tz k r z := hSide.2.1
  have hπ : IsURepOn (UWset k r z) π := hSide.2.2.1
  have hμS : IsHaarOn (Sset k r z) μS := hSide.2.2.2.1
  have hstab := (GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hσ).1
  have hSsub : Sset k r z ⊆ GG k r := (GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hzb hTz).2.2.2.1.1
  have hD1 := GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w) hstab hDec
  have hxu : σ (Matrix.of x) u ∈ DD σ w := hstab _ hx u hu
  have hxu₁ : σ (Matrix.of x) u₁ ∈ DD σ w := hstab _ hx u₁ hu₁
  obtain ⟨hint, -, -, -⟩ := hD1 _ hxu v hv
  obtain ⟨-, heq₁, -, -⟩ := hD1 _ hxu₁ v hv
  have hPi := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hzb hTz hπ
  have hae : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z := by rw [ae_iff]; exact hμS.2.2.1
  show ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x),
      be (psiGen k r z c) π μS σ (σ (Matrix.of x) u) v ξ⟫_ℂ = _
  rw [be, ContinuousLinearMap.integral_apply hint, ← integral_inner (hint.apply_continuousLinearMap ξ)]
  refine integral_congr_ae ?_
  filter_upwards [hae] with s hs
  have hsG : Matrix.of s ∈ GG k r := hSsub hs
  have hmul : σ (Matrix.of s * Matrix.of x) = (σ (Matrix.of s)).comp (σ (Matrix.of x)) :=
    hσ.1.2 _ hsG _ hx
  have hcoef : coef σ (σ (Matrix.of x) u) v (Matrix.of s) =
      coef σ u v (Matrix.of (lmulM (Matrix.of s) x)) := by
    show ⟪v, σ (Matrix.of s) (σ (Matrix.of x) u)⟫_ℂ = ⟪v, σ (Matrix.of s * Matrix.of x) u⟫_ℂ
    rw [hmul]; rfl
  have hadj := ((hPi.2.2.1) _ hs).2
  rw [ContinuousLinearMap.smul_apply, inner_smul_right, hcoef]
  congr 1
  rw [← hadj, ContinuousLinearMap.adjoint_inner_right]
  congr 1
  show PiS (psiGen k r z c) π (Matrix.of s) (be (psiGen k r z c) π μS σ (σ (Matrix.of x) u₁) v ξ) =
    be (psiGen k r z c) π μS σ (σ (Matrix.of s * Matrix.of x) u₁) v ξ
  rw [hmul, ContinuousLinearMap.comp_apply, (heq₁ _ hs).1]
  rfl

end GlobalTheory.SgInf
