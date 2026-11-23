import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

theorem Afun_isSPsiEquiv : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, IsSPsiEquiv z (psiGen k r z c) π (Afun (psiGen k r z c) π μS σ u v ξ) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu v hv ξ
  intro h hh m hm g hg
  have hRep : IsURepOn (GG k r) σ := hStd.2.1
  have hDec : Decay σ (DD σ w) a := hStd.2.2.2.2.2.2.2.1
  have hz : inWb k r z := hSide.1
  have hT : 0 < Tz k r z := hSide.2.1
  have hπ : IsURepOn (UWset k r z) π := hSide.2.2.1
  have hCl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hz hT
  have hSsub : Sset k r z ⊆ GG k r := hCl.2.2.2.1.1
  have hhm : h * m ∈ Sset k r z := ⟨h, hh, m, hm, rfl⟩
  have hstab := (GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hRep).1
  have hgu : σ g u ∈ DD σ w := hstab g hg u hu
  have hmul : σ (h * m * g) = (σ (h * m)).comp (σ g) := hRep.1.2 _ (hSsub hhm) _ hg
  have hD1 := (GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w : Set H)
    (fun g hg v hv => hstab g hg v hv) hDec (σ g u) hgu v hv).2.1 (h * m) hhm
  have hPi := ((GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hz hT hπ).1 h hh m hm).2
  unfold Afun
  rw [hmul, ContinuousLinearMap.comp_apply, hD1.1, hPi]
  rfl

end GlobalTheory.SgInf
