import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualUnramifiedPlaces
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SiegelMeanCc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsSelfDualLatticeIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalDensityOfSelfDualLatticeLemmas
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualLatticesUnramifiedPlaceNoHypothesis

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.LatticeContDensity

theorem contDensity_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ), 1 ≤ M → ∀ (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.UnramifiedPlace F E v → ∀ ψ : AddChar (Fv F v) ℂ, GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsLocalChar v ψ → ∀ n : ℤ, GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.DualExponent v ψ n → ∀ L : Submodule (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.maxOrder F E v) (Fin M → Fv F v ⊗[F] E), GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.IsSelfDualLattice σ J v L → ∀ (μ : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)) (ν : Measure (Fv F v)), SdW F E σ M J (Fv F v) ψ 1 μ → SdR (Fv F v) ψ ν → ∀ g : Fv F v → ℂ, IsContDensityOn μ (fun X => qR (Fv F v) σ J (X 0)) id ν {c | c ≠ 0} ({X | X 0 ∈ L}.indicator 1) g → ∀ β : Fv F v, Valued.v β = 1 → g β = (((GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ n) ^ ((1 / 2 : ℝ) - (M : ℝ)) * (1 - GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.eta F E v ^ M * (GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.resCard F v ^ M)⁻¹) : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ σ hσ M hM J hJ v hv ψ hψ n hn L hL μ ν hμ hν g hg β hβ

  have H : GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.SelfDualLatticeDensity :=
    GlobalTheory.LocalDensityCompare.localDensity_iff.1
      (GlobalTheory.LatticeDensity.localDensity_of_selfDualLatticeLemmas
        GlobalTheory.UnramSelfDualClosed.selfDualLatticeLemmas)
  obtain ⟨η, hη⟩ := GlobalTheory.LocalDensityCompare.exists_eta F E v
  have hEta : GlobalTheory.IndefiniteRowSideFullHecke.PlaceSplittingTypes.IsEtaAt F E v η :=
    (GlobalTheory.LocalDensityCompare.isEtaAt_iff F E v hσ.2.2.1 η).2 ⟨hv, hη⟩
  have key := (H F E σ hσ M J hM hJ v η hEta ψ hψ).2 n hn L
    ((GlobalTheory.LocalDensityCompare.isSelfDualLattice_iff v σ J L).1 hL) μ hμ ν hν

  have hβ' : Valued.v (β - β) < 1 := by simp
  have hgβ := (key.2.2 β hβ).2 g hg β hβ'
  rw [hgβ, ← GlobalTheory.LocalDensityCompare.dens_eq v n M η hη]

end GlobalTheory.LatticeContDensity
