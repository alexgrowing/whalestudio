import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.OrthoMass

theorem main : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∃ ms : ℕ → ℝ, (∀ n, 0 < ms n) ∧ ∀ (n : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (h : W →ₗ⋆[K] W →ₗ[K] K) (I : Submodule (𝓞 K) W), h.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h I n → Formalism.HermitianLatticesTheory.mass h I = ms n := by
  intro K _ _ _ hK
  refine ⟨fun n => Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm K n) (Formalism.MainNotions.StandardLattice.stdLat K n), fun n => ?_, ?_⟩
  · show 0 < Formalism.HermitianLatticesTheory.mass (Formalism.MainNotions.StandardLattice.stdForm K n) (Formalism.MainNotions.StandardLattice.stdLat K n)
    rw [Formalism.MainNotions.StandardLattice.standard_form_eq_telescope_form, Formalism.MainNotions.StandardLattice.standard_lattice_eq_telescope_lattice]
    exact Formalism.HermitianLatticesTheory.massTelescope_std_pos K hK n
  · intro n W _ _ _ _ h I _ ho
    exact Formalism.MainNotions.StandardLattice.mass_ortho K hK n W h I ho

end GlobalTheory.OrthoMass
