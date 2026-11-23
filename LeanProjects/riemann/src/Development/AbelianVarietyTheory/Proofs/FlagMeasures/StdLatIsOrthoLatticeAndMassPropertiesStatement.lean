import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StdLatIsOrthoLatticeAndMassProperties
import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdLat_isOrthoLattice_and_mass_properties : ∀ (K : Type) [Field K] [NumberField K] [StarRing K], IsCMUnram K → ∀ j : ℕ, (Cnt.stdH K j).IsSymm ∧ IsOrthoLattice (Cnt.stdH K j) (Cnt.stdLat K j) j ∧ 0 < Cnt.massU K j ∧ Cnt.massU K 0 = 1 ∧ ∀ (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V), IsOrthoLattice h L j → mass h L = Cnt.massU K j ∧ PD h := by
  first | exact @GlobalTheory.Mass.StdMass.main | exact GlobalTheory.Mass.StdMass.main | (intros; apply GlobalTheory.Mass.StdMass.main <;> assumption)
