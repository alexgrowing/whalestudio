import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeIdealEuclideanLatticeIsZLattice
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbAApply
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeIdealEuclideanLattice_isZLattice : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ M : Ideal (𝓞 K), M ≠ ⊥ → ∃ _ : DiscreteTopology (GlobalTheory.HeckePoisson.lat φ M), IsZLattice ℝ (GlobalTheory.HeckePoisson.lat φ M) := by
  first | exact @GlobalTheory.HeckePoisson.lat_isZLattice | exact GlobalTheory.HeckePoisson.lat_isZLattice | (intros; apply GlobalTheory.HeckePoisson.lat_isZLattice <;> assumption)
