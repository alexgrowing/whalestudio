import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitaris
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DefiniteBC GlobalTheory.BcSpeh
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteAutomorphicRepGL_localComponent_isUnitarisable : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : LocIrr w N), IsLocCompGL V w σ → IsUnitarisable σ.ρ := by
  first | exact @GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL | exact GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL | (intros; apply GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL <;> assumption)
