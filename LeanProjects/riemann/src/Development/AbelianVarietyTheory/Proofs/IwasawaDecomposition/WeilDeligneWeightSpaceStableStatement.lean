import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneWeightSpaceStable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictHomApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_deligne_weight_space_stable : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V), (∀ (k : ℤ) (σ : Weil h), ∀ v ∈ wtSpace a k, a.ρ σ v ∈ wtSpace a k) ∧ ∀ (k : ℤ), ∀ v ∈ wtSpace a k, a.N v ∈ wtSpace a (k + 2) := by
  first | exact @GlobalTheory.WeilDeligne.PrimDecomp.wtSpace_stable | exact GlobalTheory.WeilDeligne.PrimDecomp.wtSpace_stable | (intros; apply GlobalTheory.WeilDeligne.PrimDecomp.wtSpace_stable <;> assumption)
