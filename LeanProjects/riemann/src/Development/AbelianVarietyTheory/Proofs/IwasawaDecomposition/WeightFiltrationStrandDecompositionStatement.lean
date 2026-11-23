import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightFiltrationStrandDecomposition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictHomApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_filtration_strand_decomposition : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) (m : ℕ), (∀ (k : ℤ) (σ : Weil h), ∀ v ∈ wtSpace a k, a.ρ σ v ∈ wtSpace a k) → (∀ (k : ℤ), ∀ v ∈ wtSpace a k, a.N v ∈ wtSpace a (k + 2)) → (∀ k : ℤ, (m : ℤ) < k → wtSpace a k = ⊥) → IsSubWD a (strand a.N (wtSpace a (-(m : ℤ))) m) ∧ IsSubWD a (lowPart (wtSpace a) a.N m) := by
  first | exact @GlobalTheory.WeilDeligne.PrimDecomp.SubStab.strand_and_lowPart_stable | exact GlobalTheory.WeilDeligne.PrimDecomp.SubStab.strand_and_lowPart_stable | (intros; apply GlobalTheory.WeilDeligne.PrimDecomp.SubStab.strand_and_lowPart_stable <;> assumption)
