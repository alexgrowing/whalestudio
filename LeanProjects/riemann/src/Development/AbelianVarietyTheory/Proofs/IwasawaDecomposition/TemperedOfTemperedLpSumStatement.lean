import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TemperedOfTemperedLpSum
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictHomApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tempered_of_tempered_lpSum' : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x y : WD h), (x.lpSum y).tempered → y.tempered := by
  first | exact @GlobalTheory.WeilDeligne.TemperedSummand.tempered_of_tempered_lpSum | exact GlobalTheory.WeilDeligne.TemperedSummand.tempered_of_tempered_lpSum | (intros; apply GlobalTheory.WeilDeligne.TemperedSummand.tempered_of_tempered_lpSum <;> assumption)
