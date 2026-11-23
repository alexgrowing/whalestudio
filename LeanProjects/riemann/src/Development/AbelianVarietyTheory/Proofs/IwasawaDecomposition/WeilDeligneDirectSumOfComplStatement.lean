import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneDirectSumOfCompl
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RestrictHomApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.WeilDeligne.PrimDecomp GlobalTheory.LocLanglands
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_deligne_direct_sum_of_compl : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) (S T : Submodule ℂ V) (hS : IsSubWD a S) (hT : IsSubWD a T), IsCompl S T → WD.mk a = (WD.mk (restrict a S hS)).lpSum (WD.mk (restrict a T hT)) := by
  first | exact @GlobalTheory.WeilDeligne.PrimDecomp.sumiso | exact GlobalTheory.WeilDeligne.PrimDecomp.sumiso | (intros; apply GlobalTheory.WeilDeligne.PrimDecomp.sumiso <;> assumption)
