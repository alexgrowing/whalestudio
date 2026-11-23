import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PermOfWeilDeligneSpecialDecompositionEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.perm_of_weilDeligne_special_decomposition_eq : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (l l' : List (WD h × ℕ)), (∀ p ∈ l, IsIrrWD p.1) → (∀ p ∈ l', IsIrrWD p.1) → sumList (l.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp h (p.2 + 1)))) = sumList (l'.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp h (p.2 + 1)))) → l.Perm l' := by
  first | exact @GlobalTheory.WeilDeligne.SpUnique.perm_of_sumList_lpChar_lpSp_eq | exact GlobalTheory.WeilDeligne.SpUnique.perm_of_sumList_lpChar_lpSp_eq | (intros; apply GlobalTheory.WeilDeligne.SpUnique.perm_of_sumList_lpChar_lpSp_eq <;> assumption)
