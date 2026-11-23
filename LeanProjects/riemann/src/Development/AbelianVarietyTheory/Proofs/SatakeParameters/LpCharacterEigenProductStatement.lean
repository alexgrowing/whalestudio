import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharacterEigenProduct
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lp_character_eigen_product : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h) (l : ℕ) (σ : Weil h), ((x.lpChar (WD.lpSp h l)).eig σ).prod = ((x.eig σ).prod) ^ l := by
  first | exact @GlobalTheory.WeilDeligne.prod_eig_lpChar_lpSp | exact GlobalTheory.WeilDeligne.prod_eig_lpChar_lpSp | (intros; apply GlobalTheory.WeilDeligne.prod_eig_lpChar_lpSp <;> assumption)
