import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtensionPow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_extension_pow_alt : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (e : ℕ), 0 < e → (∀ x : K, v'.valuation L (algebraMap K L x) = v.valuation K x ^ e) → ∃ f : v.adicCompletion K →+* v'.adicCompletion L, Continuous f ∧ (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) ∧ ∀ y, Valued.v (f y) = Valued.v y ^ e := by
  first | exact @GlobalTheory.DenseCompl.exists_extension_pow | exact GlobalTheory.DenseCompl.exists_extension_pow | (intros; apply GlobalTheory.DenseCompl.exists_extension_pow <;> assumption)
