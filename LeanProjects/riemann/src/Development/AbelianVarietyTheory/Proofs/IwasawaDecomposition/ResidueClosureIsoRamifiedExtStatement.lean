import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueClosureIsoRamifiedExt
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_closure_iso_ramified_ext : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (e : ℕ) (f : v.adicCompletion K →+* v'.adicCompletion L), 0 < e → (∀ y, Valued.v (f y) = Valued.v y ^ e) → letI := f.toAlgebra; FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) → ∀ b₀ : Kbar v ≃+* Kbar v', (∀ x, b₀ (algebraMap (v.adicCompletion K) (Kbar v) x) = algebraMap (v'.adicCompletion L) (Kbar v') (f x)) → ∀ y : Kbar v, IsIntegral (v.adicCompletionIntegers K) y ↔ IsIntegral (v'.adicCompletionIntegers L) (b₀ y) := by
  first | exact @GlobalTheory.LocIntegral.isIntegral_iff_isIntegral_map | exact GlobalTheory.LocIntegral.isIntegral_iff_isIntegral_map | (intros; apply GlobalTheory.LocIntegral.isIntegral_iff_isIntegral_map <;> assumption)
