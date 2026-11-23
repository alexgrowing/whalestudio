import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointMorphismFactorization
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_morphism_factorization : ∀ (Z : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral Z] (K : Type) [Field K] [Algebra Z.functionField K] [FiniteDimensional Z.functionField K] (g : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ Z) [AlgebraicGeometry.QuasiCompact g] [AlgebraicGeometry.QuasiSeparated g], g = AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap Z.functionField K)) ≫ Z.fromSpecStalk (genericPoint Z) → ∃ (hη : g.fromNormalization (genericPoint g.normalization) ⤳ genericPoint Z) (ψ : K →+* g.normalization.functionField), ψ.comp (algebraMap Z.functionField K) = GlobalTheory.TrueGeo.SmallSec.fnMap g.fromNormalization hη := by
  first | exact @GlobalTheory.NormFnField.normalization_functionField | exact GlobalTheory.NormFnField.normalization_functionField | (intros; apply GlobalTheory.NormFnField.normalization_functionField <;> assumption)
