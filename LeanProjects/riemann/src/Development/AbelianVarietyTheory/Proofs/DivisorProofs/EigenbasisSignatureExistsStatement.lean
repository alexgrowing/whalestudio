import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenbasisSignatureExists
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenbasis_signature_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l) (k : Type) [Field k] [NumberField k] (j : c.F →+* k) (o : Obj D l (baseKA l) (spMap j ≫ spMap (IntermediateField.inclusion c.le).toRingHom)) (τ : E →+* ℂ), τ (H.rt : E) = H.rt0 → (∃ x : Fin D.p → (epsR k ⟶ o.t.G), EigenvectorLieDegree.IsEigBasis o.t.act ((EigenvectorLieDegree.embIn c j τ).comp (algebraMap (𝓞 E) E)) x) ∧ ∃ x : Fin D.q → (epsR k ⟶ o.t.G), EigenvectorLieDegree.IsEigBasis o.t.act ((EigenvectorLieDegree.embIn c j (conjEmb τ)).comp (algebraMap (𝓞 E) E)) x := by
  first | exact @GlobalTheory.EigBasisExist.exists_eigBases | exact GlobalTheory.EigBasisExist.exists_eigBases | (intros; apply GlobalTheory.EigBasisExist.exists_eigBases <;> assumption)
