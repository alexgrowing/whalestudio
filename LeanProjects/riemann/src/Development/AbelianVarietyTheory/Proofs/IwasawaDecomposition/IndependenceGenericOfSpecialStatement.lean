import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndependenceGenericOfSpecial
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LN GlobalTheory.TorRef
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.independence_generic_of_special : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (L : LB G.left) (N n : ℕ)
    (b : Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk (𝟙 (Sp R))))) (K : Type) [Field K] (V : ValuationSubring K)
    (g : R →+* V), Flat G.hom → L.IsLB → IndepAlong G L N (toBase ((IsLocalRing.residue V).comp g)) b →
    IndepAlong G L N (toBase (V.subtype.comp g)) b := by
  first | exact @GlobalTheory.IndepFibre.indepAlong_generic | exact GlobalTheory.IndepFibre.indepAlong_generic | (intros; apply GlobalTheory.IndepFibre.indepAlong_generic <;> assumption)
