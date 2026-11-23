import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_siegPre_iso_of_polAV : Out.Laws → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (o : Type) [CommRing o] (K : Type) [Field K] (em : o →+* K) (h k : ℕ) (ζ : o) (ze : Kˣ) (P : Out.PolAV (Sp K)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over (Sp K)) ⟶ P.A)), P.g = h → (k : K) ≠ 0 → (ze : K) = em ζ → IsPrimitiveRoot ze k → (∀ x y, lev (x + y) = lev x * lev y) → (∀ x, lev x ^ k = 1) → (∀ x y, Out.WeilIs P.A P.L k (lev x) (lev y) (unitOn (ze ^ omegaStd x y))) → ∃ (c : SiegPre h k ζ (spMap em)) (φ : c.A ≅ P.A), IsMonHom φ.hom ∧ c.Principal ∧ LBIso c.P ((abelian₂ P.A P.L).pull (lift (fst c.A c.A ≫ φ.hom) (snd c.A c.A ≫ φ.hom)).left) ∧ ∀ x, c.lev x ≫ φ.hom = lev x := by
  first | exact @GlobalTheory.exists_siegPre_of_polAV | exact GlobalTheory.exists_siegPre_of_polAV | (intros; apply GlobalTheory.exists_siegPre_of_polAV <;> assumption)
