import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionDescentFiniteEtaleCover
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_descent_finite_etale_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (W : (Sp R).Opens) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (k : ℕ), IsSeparated G.hom → TorsFiniteFlat G W k → ∀ N : Over W.toScheme, FinFlatEt N → Surjective N.hom → ∀ (u : genPart (overW W N) ⟶ G) (d : overW W (N ⊗ N) ⟶ G), u ^ k = 1 → d ^ k = 1 → (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (a b : TF (R := R) F ⟶ genPart (overW W N)) (c : TF (R := R) F ⟶ overW W (N ⊗ N)), c ≫ (Over.map W.ι).map (fst N N) = a ≫ genι _ → c ≫ (Over.map W.ι).map (snd N N) = b ≫ genι _ → a ≫ u = (b ≫ u) * (c ≫ d)) → ∃ v : overW W N ⟶ G, v ^ k = 1 ∧ genι _ ≫ v = u := by
  first | exact @GlobalTheory.FlatTors.exists_tors_ext | exact GlobalTheory.FlatTors.exists_tors_ext | (intros; apply GlobalTheory.FlatTors.exists_tors_ext <;> assumption)
