import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymmetricLiftOrderSymmetryMultiplicativity
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricLift_order_symmetry_multiplicativity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S), Function.Surjective (t.G ⊗ t.G).hom.appTop.hom → ∀ (wP : PrimTyG t), wP.IsGen → ∀ (k : ℕ) (a : baseOver S ⟶ t.G) (U : ThetaGrp t.G t.PP.L (k : ℤ) (baseOver S)), SymLift t.G t.PP.L (k : ℤ) k a U → ∀ (T : Over S) (σ : T ⟶ baseOver S) (z : T.left) (J : (T.left ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → LiftLaws (cubV t.cub z J) (fun p : T ⟶ t.G => val wP p.left z J) (fun p : T ⟶ t.G => GlobalTheory.CommPairing.tval U (lift σ p).left z J) (fun p : T ⟶ t.G => p ≫ t.act.act H.w0) (σ ≫ a) k := by
  first | exact @GlobalTheory.TransUnit.liftLaws_of_symLift | exact GlobalTheory.TransUnit.liftLaws_of_symLift | (intros; apply GlobalTheory.TransUnit.liftLaws_of_symLift <;> assumption)
