import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorExtendsPower
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtAt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_extends_power : ∀ (X : Scheme.{0}) (L : LB X) (R : Type) [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ X)
    (e : LB.Gen (L.pull x)) (m : ℕ), e.IsGen → GlobalTheory.TraitGen.ExtAt L x e →
    ∃ e' : LB.Gen ((lbPow L m).pull x), e'.IsGen ∧ GlobalTheory.TraitGen.ExtAt (lbPow L m) x e' := by
  first | exact @GlobalTheory.TraitGen.extAt_lbPow | exact GlobalTheory.TraitGen.extAt_lbPow | (intros; apply GlobalTheory.TraitGen.extAt_lbPow <;> assumption)
