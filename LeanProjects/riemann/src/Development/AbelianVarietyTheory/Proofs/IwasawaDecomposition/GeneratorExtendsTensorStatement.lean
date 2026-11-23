import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorExtendsTensor
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtAt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_extends_tensor : ∀ (X : Scheme.{0}) (A B : LB X) (R : Type) [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ X)
    (eA : LB.Gen (A.pull x)) (eB : LB.Gen (B.pull x)), eA.IsGen → eB.IsGen →
    GlobalTheory.TraitGen.ExtAt A x eA → GlobalTheory.TraitGen.ExtAt B x eB →
    ∃ e : LB.Gen ((GlobalTheory.CechPic.tens A B).pull x), e.IsGen ∧ GlobalTheory.TraitGen.ExtAt (GlobalTheory.CechPic.tens A B) x e := by
  first | exact @GlobalTheory.TraitGen.exists_tens_extAt | exact GlobalTheory.TraitGen.exists_tens_extAt | (intros; apply GlobalTheory.TraitGen.exists_tens_extAt <;> assumption)
