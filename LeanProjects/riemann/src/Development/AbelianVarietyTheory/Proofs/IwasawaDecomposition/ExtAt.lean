import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericSectionExtendsNormalStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitGen

def ExtAt {X : Scheme.{0}} (L : LB X) {R : Type} [CommRing R] [IsDomain R] (x : Sp (FractionRing R) ⟶ X)
    (e : LB.Gen (L.pull x)) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V →
    ∀ (ψ : R →+* V) (gam : FractionRing R →+* FractionRing V),
    (∀ r, gam (algebraMap R _ r) = algebraMap V _ (ψ r)) →
    ∀ χ : Sp V ⟶ X, spMap gam ≫ x = Out.jK V ≫ χ → ∃ e' : LB.Gen (L.pull χ), e'.IsGen ∧
      ∀ z J, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Good L z J →
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (L := L) (φ := fun _ : PUnit => x) (ε := fun _ => 1) e (spMap gam) z J =
        ReciprocityTheory.ChartRestriction.G.Geo.Tor.val (L := L) (φ := fun _ : PUnit => χ) (ε := fun _ => 1) e' (Out.jK V) z J

end GlobalTheory.TraitGen
