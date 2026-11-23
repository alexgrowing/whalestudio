import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenTransl

variable {R : Type} [CommRing R] [IsDomain R] (G : Over (Sp R))

abbrev genOver : Over (Sp R) := Over.mk (pullback.snd G.hom (jK R) ≫ jK R)

def genPr : genOver G ⟶ G := Over.homMk (pullback.fst G.hom (jK R)) pullback.condition

def genPt (a : Over.mk (jK R) ⟶ G) : genOver G ⟶ G :=
  Over.homMk (pullback.snd G.hom (jK R) ≫ a.left) (by
    rw [Category.assoc, Over.w a]; rfl)

def IsGenTransl [GrpObj G] (L L₁ : LB G.left) (a : Over.mk (jK R) ⟶ G) : Prop :=
  LBIso (L₁.pull (pullback.fst G.hom (jK R))) (L.pull ((genPr G * genPt G a).left))

end GlobalTheory.GenTransl
