import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsGHeckeMapForget
import Development.AbelianVarietyTheory.Definitions.Divisors.HxiTZeroComb
import Development.AbelianVarietyTheory.Definitions.Divisors.CompactBIffCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne

noncomputable section

namespace GlobalTheory.WeightTwoHeckePower

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G R} {N M : ℕ}

abbrev sPow (X : GenModel gb N) (r : ℕ) : (GlobalTheory.KS.pow X.univ.A r).left ⟶ Sp R :=
  (GlobalTheory.KS.pow X.univ.A r).hom ≫ X.s

theorem liftMap_w {X : GenModel gb N} {X' : GenModel gb M} {f : X'.X ⟶ X.X} {o : GObj gb N X'.s}
    (ψ : X'.univ.A ⟶ o.A) (m : GObjMap o X.univ f) :
    (ψ.left ≫ m.φ) ≫ X.univ.A.hom = X'.univ.A.hom ≫ f := by
  rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w]

def liftPow {X : GenModel gb N} {X' : GenModel gb M} {f : X'.X ⟶ X.X} {o : GObj gb N X'.s}
    (ψ : X'.univ.A ⟶ o.A) (m : GObjMap o X.univ f) (r : ℕ) :
    (GlobalTheory.KS.pow X'.univ.A r).left ⟶ (GlobalTheory.KS.pow X.univ.A r).left :=
  GlobalTheory.KS.powMap f (ψ.left ≫ m.φ) (liftMap_w ψ m) r

def actPow {S : Scheme.{0}} (A : Over S) [GrpObj A] (act : OActN G.O A) (α : G.O) (r : ℕ) :
    (GlobalTheory.KS.pow A r).left ⟶ (GlobalTheory.KS.pow A r).left :=
  (Limits.Pi.map fun _ : Fin r => act.act α).left

def heckePow {X : GenModel gb N} {X' : GenModel gb M} {f : X'.X ⟶ X.X} {o : GObj gb N X'.s}
    (ψ : X'.univ.A ⟶ o.A) (m : GObjMap o X.univ f) (α : G.O) (r : ℕ) :
    (GlobalTheory.KS.pow X'.univ.A r).left ⟶ (GlobalTheory.KS.pow X.univ.A r).left :=
  liftPow ψ m r ≫ actPow X.univ.A X.univ.act α r

end GlobalTheory.WeightTwoHeckePower
