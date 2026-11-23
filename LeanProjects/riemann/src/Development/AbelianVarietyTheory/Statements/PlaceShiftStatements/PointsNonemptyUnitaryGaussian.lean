import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PrimeToPOne

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LKCx

variable {p : ℕ} [Fact p.Prime]

def KpOne (G : HTGroup p) : Subgroup (Gr G 1) := (Kp0 G).map (inclG G 1)

def Form.toAf {G : HTGroup p} (P : Form G) : grp G P.β →* G.GAf :=
  toAfF G P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec

abbrev Form.Pts {G : HTGroup p} (v : InfinitePlace G.F) (P : Form G) (Kf : Subgroup G.GAf)
    (K' : Subgroup (Gr G 1)) : Type :=
  GlobalTheory.LKCx.Pts G v P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec Kf K'

abbrev Form.Stab {G : HTGroup p} (v : InfinitePlace G.F) (P : Form G) (Kf : Subgroup G.GAf)
    (K' : Subgroup (Gr G 1)) (a : Dat G v P.β) : Type :=
  GlobalTheory.LKCx.Stab G v P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec Kf K' a

abbrev AllPts (G : HTGroup p) (v : InfinitePlace G.F) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) : Type :=
  Σ q : FCls G, Form.Pts v (Quot.out q) Kf K'

def CxPtsM {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} (M : Model b N) (σ : R →+* ℂ) : Type :=
  {y : Sp ℂ ⟶ M.X // y ≫ M.s = spMap σ}

def QIsog {D : Datum p} {G : HTGroup p} (L : Link D G) {R : Type} [CommRing R] {b : Base D R} {k : Type} [Field k]
    {β : R →+* k} {N : ℕ} (o : Obj b N (spMap β)) : Type :=
  {π : End0 (av o) // PrimeToP o π ∧ ∃ g, IsGamma L o π g}

def FixP {G : HTGroup p} (v : InfinitePlace G.F) (P : Form G) (K' : Subgroup (Gr G 1)) (a : Dat G v P.β) : Type :=
  {y : grp G P.β // FixL G v P.β y a.2.1 ∧ a.1.2⁻¹ * toP1 G P.β y * a.1.2 ∈ K'}

def CxUnif : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.IsSimple →
    ∀ (R : Type) [CommRing R] (b : Base D R) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ),
    b.Matches σ → b.IsType σ ρ → ∀ N : ℕ, 3 ≤ N → N.Coprime p → ∀ (M : Model b N) (v : InfinitePlace G.F),
    sigPosH (G.gram_herm v) = 1 →
    ∃ Φ : CxPtsM M σ ≃ AllPts G v (L.KN N) (KpOne G),
      ∀ (y : CxPtsM M σ) (o : Obj b N (spMap σ)), Classifies M y.1 o →
        ∀ (q : FCls G) (a : Dat G v (Quot.out q).β),
          Φ y = (⟨q, Quot.mk _ a⟩ : AllPts G v (L.KN N) (KpOne G)) →
          ∃ E : QIsog L o ≃ FixP v (Quot.out q) (KpOne G) a,
            (∀ π : QIsog L o, IsGamma L o π.1 (a.1.1⁻¹ * (Quot.out q).toAf (E π).1 * a.1.1)) ∧
            Nat.card {π : QIsog L o // ∃ k ∈ L.KN N, IsGamma L o π.1 k} =
              Nat.card (Form.Stab v (Quot.out q) (L.KN N) (KpOne G) a)

def FixP.one {G : HTGroup p} (v : InfinitePlace G.F) (P : Form G) (K' : Subgroup (Gr G 1)) (a : Dat G v P.β) :
    FixP v P K' a :=
  ⟨1, fixL_one G v P.β _, by simpa using K'.one_mem⟩

example {G : HTGroup p} (P : Form G) (h : G.GAf) : h⁻¹ * P.toAf 1 * h = 1 := by simp

example {G : HTGroup p} (v : InfinitePlace G.F) (P : Form G) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1))
    (a : Dat G v P.β) : Nonempty (Form.Stab v P Kf K' a) :=
  ⟨Stab.one G v P.β _ _ _ Kf K' a⟩

end GlobalTheory.LKCx
