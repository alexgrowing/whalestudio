import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LevelChange
import Development.AbelianVarietyTheory.Definitions.Divisors.HxiTZeroComb

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical

namespace UpperTheory.Gal.W2

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {gb : GBase D.toG ℂ}

abbrev TIs {S : Scheme.{0}} {s : S ⟶ Sp ℂ} {N : ℕ} (o : GObj gb N s) {k : Type} [Field k] (t : Sp k ⟶ S) : Type :=
  GTateIso D.toG k (Over.mk t ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))

def IsTr (h : G.GAf) {S : Scheme.{0}} {s : S ⟶ Sp ℂ} {N N' : ℕ} (o' : GObj gb N' s) (o'' : GObj gb N s) (ψ : o'.A ⟶ o''.A) : Prop :=
  IsMonHom ψ ∧ (∀ c : D.O, o'.act.act c ≫ ψ = ψ ≫ o''.act.act c) ∧
    (∃ (ψ' : o''.A ⟶ o'.A) (d : ℕ), IsMonHom ψ' ∧ (∀ c : D.O, o''.act.act c ≫ ψ' = ψ' ≫ o'.act.act c) ∧
      ψ ≫ ψ' = (𝟙 o'.A) ^ d ∧ ψ' ≫ ψ = (𝟙 o''.A) ^ d ∧ d.Coprime p) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S) (β : ℂ →+* k), t ≫ s = spMap β →
      ∃ (I' : TIs o' t) (I'' : TIs o'' t), (∀ y, toUnit _ ≫ o'.eta y = I'.ev N' y) ∧ (∀ y, toUnit _ ≫ o''.eta y = I''.ev N y) ∧
        ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x y : D.La,
          I'.ev n x ≫ ψ = I''.ev n y ↔ ∃ v ∈ LaHat D, L.actG h (inAf D x) = inAf D y + n • v

structure Leg (h : G.GAf) {N N' : ℕ} (X' : GenModel gb N') (X : GenModel gb N) where
  q : X'.X ⟶ X.X
  o : GObj gb N X'.s
  ψ : X'.univ.A ⟶ o.A
  φ : GObjMap o X.univ q
  ov : q ≫ X.s = X'.s
  tr : IsTr L h X'.univ o ψ

variable {L} {h : G.GAf} {N N' : ℕ} {X' : GenModel gb N'} {X : GenModel gb N}

def Leg.tot (c : Leg L h X' X) : X'.univ.A.left ⟶ X.univ.A.left := c.ψ.left ≫ c.φ.φ

theorem Leg.tot_w (c : Leg L h X' X) : c.tot ≫ X.univ.A.hom = X'.univ.A.hom ≫ c.q := by
  rw [Leg.tot, Category.assoc, c.φ.cart.1.w, ← Category.assoc, Over.w]

def Leg.pw (c : Leg L h X' X) (k : ℕ) : (GlobalTheory.KS.pow X'.univ.A k).left ⟶ (GlobalTheory.KS.pow X.univ.A k).left :=
  GlobalTheory.KS.powMap c.q c.tot c.tot_w k

def Leg.tw (c : Leg L h X' X) {k : ℕ} (α : Fin k → 𝓞 D.F) : (GlobalTheory.KS.pow X'.univ.A k).left ⟶ (GlobalTheory.KS.pow X.univ.A k).left :=
  c.pw k ≫ (GlobalTheory.KS.matEnd X.univ.act (Matrix.diagonal fun s => algebraMap (𝓞 D.F) D.O (α s))).left

abbrev sZ {N : ℕ} (X : GenModel gb N) (k : ℕ) : (GlobalTheory.KS.pow X.univ.A k).left ⟶ Sp ℂ := (GlobalTheory.KS.pow X.univ.A k).hom ≫ X.s

def gfamD {N : ℕ} (X : GenModel gb N) (hX : SmoothOfRelativeDimension D.g X.univ.A.hom)
    (hL : (X.univ.P.pull (lift (𝟙 X.univ.A) (𝟙 X.univ.A)).left).IsLB) : Fam ℂ D.O D.La D.g := gfam X.univ hX hL

def LevOk (L : Link D G) (N N' : ℕ) (h : G.GAf) : Prop :=
  3 ≤ N ∧ N.Coprime p ∧ 3 ≤ N' ∧ N'.Coprime p ∧ N ∣ N' ∧ ∀ u ∈ L.KN N', h * u * h⁻¹ ∈ L.KN N

end UpperTheory.Gal.W2
