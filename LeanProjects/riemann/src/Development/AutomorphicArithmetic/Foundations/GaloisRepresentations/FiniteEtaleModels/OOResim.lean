import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiftUnit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.OTResim

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.FiniteEtaleModels.O

private def reObj {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R}
    (o : GObj gb N s) (g : ℕ → G.La →+ G.La) (hg : IsSys g) (hpos : 0 < N) : GObj gb N s :=
  { o with
    eta := fun y => o.eta (g N y)
    eta_add := fun x y => by rw [map_add, o.eta_add]
    eta_lin := fun a x => by
      obtain ⟨z, hz⟩ := hg.lin N hpos a x
      rw [hz, o.eta_add, o.eta_ker, _root_.mul_one, o.eta_lin]
    eta_ker := fun x => by rw [map_nsmul, o.eta_ker]
    geom := fun k _ _ x β hx => by
      obtain ⟨I, hI⟩ := o.geom k x β hx
      obtain ⟨I', hI'⟩ := tResim G k _ _ _ I g hg
      exact ⟨I', fun y => by rw [hI' N hpos y]; exact hI (g N y)⟩ }

theorem oResim : OResim := by
  intro q _ D R R' _ _ _ b gb N N₀ c hN hpos X X₁ s s₁ o u f n g hg hg0
  have hN0 : 0 < N₀ := Nat.pos_of_ne_zero (by rintro rfl; simp [hN] at hpos)
  have hc : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; simp [hN] at hpos)
  have key : ∀ y : D.La, u.eta (g N y) = u.eta y := by
    intro y
    obtain ⟨z, hz⟩ : ∃ z : D.La, g (N₀ * c) y = g N₀ y + N₀ • z := hg.tow N₀ c hN0 hc y
    obtain ⟨z', hz'⟩ := hg0 y
    subst hN
    rw [hz, hz', u.eta_add, u.eta_add, u.eta_ker, u.eta_ker, _root_.mul_one, _root_.mul_one]
  refine ⟨reObj o g hg hpos, ⟨n.φ, n.φ₂, n.cart, n.sq, n.act, n.pol, fun y => ?_⟩, fun y => rfl⟩
  show Over.Hom.left (o.eta (g N (c • y))) ≫ n.φ = f ≫ Over.Hom.left (u.eta y)
  rw [map_nsmul, n.eta, key]

end UpperTheory.Gal.FiniteEtaleModels.O
