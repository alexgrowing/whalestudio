import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CharChPartZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPw
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowAmple

theorem pw_pw_mul {X : Scheme.{0}} (H : LB X) (a b : ℤ) :
    GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw H a) b = GlobalTheory.AbLaw.pw H (a * b) :=
  congrArg (fun g => (⟨H.ι, H.U, g⟩ : LB X))
    (funext fun i => funext fun j => (zpow_mul (H.g i j) a b).symm)

theorem relAmple_pw : ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) (L : LB B.left),
    L.IsLB → RelAmple B L → ∀ a : ℕ, 1 ≤ a → RelAmple B (GlobalTheory.AbLaw.pw L (a : ℤ)) := by
  intro R _ B L hL hA a ha
  obtain ⟨d, hd, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy R B L hL).1 hA
  obtain ⟨n', s', hs'⟩ := GlobalTheory.AbLaw.veryAmpleBy_pw R B.left B.hom (GlobalTheory.AbLaw.pw L d) n s
    (GlobalTheory.AbLaw.isLB_pw hL d) hs a ha
  have e : GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw L (d : ℤ)) (a : ℤ) = GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw L (a : ℤ)) (d : ℤ) := by
    rw [pw_pw_mul, pw_pw_mul, mul_comm]
  have h2 : ∃ t : Fin (n' + 1) → LB.Sec (GlobalTheory.AbLaw.pw (GlobalTheory.AbLaw.pw L (a : ℤ)) (d : ℤ)),
      GlobalTheory.AbLaw.VeryAmpleBy B.hom _ t := by
    rw [← e]; exact ⟨s', hs'⟩
  obtain ⟨t, ht⟩ := h2
  exact GlobalTheory.Unif.relAmple_of_veryAmpleBy (GlobalTheory.AbLaw.isLB_pw hL a) hd t ht

end GlobalTheory.PowAmple
