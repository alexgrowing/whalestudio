import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

theorem veryAmpleBy_pw_of_affine_loci : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (H : LB X) (n : ℕ) (t : Fin (n + 1) → LB.Sec H), H.IsLB → (⨆ i, nonzeroLocus (t i) = ⊤) → (∀ i, IsAffineOpen (nonzeroLocus (t i))) → ∃ d : ℕ, 1 ≤ d ∧ ∃ (n' : ℕ) (s : Fin (n' + 1) → LB.Sec (pw H d)), VeryAmpleBy f (pw H d) s := by
  intro R _ X f _ H n t hH hc ha
  have h : IsAmpleLB H :=
    isAmpleLB_of_cover hH le_rfl (fun i => secToPow (t i) 1)
      (by simp only [nonzeroLocus_secToPow _ le_rfl, hc])
      fun i => (nonzeroLocus_secToPow (t i) le_rfl).symm ▸ ha i
  have : IsProper (Over.mk f).hom := ‹IsProper f›
  exact (Unif.relAmple_iff_veryAmpleBy R (Over.mk f) H hH).1
    ((relAmple_iff_isAmpleLB_of_isAffine (Over.mk f) hH).2 h)

end GlobalTheory.AbLaw
