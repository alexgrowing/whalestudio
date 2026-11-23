import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompPowPts
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.TorsionFamily

section General

variable {S : Scheme.{0}}

noncomputable def torsionLift (G : Over S) [GrpObj G] {T : Over S} (f : T ⟶ G) (n : ℕ) (hf : f ^ n = 1) :
    T ⟶ torsion G n :=
  pullback.lift f (toUnit T) (by rw [GlobalTheory.GrpTangent.comp_mulN, hf, Hom.one_def])

@[reassoc]
theorem torsionLift_ι (G : Over S) [GrpObj G] {T : Over S} (f : T ⟶ G) (n : ℕ) (hf : f ^ n = 1) :
    torsionLift G f n hf ≫ torsion.ι G n = f :=
  pullback.lift_fst _ _ _

theorem torsion_ι_pow (G : Over S) [GrpObj G] (n : ℕ) : torsion.ι G n ^ n = 1 := by
  rw [← GlobalTheory.GrpTangent.comp_mulN, Hom.one_def]
  exact pullback.condition.trans (congrArg (· ≫ η) (toUnit_unique _ _))

noncomputable def fpow (X : Over S) : ℕ → Over S
  | 0 => 𝟙_ (Over S)
  | k + 1 => X ⊗ fpow X k

noncomputable def fproj (X : Over S) : (k : ℕ) → Fin k → (fpow X k ⟶ X)
  | 0 => fun i => i.elim0
  | k + 1 => fun i => Fin.cases (fst X (fpow X k)) (fun j => snd X (fpow X k) ≫ fproj X k j) i

noncomputable def flift (X : Over S) {T : Over S} : (k : ℕ) → (Fin k → (T ⟶ X)) → (T ⟶ fpow X k)
  | 0 => fun _ => toUnit T
  | k + 1 => fun f => lift (f 0) (flift X k (fun j => f j.succ))

end General

end GlobalTheory.TorsionFamily
