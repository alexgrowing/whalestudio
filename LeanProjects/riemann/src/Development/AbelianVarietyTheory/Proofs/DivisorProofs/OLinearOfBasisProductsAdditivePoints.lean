import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiFor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory

theorem basisLin_oLinear : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (H : Scheme.{0}) (Y AH : Over H) [GrpObj AH] [IsCommMonObj AH] (actH : OActN D.O AH) (u : D.La → (Y ⟶ AH)), (∀ x y, u (x + y) = u x * u y) → ∀ (ιO ιL : Type) (bO : Module.Basis ιO ℤ D.O) (bL : Module.Basis ιL ℤ D.La), (∀ j i, u (bO j • bL i) = u (bL i) ≫ actH.act (bO j)) → ∀ (c : D.O) x, u (c • x) = u x ≫ actH.act c := by
  intro p _ D H Y AH _ _ actH u hu ιO ιL bO bL hb

  have hcomp : ∀ (f : Y ⟶ AH) (b c : D.O), f ≫ actH.act (b + c) = (f ≫ actH.act b) * (f ≫ actH.act c) := by
    intro f b c
    rw [actH.add, MonObj.comp_mul]

  have u0 : u 0 = 1 := by
    have h := hu 0 0
    simp only [add_zero] at h
    have := congrArg (fun t => t * (u 0)⁻¹) h
    simpa using this.symm
  let U : D.La →+ Additive (Y ⟶ AH) :=
    { toFun := fun x => Additive.ofMul (u x)
      map_zero' := by simp [u0]
      map_add' := fun x y => by simp [hu] }

  have step1 : ∀ i (c : D.O), u (c • bL i) = u (bL i) ≫ actH.act c := by
    intro i
    let F : D.O →+ Additive (Y ⟶ AH) := U.comp ((LinearMap.toSpanSingleton D.O D.La (bL i)).toAddMonoidHom)
    let G : D.O →+ Additive (Y ⟶ AH) :=
      { toFun := fun c => Additive.ofMul (u (bL i) ≫ actH.act c)
        map_zero' := by
          have h := hcomp (u (bL i)) 0 0
          simp only [add_zero] at h
          have : u (bL i) ≫ actH.act 0 = 1 := by
            have := congrArg (fun t => t * (u (bL i) ≫ actH.act 0)⁻¹) h
            simpa using this.symm
          simp [this]
        map_add' := fun b c => by simp [hcomp] }
    have hFG : F.toIntLinearMap = G.toIntLinearMap := bO.ext fun j => by
      simp [F, G, U, hb]
    intro c
    have := congrArg (fun L => L c) hFG
    simpa [F, G, U] using this
  intro c
  let F : D.La →+ Additive (Y ⟶ AH) := U.comp (DistribMulAction.toAddMonoidHom D.La c)
  let G : D.La →+ Additive (Y ⟶ AH) :=
    { toFun := fun x => Additive.ofMul (u x ≫ actH.act c)
      map_zero' := by
        haveI := actH.hom c
        simp [u0, MonObj.one_comp]
      map_add' := fun x y => by
        haveI := actH.hom c
        simp [hu, MonObj.mul_comp] }
  have hFG : F.toIntLinearMap = G.toIntLinearMap := bL.ext fun i => by
    simp [F, G, U, step1]
  intro x
  have := congrArg (fun L => L x) hFG
  simpa [F, G, U] using this

end GlobalTheory
