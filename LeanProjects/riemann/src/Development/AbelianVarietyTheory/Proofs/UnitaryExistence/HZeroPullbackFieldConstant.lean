import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.InversionStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.HolSec

theorem exists_sec_pull {X X' : Scheme.{0}} (L : LB X) (F : X' ⟶ X) (W : X.Opens) (mem : ∀ x, F x ∈ W)
    (θ₀ : ∀ j, Γ(X, W ⊓ L.U j)) (hθ₀ : θ₀ ∈ secOn L W) :
    ∃ t : LB.Sec (L.pull F), ∀ j (x : Sp ℂ ⟶ X'), ⊤ ≤ (x ≫ F) ⁻¹ᵁ L.U j →
      valAt' x ((L.pull F).U (fun _ => j)) (t.f (fun _ => j)) = valAt' (x ≫ F) (W ⊓ L.U j) (θ₀ j) := by
  have le : ∀ J, (L.pull F).U J ≤ F ⁻¹ᵁ (W ⊓ L.U (J PUnit.unit)) := fun J x hx => ⟨mem x, mem_pull.1 hx⟩
  have ev : ∀ y J, y ∈ (L.pull F).U J → gs (𝟙 _) y _ ((F.appLE _ _ (le J)).hom (θ₀ _)) = gs F y _ (θ₀ (J PUnit.unit)) :=
    fun y J h => (gs_appLE F _ _ (le J) (𝟙 _) y h _).trans (by rw [Category.id_comp])
  refine ⟨⟨fun J => (F.appLE _ _ (le J)).hom (θ₀ _), fun J J' => fn_ext fun y hy => ?_⟩, fun j x hx => ?_⟩
  · have h := mem_pull.1 hy.1
    have h' := mem_pull.1 hy.2
    have hm : F y ∈ W ⊓ L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit) := ⟨⟨mem y, h⟩, h'⟩
    have e := congrArg (gs F y _) (hθ₀ (J PUnit.unit) (J' PUnit.unit))
    rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm, gs_unit _ y (L.U _ ⊓ L.U _) ⟨h, h'⟩] at e
    rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_unit _ y _ hy, ev y J hy.1, ev y J' hy.2,
      gm_pull_g L F (𝟙 _) y J J' hy.1 hy.2, Category.id_comp]
    exact e
  · exact valAt'_appLE x F _ _ (le _) _ (fun p hp => mem_pull.2 (hx hp))

end GlobalTheory.HolSec
