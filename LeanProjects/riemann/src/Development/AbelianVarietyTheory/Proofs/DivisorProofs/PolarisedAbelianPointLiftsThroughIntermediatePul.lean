import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastMore
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormPsiPullLocalRingsOfIntegersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiNormIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolLift

theorem lift_of_pullback_comp : ∀ {S₀ S₁ S₂ : Scheme.{0}} (f₁ : S₁ ⟶ S₀) (f₂ : S₂ ⟶ S₁) (A : PolAV S₀) (B : PolAV S₁) (P : PolAV S₂) (b : B.A.left ⟶ A.A.left) (a : P.A.left ⟶ A.A.left), IsGrpPullback B.A A.A f₁ b → IsGrpPullback P.A A.A (f₂ ≫ f₁) a → ∃ c : P.A.left ⟶ B.A.left, c ≫ b = a ∧ c ≫ B.A.hom = P.A.hom ≫ f₂ ∧ IsGrpPullback P.A B.A f₂ c ∧ (LBIso P.L (A.L.pull a) → LBIso B.L (A.L.pull b) → LBIso P.L (B.L.pull c)) := by
  intro S₀ S₁ S₂ f₁ f₂ A B P b a hB hP
  have w : a ≫ A.A.hom = (P.A.hom ≫ f₂) ≫ f₁ := by
    rw [hP.1.w, Category.assoc]
  refine ⟨hB.1.lift a (P.A.hom ≫ f₂) w, hB.1.lift_fst _ _ w, hB.1.lift_snd _ _ w, ?_, ?_⟩
  · exact IsGrpPullback.cancel hB (hP.congr rfl (hB.1.lift_fst _ _ w).symm) (hB.1.lift_snd _ _ w)
  · intro hPa hBb
    have e : hB.1.lift a (P.A.hom ≫ f₂) w ≫ b = a := hB.1.lift_fst _ _ w
    have h2 : LBIso (B.L.pull (hB.1.lift a (P.A.hom ≫ f₂) w)) (A.L.pull a) :=
      LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull B.L _ _ rfl)
        (chartPullSame A.L (fun _ => a) (fun _ => b) _ _ fun _ => e.symm) hBb
    exact LBIso.trans P.isLB (pull_isLB A.isLB a) (pull_isLB B.isLB _) hPa h2.symm

end GlobalTheory.PolLift
