import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsionImports
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CardTorsionTranslateZerosLt

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpecialFibreLocus

theorem exists_sec_nonzeroLocus_iff : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (U : Unif (IsLocalRing.maximalIdeal V) D A G) (ϑ : H0 U.LG.L 1), ∃ θ : LB.Sec D.toPre.P.L, ∀ y : (thickObj V (IsLocalRing.maximalIdeal V) 0 G).left, (fstG (IsLocalRing.maximalIdeal V) 0 G).left y ∈ nonzeroLocus ϑ ↔ (U.gt 0).pG.left y ∈ nonzeroLocus θ := by
  intro hG V _ _ _ D A G _ _ U ϑ
  obtain ⟨f, hf⟩ := GlobalTheory.FewZeros.exists_weight_zero hG U ϑ
  obtain ⟨s, hs⟩ := GlobalTheory.FewZeros.exists_sec_of_formEq_id D.toPre.P.isLB (fun U _ k => by
    have e : toUnit D.toPre.P.A ≫ D.toPre.c 0 = 1 := cPoint_zero (D := D.toPre) _
    have e₁ : padd D.toPre.P.A (𝟙 D.toPre.P.A) 1 = 𝟙 D.toPre.P.A := _root_.mul_one (𝟙 D.toPre.P.A)
    have e₂ : toUnit D.toPre.P.A ≫ η[D.toPre.P.A] = 1 := rfl
    simp [Out.DegPre.famφB, Out.DegPre.famε, Fin.prod_univ_four, e, e₁, e₂]) f
  exact ⟨s, fun y => hs ▸ hf y⟩

end GlobalTheory.SpecialFibreLocus
