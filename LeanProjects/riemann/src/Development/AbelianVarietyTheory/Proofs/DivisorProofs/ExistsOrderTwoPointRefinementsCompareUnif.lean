import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwoTorsionTwistOfSamePolarisedDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationDataTranslateOrderTwoIsTwistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegOfSameTorusTwistStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp

theorem point_and_compare : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₀ D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, SamePol D₀.toPre D.toPre → ∃ g : GtPt D.toPre (𝟙_ (Over (Sp R))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) ∧ ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G), LBIso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (D₁ D₂' : DegData R' (maximalIdeal R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ρ D₀.toPre D₁.toPre) ∧ Nonempty (IsPullDeg ρ D₂.toPre D₂'.toPre) ∧ Nonempty (IsPullDeg (RingHom.id R') D₁.toPre D₂'.toPre) := by
  have L1 := GlobalTheory.T.exists_twoTorsion_twist_of_same_polarisedData
  have L2 := GlobalTheory.T.uniformisationData_translate_orderTwo_isTwist
  have L3 := GlobalTheory.T.nonempty_isPullDeg_of_same_torus_twist
  intro R _ _ _ hB D₀ D A G _ _ hG U hS
  obtain ⟨g, hz, htw⟩ := L1 R hB D₀ D hS
  refine ⟨g, hz, fun a ha hlev A₂ D₂ U₂ hL => ?_⟩
  have h2 := L2 R hB D A G hG U g hz a ha hlev A₂ D₂ U₂ hL
  obtain ⟨h3⟩ := L3 R hB D₀ D₂ D g htw h2
  obtain ⟨s₀, -⟩ := GlobalTheory.DegPullId.exists_isPullDeg_id_self R (maximalIdeal R) hB.1 D₀
  obtain ⟨s₂, -⟩ := GlobalTheory.DegPullId.exists_isPullDeg_id_self R (maximalIdeal R) hB.1 D₂
  exact ⟨R, inferInstance, inferInstance, inferInstance, RingHom.id R, D₀, D₂,
    ⟨hB.1, Function.injective_id, RingHom.Finite.id R⟩, inferInstance, ⟨s₀⟩, ⟨s₂⟩, ⟨h3⟩⟩

end GlobalTheory.MumCmp
