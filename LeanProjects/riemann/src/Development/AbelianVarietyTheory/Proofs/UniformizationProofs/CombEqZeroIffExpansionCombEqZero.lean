import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtIffStalks
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.VanishOfTermsVanish
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsFSum

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem comb_eq_zero_iff_expansion_comb_eq_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (n : ℕ) (c : Fin n → R) (σ : Fin n → LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f : Fin n → ∀ α, D.toPre.SecB k α), (∀ i e, U.ExpandsAt e k (σ i) (f i)) → ((∀ j, ∑ i, resTop _ (scal G.hom (c i)) * (σ i).f j = 0) → ∀ α j, ∑ i, resTop _ (scal D.toPre.P.A.hom (c i)) * (f i α).f j = 0) ∧ (GeometricallyConnected G.hom → (∀ α j, ∑ i, resTop _ (scal D.toPre.P.A.hom (c i)) * (f i α).f j = 0) → ∀ j, ∑ i, resTop _ (scal G.hom (c i)) * (σ i).f j = 0) := by
  intro R _ _ I hR D A G _ _ U k n c σ f hE
  obtain ⟨hN, -, -, hC⟩ := hR
  have hI : I ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot I
  let σ₀ := ExpansionLinear.secComb (fun i => scal G.hom (c i)) σ
  let f₀ : ∀ α, D.toPre.SecB k α := fun α =>
    ExpansionLinear.secComb (fun i => scal D.toPre.P.A.hom (c i)) (fun i => f i α)
  have h₀ : ∀ e, U.ExpandsAt e k σ₀ f₀ := fun e =>
    expandsAt_linear R I D A G U k e n c σ f σ₀ f₀ (fun i => hE i e) (fun _ => rfl) (fun _ _ => rfl)
  refine ⟨fun h α => ?_, fun hG h => ?_⟩
  · have := D.toPre.P.isAb.smooth
    have := D.toPre.P.isAb.geomConnected
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I hI D.toPre.P.A).1 _
      (DVR.linComb_isLB _ D.toPre.P.isLB _ _) (f₀ α) fun e j => ?_
    refine (ExtDiv.pG_app_eq_zero_iff (U.gt e) _ _).1
      (WeightPf.weightIndep R I D A G U e k σ₀ f₀ (fun j => ?_) (h₀ e) α j)
    exact (congrArg _ (h j)).trans (map_zero _)
  · have := U.smooth
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I hI G).1 _
      (DVR.linComb_isLB _ U.LG.isLB _ _) σ₀ fun e j => ?_
    exact ClosedFibreTerm.vanish_of_terms_vanish U e k σ₀ f₀ (h₀ e)
      (fun α j => (congrArg _ (h α j)).trans (map_zero _)) j

end GlobalTheory
