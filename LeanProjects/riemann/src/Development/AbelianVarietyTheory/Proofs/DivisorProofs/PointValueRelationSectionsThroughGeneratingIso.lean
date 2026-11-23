import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOpSub
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTwistSections
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.GermVal

theorem valR_linComb_germ : ∀ (Y X₁ X₂ : Scheme.{0}) (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : Y ⟶ X₁) (f₂ : Y ⟶ X₂) (w : LB.Iso (L₁.pull f₁) (L₂.pull f₂)) (k : ℕ) (σ' : SecM (𝟙 X₁) L₁ k) (s : LB.Sec (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ)))), (∀ (y : Y) (i : L₂.ι) (j : L₁.ι), f₂ y ∈ L₂.U i → f₁ y ∈ L₁.U j → gs (𝟙 Y) y _ (s.f fun _ => i) = (gs (𝟙 Y) y _ (w.s (fun _ => i, fun _ => j)).val) ^ k * gs f₁ y _ (σ'.f fun _ => j)) → ∀ (F : Type) [CommRing F] [IsLocalRing F] (ξ : Sp F ⟶ Y) (i : L₂.ι) (j : L₁.ι), ⊤ ≤ (ξ ≫ f₂) ⁻¹ᵁ L₂.U i → ⊤ ≤ (ξ ≫ f₁) ⁻¹ᵁ L₁.U j → valR ξ _ (s.f fun _ => i) = (valR ξ _ (w.s (fun _ => i, fun _ => j)).val) ^ k * valR (ξ ≫ f₁) _ (σ'.f fun _ => j) := by
  intro Y X₁ X₂ L₁ L₂ f₁ f₂ w k σ' s H F _ _ ξ i j h2 h1
  have m2 : f₂ (ξ (IsLocalRing.closedPoint F)) ∈ L₂.U i := (GlobalTheory.ZH.CrdCalc.top_le_iff (ξ ≫ f₂) _).1 h2
  have m1 : f₁ (ξ (IsLocalRing.closedPoint F)) ∈ L₁.U j := (GlobalTheory.ZH.CrdCalc.top_le_iff (ξ ≫ f₁) _).1 h1
  have hy := H (ξ (IsLocalRing.closedPoint F)) i j m2 m1
  have a2 : ξ (IsLocalRing.closedPoint F) ∈ (LB.LinComb L₂ (K := Fin 1) (fun _ => f₂) (fun _ => (k : ℤ))).U (fun _ => i) :=
    Set.mem_iInter.2 fun _ => m2
  have aw : ξ (IsLocalRing.closedPoint F) ∈
      ((L₂.pull f₂).div (L₁.pull f₁)).U (fun _ => i, fun _ => j) :=
    ⟨Set.mem_iInter.2 fun _ => m2, Set.mem_iInter.2 fun _ => m1⟩
  have a1 : f₁ (ξ (IsLocalRing.closedPoint F)) ∈ (LB.LinComb L₁ (K := Fin 1) (fun _ => 𝟙 X₁) (fun _ => (k : ℤ))).U (fun _ => j) :=
    Set.mem_iInter.2 fun _ => m1
  rw [GlobalTheory.ZH.ThetaData.valR_eq_gs ξ _ a2, GlobalTheory.ZH.ThetaData.valR_eq_gs ξ _ aw,
    GlobalTheory.ZH.ThetaData.valR_eq_gs (ξ ≫ f₁) _ a1, gs_stalkMap ξ _ _ a2, gs_stalkMap ξ _ _ aw,
    gs_comp ξ f₁ _ _ a1, hy]
  simp only [map_mul, map_pow]

end GlobalTheory.GermVal
