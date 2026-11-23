import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLeWchart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge

noncomputable section

namespace GlobalTheory.MBLow.TanGauge

theorem valR_secLin : ∀ {X Y Y' : Scheme.{0}} (L : LB X) {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂]
    (φ₁ : K₁ → (Y' ⟶ X)) (ε₁ : K₁ → ℤ) (s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)) (φ₂ : K₂ → (Y ⟶ X)) (ε₂ : K₂ → ℤ) {n : ℕ}
    (s₂ : Fin n → LB.Sec (LB.LinComb L φ₂ ε₂)) (h : Y' ⟶ Y) (c : Fin n → Γ(Y', ⊤)),
    GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c → ∀ (j₁ : K₁ → L.ι) (j₂ : K₂ → L.ι),
    LB.Coh L (Sum.elim φ₁ (fun k => h ≫ φ₂ k)) (Sum.elim j₁ j₂) → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ Y'),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ₁ j₁ → ⊤ ≤ (y ≫ h) ⁻¹ᵁ LB.wchart L φ₂ j₂ →
    valR y (LB.wchart L φ₁ j₁) (s₁.f j₁) = ∑ i, valR y ⊤ (c i) * valR (y ≫ h) (LB.wchart L φ₂ j₂) ((s₂ i).f j₂) := by
  intro X Y Y' L K₁ K₂ _ _ φ₁ ε₁ s₁ φ₂ ε₂ n s₂ h c H j₁ j₂ hc A _ y hy₁ hy₂
  have hy₂' : ⊤ ≤ y ⁻¹ᵁ LB.wchart L (fun k => h ≫ φ₂ k) j₂ :=
    top_le_wchart L _ _ y fun k => by rw [← Category.assoc]; exact wchart_top_le L φ₂ j₂ (y ≫ h) hy₂ k
  have hW : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂) := fun q hq => ⟨hy₁ hq, hy₂' hq⟩
  have a₂ : LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂ ≤ h ⁻¹ᵁ LB.wchart L φ₂ j₂ :=
    inf_le_right.trans (fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k)
  have e := congrArg (valR y (LB.wchart L φ₁ j₁ ⊓ LB.wchart L (fun k => h ≫ φ₂ k) j₂)) (H j₁ j₂ hc)
  rw [← GlobalTheory.ZH.CrdCalc.valR_res y inf_le_left hW (s₁.f j₁)]
  refine e.trans ?_
  rw [GlobalTheory.ZH.CrdCalc.valR_eq y _ hW, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← GlobalTheory.ZH.CrdCalc.valR_eq y _ hW, ← GlobalTheory.ZH.CrdCalc.valR_eq y _ hW]
  congr 1
  · exact GlobalTheory.ZH.CrdCalc.valR_res y le_top hW (c i)
  · exact (GlobalTheory.ZH.CrdCalc.valR_res y a₂ hW _).trans
      (GlobalTheory.ZH.EvCrd.valR_comp y h (LB.wchart L φ₂ j₂) (fun q hq => hy₂ hq) _)

end GlobalTheory.MBLow.TanGauge
