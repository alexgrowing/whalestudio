import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLeWchart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge

noncomputable section
namespace GlobalTheory.MBLow.TanGauge

theorem trV_cocycle : ∀ {X : Scheme.{0}} (L : LB X), L.IsLB → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ X) (a b c : L.ι) (n : ℤ),
    ⊤ ≤ y ⁻¹ᵁ L.U a → ⊤ ≤ y ⁻¹ᵁ L.U b → ⊤ ≤ y ⁻¹ᵁ L.U c →
    trV L y a b n * trV L y b c n = trV L y a c n := by
  intro X L hL A _ y a b c n ha hb hc
  have hT : ⊤ ≤ y ⁻¹ᵁ (L.U a ⊓ L.U b ⊓ L.U c) := fun q hq => ⟨⟨ha hq, hb hq⟩, hc hq⟩
  have e := congrArg (fun u => ((u ^ n : Γ(X, L.U a ⊓ L.U b ⊓ L.U c)ˣ) : Γ(X, L.U a ⊓ L.U b ⊓ L.U c))) (hL.cocycle a b c)
  simp only [mul_zpow, ← map_zpow, Units.val_mul] at e
  have e' := congrArg (valR y (L.U a ⊓ L.U b ⊓ L.U c)) e
  rw [GlobalTheory.ZH.CrdCalc.valR_mul y _ hT] at e'
  unfold trV
  rw [← GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_left : L.U a ⊓ L.U b ⊓ L.U c ≤ L.U a ⊓ L.U b) hT,
    ← GlobalTheory.ZH.CrdCalc.valR_res y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      L.U a ⊓ L.U b ⊓ L.U c ≤ L.U b ⊓ L.U c) hT,
    ← GlobalTheory.ZH.CrdCalc.valR_res y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      L.U a ⊓ L.U b ⊓ L.U c ≤ L.U a ⊓ L.U c) hT]
  exact e'

end GlobalTheory.MBLow.TanGauge
end
