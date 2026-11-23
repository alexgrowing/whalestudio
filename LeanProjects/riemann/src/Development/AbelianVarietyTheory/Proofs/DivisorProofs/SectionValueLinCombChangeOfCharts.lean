import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLeWchart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge

noncomputable section
namespace GlobalTheory.MBLow.TanGauge

theorem valHom_res_pullU_zpow {X Y : Scheme.{0}} {A : Type} [CommRing A] (y : Sp A ⟶ Y) (f : Y ⟶ X)
    (U : X.Opens) {V : Y.Opens} (e : V ≤ f ⁻¹ᵁ U) (hV : ⊤ ≤ y ⁻¹ᵁ V) (u : Γ(X, U)ˣ) (n : ℤ) :
    GlobalTheory.ZH.CrdCalc.valHom y V hV ((res e (pullU f U u)) ^ n : Γ(Y, V)ˣ).val = valR (y ≫ f) U (u ^ n).val := by
  rw [← map_zpow, ← map_zpow, ← GlobalTheory.ZH.CrdCalc.valR_eq y V hV]
  have hU : ⊤ ≤ y ⁻¹ᵁ f ⁻¹ᵁ U := hV.trans (y.preimage_mono e)
  refine (GlobalTheory.ZH.CrdCalc.valR_res y e hV _).trans ?_
  exact GlobalTheory.ZH.EvCrd.valR_comp y f U hU _

theorem valR_linComb_sec : ∀ {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) {A : Type} [CommRing A] (y : Sp A ⟶ Y) (j j' : K → L.ι),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j → ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j' →
    valR y (LB.wchart L φ j) (s.f j) =
      (∏ k, trV L (y ≫ φ k) (j k) (j' k) (ε k)) * valR y (LB.wchart L φ j') (s.f j') := by
  intro X Y L K _ φ ε s A _ y j j' h h'
  have hh : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j') := fun q hq => ⟨h hq, h' hq⟩
  have e1 := GlobalTheory.ZH.CrdCalc.valR_res y
    (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j) hh (s.f j)
  have e2 := GlobalTheory.ZH.CrdCalc.valR_res y
    (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j') hh (s.f j')
  rw [← e1, ← e2]
  have c := s.compat j j'
  change valR y _ ((Y.presheaf.map _).hom _) = _ * valR y _ ((Y.presheaf.map _).hom _)
  refine (congrArg (valR y (LB.wchart L φ j ⊓ LB.wchart L φ j')) c).trans ?_
  refine (GlobalTheory.ZH.CrdCalc.valR_mul y (LB.wchart L φ j ⊓ LB.wchart L φ j') hh _ _).trans ?_
  congr 1
  refine (GlobalTheory.ZH.CrdCalc.valR_eq y (LB.wchart L φ j ⊓ LB.wchart L φ j') hh _).trans ?_
  dsimp only [LB.LinComb]
  rw [Units.coe_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hk : ⊤ ≤ (y ≫ φ k) ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)) := fun q _ =>
    ⟨wchart_top_le L φ j y h k (x := q) trivial, wchart_top_le L φ j' y h' k (x := q) trivial⟩
  unfold trV
  exact valHom_res_pullU_zpow y (φ k) (L.U (j k) ⊓ L.U (j' k)) (V := LB.wchart L φ j ⊓ LB.wchart L φ j') _ hh
    (L.g (j k) (j' k)) (ε k)

end GlobalTheory.MBLow.TanGauge
