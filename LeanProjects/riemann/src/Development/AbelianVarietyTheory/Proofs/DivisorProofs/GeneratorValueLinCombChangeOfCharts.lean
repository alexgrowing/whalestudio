import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLeWchart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.TanGauge

noncomputable section
namespace GlobalTheory.MBLow.TanGauge

theorem valR_linComb_g_factor {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    {A : Type} [CommRing A] (y : Sp A ⟶ Y) (j j' : K → L.ι)
    (hh : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j')) (k : K) :
    valR y (LB.wchart L φ j ⊓ LB.wchart L φ j')
      ((res (le_inf (inf_le_left.trans (LB.wchart_le L φ j k))
      (inf_le_right.trans (LB.wchart_le L φ j' k)) :
        LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)))
      (pullU (φ k) _ (L.g (j k) (j' k)))) ^ (ε k)).val = trV L (y ≫ φ k) (j k) (j' k) (ε k) := by
  have h0 : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ φ k ⁻¹ᵁ (L.U (j k) ⊓ L.U (j' k)) :=
    le_inf (inf_le_left.trans (LB.wchart_le L φ j k)) (inf_le_right.trans (LB.wchart_le L φ j' k))
  have key : (res h0 (pullU (φ k) (L.U (j k) ⊓ L.U (j' k)) (L.g (j k) (j' k)))) ^ (ε k) =
      res h0 (pullU (φ k) (L.U (j k) ⊓ L.U (j' k)) ((L.g (j k) (j' k)) ^ (ε k))) :=
    ((congrArg (res h0) (map_zpow (pullU (φ k) (L.U (j k) ⊓ L.U (j' k))) _ _)).trans
      (map_zpow (res h0) _ _)).symm
  refine (congrArg (fun u => valR y (LB.wchart L φ j ⊓ LB.wchart L φ j') (Units.val u)) key).trans ?_
  have e1 := GlobalTheory.ZH.CrdCalc.valR_res y h0 hh
      (((φ k).app (L.U (j k) ⊓ L.U (j' k))).hom ((L.g (j k) (j' k)) ^ (ε k)).val)
  refine Eq.trans ?_ (e1.trans ?_)
  · rfl
  · unfold trV
    exact GlobalTheory.ZH.EvCrd.valR_comp y (φ k) _ (hh.trans (y.preimage_mono h0)) _

theorem valR_gen_linComb : ∀ {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen → ∀ {A : Type} [CommRing A] (y : Sp A ⟶ Y) (j j' : K → L.ι),
    ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j → ⊤ ≤ y ⁻¹ᵁ LB.wchart L φ j' →
    valR y (LB.wchart L φ j) (t.s j).val =
      (∏ k, trV L (y ≫ φ k) (j k) (j' k) (ε k)) * valR y (LB.wchart L φ j') (t.s j').val := by
  intro X Y L K _ φ ε t ht A _ y j j' h h'
  have hh : ⊤ ≤ y ⁻¹ᵁ (LB.wchart L φ j ⊓ LB.wchart L φ j') := fun q hq => ⟨h hq, h' hq⟩
  have e : valR y (LB.wchart L φ j ⊓ LB.wchart L φ j')
      (res (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j) (t.s j)).val =
      valR y (LB.wchart L φ j ⊓ LB.wchart L φ j')
      ((show Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ from (LB.LinComb L φ ε).g j j').val *
        (res (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j') (t.s j')).val) :=
    congrArg (fun u => valR y (LB.wchart L φ j ⊓ LB.wchart L φ j') (Units.val u)) (ht j j')
  rw [GlobalTheory.ZH.CrdCalc.valR_mul y _ hh] at e
  have e1 := GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_left : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j) hh (t.s j).val
  have e2 := GlobalTheory.ZH.CrdCalc.valR_res y (inf_le_right : LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j') hh (t.s j').val
  have e3 : valR y (LB.wchart L φ j ⊓ LB.wchart L φ j') (show Γ(Y, LB.wchart L φ j ⊓ LB.wchart L φ j')ˣ from (LB.LinComb L φ ε).g j j').val =
      ∏ k, trV L (y ≫ φ k) (j k) (j' k) (ε k) := by
    change valR y (LB.wchart L φ j ⊓ LB.wchart L φ j') (Units.val (∏ k, _)) = _
    rw [Units.coe_prod, GlobalTheory.ZH.CrdCalc.valR_eq y _ hh, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← GlobalTheory.ZH.CrdCalc.valR_eq y _ hh]
    exact valR_linComb_g_factor L φ ε y j j' hh k
  rw [← e3]
  exact e1.symm.trans (e.trans (congrArg _ e2))

end GlobalTheory.MBLow.TanGauge
