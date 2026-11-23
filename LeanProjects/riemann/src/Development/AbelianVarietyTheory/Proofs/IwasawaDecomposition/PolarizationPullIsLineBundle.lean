import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsChartOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationBaseChangeModels
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.Reg GlobalTheory.FlagMod

noncomputable section

namespace GlobalTheory.PolPull

variable {X Y' Y'' : Scheme.{0}}

def GermCoc (L : LB X) (f : Y' ⟶ X) (y : Y') : Prop :=
  ∀ i j k, f y ∈ L.U i → f y ∈ L.U j → f y ∈ L.U k →
    gm f y _ (L.g i j) * gm f y _ (L.g j k) = gm f y _ (L.g i k)

theorem germCoc_of_isLB {L : LB X} (hL : L.IsLB) (f : Y' ⟶ X) (y : Y') : GermCoc L f y :=
  fun _ _ _ hi hj hk => gm_cocycle hL f y hi hj hk

theorem germCoc_dual {L : LB X} {f : Y' ⟶ X} {y : Y'} (h : GermCoc L f y) : GermCoc (CechPic.dual L) f y := by
  intro i j k hi hj hk
  show gm f y _ (L.g i j)⁻¹ * gm f y _ (L.g j k)⁻¹ = gm f y _ (L.g i k)⁻¹
  rw [map_inv, map_inv, map_inv, ← h i j k hi hj hk, mul_inv]

theorem germCoc_tens {A B : LB X} {f : Y' ⟶ X} {y : Y'} (hA : GermCoc A f y) (hB : GermCoc B f y) :
    GermCoc (CechPic.tens A B) f y := by
  intro p q r hp hq hr
  rw [CechPic.gm_tens A B f y p q hp hq, CechPic.gm_tens A B f y q r hq hr, CechPic.gm_tens A B f y p r hp hr,
    ← hA _ _ _ hp.1 hq.1 hr.1, ← hB _ _ _ hp.2 hq.2 hr.2, mul_mul_mul_comm]

theorem germCoc_linComb (L : LB X) {K : Type} [Fintype K] (φ : K → (Y'' ⟶ X)) (ε : K → ℤ) {f : Y' ⟶ Y''} {y : Y'}
    (h : ∀ k, GermCoc L (f ≫ φ k) y) : GermCoc (LB.LinComb L φ ε) f y := by
  intro i j k hi hj hk
  show gm f y (LB.wchart L φ i ⊓ LB.wchart L φ j) _ * gm f y (LB.wchart L φ j ⊓ LB.wchart L φ k) _ =
    gm f y (LB.wchart L φ i ⊓ LB.wchart L φ k) _
  rw [gm_linComb L φ ε f y i j hi hj, gm_linComb L φ ε f y j k hj hk, gm_linComb L φ ε f y i k hi hk,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [← mul_zpow, h a _ _ _ (Set.mem_iInter.1 hi a) (Set.mem_iInter.1 hj a) (Set.mem_iInter.1 hk a)]

section Det

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

theorem detChg_cocycle (M M' M'' : MChart Y) :
    res (inf_le_left : M.U ⊓ M'.U ⊓ M''.U ≤ M.U ⊓ M'.U) (detChg M M') *
    res (le_inf (inf_le_left.trans inf_le_right) inf_le_right : M.U ⊓ M'.U ⊓ M''.U ≤ M'.U ⊓ M''.U) (detChg M' M'') =
    res (le_inf (inf_le_left.trans inf_le_left) inf_le_right : M.U ⊓ M'.U ⊓ M''.U ≤ M.U ⊓ M''.U) (detChg M M'') := by
  refine Units.ext (ext_ev fun S _ z hz => ?_)
  rw [Units.val_mul, map_mul]
  exact ((congrArg₂ (· * ·) (ev_res z _ hz _ _) (ev_res z _ hz _ _)).trans
    (ev_detChg_mul M M' M'' z (le_preimage_mono inf_le_left hz)
      (le_preimage_mono (le_inf (inf_le_left.trans inf_le_right) inf_le_right) hz)
      (le_preimage_mono (le_inf (inf_le_left.trans inf_le_left) inf_le_right) hz))).trans (ev_res z _ hz _ _).symm

theorem germCoc_detLie (f : Y' ⟶ Y.X) (y : Y') : GermCoc (detLie Y) f y := by
  intro M M' M'' hi hj hk
  have hm : f y ∈ M.U ⊓ M'.U ⊓ M''.U := ⟨⟨hi, hj⟩, hk⟩
  have e := congrArg (gm f y _) (detChg_cocycle M M' M'')
  rw [map_mul, gm_res f y _ hm, gm_res f y _ hm, gm_res f y _ hm] at e
  exact e

theorem isLB_pull_polOf (Y : Model Xo c β) (m : ℕ) (DY : EffCartierData Y.X) {X' : Scheme.{0}} (F : X' ⟶ Y.X)
    (hF : ∀ y : X', ∃ M : MChart Y, F y ∈ M.U) : ((polOf Y m DY).pull F).IsLB := by
  have hG : ∀ (f : X' ⟶ Y.X) (y : X'), GermCoc (polOf Y m DY) f y := fun f y =>
    germCoc_tens (germCoc_linComb _ _ _ fun _ => germCoc_dual (germCoc_detLie _ _))
      (germCoc_dual (germCoc_of_isLB DY.isLB_lb _ _))
  refine ⟨top_le_iff.1 fun y _ => ?_, fun J => unit_ext fun y hy => ?_, fun I J K => unit_ext fun y hy => ?_⟩
  · obtain ⟨M, hM⟩ := hF y
    obtain ⟨b, hb⟩ := exists_chart DY.isLB_lb (F y)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => ((fun _ => M), b),
      Set.mem_iInter.2 fun _ => ⟨Set.mem_iInter.2 fun _ => hM, hb⟩⟩
  · rw [gm_res (𝟙 X') y _ hy, map_one, gm_pull_g _ F (𝟙 X') y J J hy hy]
    have hJ := Set.mem_iInter.1 hy PUnit.unit
    exact mul_eq_left.1 (hG _ y _ _ _ hJ hJ hJ)
  · rw [map_mul, gm_res (𝟙 X') y _ hy, gm_res (𝟙 X') y _ hy, gm_res (𝟙 X') y _ hy,
      gm_pull_g _ F (𝟙 X') y I J hy.1.1 hy.1.2, gm_pull_g _ F (𝟙 X') y J K hy.1.2 hy.2,
      gm_pull_g _ F (𝟙 X') y I K hy.1.1 hy.2]
    exact hG _ y _ _ _ (Set.mem_iInter.1 hy.1.1 PUnit.unit) (Set.mem_iInter.1 hy.1.2 PUnit.unit)
      (Set.mem_iInter.1 hy.2 PUnit.unit)

end Det

end GlobalTheory.PolPull
