import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBGen
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IntChartPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExistsTruncatedIntegralChart
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory.PrimDown

theorem exists_down_id {X₀ X' Y : Scheme.{0}} {L : LB X₀} {L' : LB X'} {F : X' ⟶ X₀} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (ht : t.IsGen) : ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (y : Y) p q, y ∈ LB.wchart L (fun k => φ' k ≫ F) p → y ∈ LB.wchart L' φ' q →
        gm (𝟙 Y) y _ (a.s q) = (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ q : K → L'.ι, ∃ s : Γ(Y, LB.wchart L' φ' q)ˣ, ∀ (y : Y) p,
      y ∈ LB.wchart L (fun k => φ' k ≫ F) p → y ∈ LB.wchart L' φ' q →
      gm (𝟙 Y) y _ s = (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) := by
    intro q
    have hv : ∀ (y : Y) p, y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
        gm (𝟙 Y) y _ ((u p q)⁻¹ * res inf_le_left (t.s p)) =
          (pw w φ' ε (𝟙 Y) y p q)⁻¹ * gm (𝟙 Y) y (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) :=
      fun y p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans (congrArg (·⁻¹) (hu p q _ _ y hz)))
        (gm_res _ y _ hz _))
    obtain ⟨s, hs⟩ := glue_unit _ (fun p => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q) (fun _ => inf_le_right)
      (fun y hy => by
        choose p hp using fun k => exists_chart hL (F (φ' k y))
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp, hy⟩) (fun p => (u p q)⁻¹ * res inf_le_left (t.s p))
      (fun p p' y hy => by
        rw [hv y p hy.1, hv y p' hy.2, pw_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.2.1 hy.1.2 hy.1.2,
          trF_self hL' _ ε (𝟙 Y) y hy.1.2, gen_trans ht (𝟙 Y) y hy.1.1 hy.2.1, inv_one, _root_.mul_one, mul_inv,
          _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun y p h₁ h₂ => ?_⟩
    have hz : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
    exact (gm_res _ y inf_le_right hz s).symm.trans ((congrArg (gm _ y _) (hs p)).trans (hv y p hz))
  choose s hs using glue
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun y p q h₁ h₂ => hs q y p h₁ h₂⟩
  choose p hp using fun k => exists_chart hL (F (φ' k y))
  have m : y ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
  refine (hs j y p m hj).trans (Eq.trans ?_ (congrArg _ (hs j' y p m hj')).symm)
  rw [pw_trans hw φ' ε (𝟙 Y) y m m hj hj', trF_self hL _ ε (𝟙 Y) y m, _root_.one_mul, mul_inv, inv_inv, _root_.mul_assoc]

theorem exists_down_all {X₀ X' Y : Scheme.{0}} {L : LB X₀} {L' : LB X'} {F : X' ⟶ X₀} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
          gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) =
            pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) := by
  obtain ⟨a, ha, hv⟩ := exists_down_id hw hL hL' t ht
  obtain ⟨t₁, -, hu⟩ := exists_up hw hL hL' a ha
  have e : ∀ p, t.s p = t₁.s p := fun p => unit_ext fun y hy => by
    choose q hq using fun k => exists_chart hL' (φ' k y)
    have m : y ∈ LB.wchart L' φ' q := Set.mem_iInter.2 hq
    refine Eq.trans ?_ (hu _ (𝟙 Y) y p q hy m).symm
    exact (mul_inv_cancel_left _ _).symm.trans (congrArg _ (hv y p q hy m).symm)
  exact ⟨a, ha, fun Z r z p q hp hq => (congrArg (gm r z _) (e p)).trans (hu Z r z p q hp hq)⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem prod_eSec {X0 : Scheme.{0}} (t : SAB H X0) {U : Type} [CommGroup U]
    (h : ((𝟙_ (Over X0)).left ⟶ t.G.left) → U) :
    ∏ k, h (eSec t.G ≫ primφ t k) ^ primε k = h (eSec t.G) := by
  have hpt : ∀ I : ULift.{0} (Finset (Fin 2)), eSec t.G ≫ cφG t ![𝟙 t.G, t.act.act H.w0] I =
      (psum t.G ![1, η[t.G] ≫ t.act.act H.w0] I.down).left := by
    intro I
    simp only [cφG, eSec, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · exact (Category.comp_id _).trans (GermB.eta_one t.G)
    · rfl
  rw [Fintype.prod_sum_type]
  simp only [primφ, primε, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, zpow_neg,
    Finset.prod_inv_distrib, zpow_one]
  have z := (Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ cε 2 I) (hpt I)).trans
    (GermB.cube_one_left t (fun p => h p.left) (η[t.G] ≫ t.act.act H.w0))
  exact (congrArg (fun u => h (eSec t.G) * u⁻¹) z).trans (by rw [inv_one, _root_.mul_one])

end GlobalTheory.PrimDown

namespace GlobalTheory

theorem primG_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 X1 : Scheme.{0}) (t : SAB H X0) (t' : SAB H X1) (f : X1 ⟶ X0) (mp : SABMap t' t f) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ wP : PrimTyG t, IsPrimG t wP → ∃ wP' : PrimTyG t', IsPrimG t' wP' ∧ (∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun k => primφ t' k ≫ mp.φ) primε), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (LB.pullGen t.PP.L _ _ wP mp.φ) ∧ LB.Gen.Maps (LB.linCombIso w (primφ t') primε) wP' (flatGen t.PP.L mp.φ _ _ c₁)) := by
  intro E _ _ _ H X0 X1 t t' f mp w hw wP hP
  have hL := t.PP.isLB
  have hL' := t'.PP.isLB
  obtain ⟨c₁, hc₁, hcc⟩ := ChartPrimTrPf.exists_reindex t.PP.L (φ := fun k => mp.φ ≫ primφ t k)
    (φ' := fun k => primφ t' k ≫ mp.φ) (funext fun k => ChartPrimTrPf.primφ_comm mp k) primε
    (LB.pullGen t.PP.L (primφ t) primε wP mp.φ) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hP.1 _)
  obtain ⟨a, ha, R⟩ := PrimDown.exists_down_all ((isGen_iff w).1 hw.1) hL hL' c₁ hc₁
  refine ⟨a, ⟨ha, corr_of_val hL' fun y J' hJ' => ?_⟩, c₁, hcc, ChartPrimTrPf.maps_flat w _ _ a c₁ R⟩
  choose J hJ using fun χ : (𝟙_ (Over X1)).left ⟶ t.G.left => exists_chart hL (χ y)
  have hJ : Good t.PP.L y J := hJ
  have pm := (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig mp.cm.e _
    (rigPull_le mp.cm.F mp.cm.e mp.cm.e_comm t.PP.L) (fun _ => rfl)).1 hw.2
  have e₁ := pm _ (𝟙 _) y (fun _ => J (eSec t'.G ≫ mp.φ)) (fun _ => J' (eSec t'.G)) (fun _ => hJ _) (fun _ => hJ' _)
  rw [Fintype.prod_unique, zpow_one, Category.id_comp, Category.id_comp] at e₁
  have e₂ : val c₁ (eSec t'.G) y J =
      gw w (eSec t'.G) y (J (eSec t'.G ≫ mp.φ)) (J' (eSec t'.G)) * val a (eSec t'.G) y J' := by
    refine (R _ (eSec t'.G) y _ _ (hJ.mem _ _) (hJ'.mem _ _)).trans (congrArg₂ (· * ·) ?_ rfl)
    refine Eq.trans ?_ (PrimDown.prod_eSec t' (fun q => gw w q y (J (q ≫ mp.φ)) (J' q)))
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Category.assoc]
  have e₃ : val c₁ (eSec t'.G) y J = val (L := t.PP.L) (φ := fun _ : PUnit => eSec t.G) (ε := fun _ => 1)
      t.PP.rig mp.cm.e y J := by
    refine (val_corr hJ hcc _).trans ((val_pull hJ _ _ _).trans ?_)
    refine Eq.trans ?_ (val_corr hJ hP.2 _)
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    exact congrArg (fun r => val (L := t.PP.L) (φ := primφ t) (ε := primε) wP r y J) mp.cm.e_comm
  have e₄ := (val_of (L := t.PP.L) (φ := fun _ : PUnit => eSec t.G) (ε := fun _ => 1) t.PP.rig mp.cm.e y J
    (fun _ => J (eSec t'.G ≫ mp.φ)) (fun _ => congrArg J mp.cm.e_comm.symm)).trans e₁
  have e₅ := mul_left_cancel (e₂.symm.trans (e₃.trans e₄))
  refine (val_pull hJ' _ _ _).trans ?_
  rw [Category.id_comp]
  refine e₅.trans ?_
  exact (val_of (L := t'.PP.L) (φ := fun _ : PUnit => eSec t'.G) (ε := fun _ => 1) t'.PP.rig (𝟙 _) y J' _
    (fun _ => by rw [Category.id_comp])).symm

end GlobalTheory
