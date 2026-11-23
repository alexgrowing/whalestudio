import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l}

set_option maxHeartbeats 400000 in

theorem gfp_gen_of {L : Type} [Field L] (x : Sp L ⟶ Xo.X) {t' : SAB H (Sp L)} (m1 : SABMap t' Xo.univ.t x)
    (σ' : LB.Sec t'.PP.L) (hgen : ∀ s' : LB.Sec t'.PP.L, ∃! a : L, ∀ i, s'.f i = constFn t'.G.hom _ a * σ'.f i) :
    ∃ s : LB.Sec (PPx x), ∀ s'' : LB.Sec (PPx x), ∃! a : L, ∀ i, s''.f i = scal x a i * s.f i := by
  obtain ⟨w, hwg, -⟩ := m1.lin
  have hw : PGen w := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff w).1 hwg
  obtain ⟨su, hsu⟩ := thf_secUp hw Xo.univ.t.PP.isLB t'.PP.isLB σ'
  have hpb : IsPullback m1.cm.F t'.G.hom Xo.univ.t.G.hom x := And.left m1.cart
  obtain ⟨h, hF, hπ⟩ : ∃ h : Gx x ⟶ t'.G.left,
      h ≫ m1.cm.F = (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left ∧
        h ≫ t'.G.hom = (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left :=
    ⟨hpb.lift _ _ ((Over.w (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G)).trans
      (Over.w (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G)).symm), hpb.lift_fst _ _ _,
      hpb.lift_snd _ _ _⟩
  obtain ⟨k, hkφ, hkπ⟩ : ∃ k : t'.G.left ⟶ Gx x,
      k ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left = m1.cm.F ∧
        k ≫ (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom :=
    ⟨(CartesianMonoidalCategory.lift (Over.homMk t'.G.hom rfl : Over.mk (t'.G.hom ≫ x) ⟶ Over.mk x)
      (Over.homMk m1.cm.F hpb.w : Over.mk (t'.G.hom ≫ x) ⟶ Xo.univ.t.G)).left,
      congrArg (fun f => Over.Hom.left f) (CartesianMonoidalCategory.lift_snd
        (Over.homMk t'.G.hom rfl : Over.mk (t'.G.hom ≫ x) ⟶ Over.mk x)
        (Over.homMk m1.cm.F hpb.w : Over.mk (t'.G.hom ≫ x) ⟶ Xo.univ.t.G)),
      congrArg (fun f => Over.Hom.left f) (CartesianMonoidalCategory.lift_fst
        (Over.homMk t'.G.hom rfl : Over.mk (t'.G.hom ≫ x) ⟶ Over.mk x)
        (Over.homMk m1.cm.F hpb.w : Over.mk (t'.G.hom ≫ x) ⟶ Xo.univ.t.G))⟩
  have hkh : k ≫ h = 𝟙 _ := hpb.hom_ext (by rw [Category.assoc, hF, hkφ, Category.id_comp])
    (by rw [Category.assoc, hπ, hkπ, Category.id_comp])
  have hhk : h ≫ k = 𝟙 _ := by
    have e1 : (Over.homMk (h ≫ k) (by
        rw [← Over.w (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G)]
        simp only [Category.assoc]
        rw [reassoc_of% hkπ, reassoc_of% hπ]) :
        Over.mk x ⊗ Xo.univ.t.G ⟶ Over.mk x ⊗ Xo.univ.t.G) = 𝟙 _ := by
      apply CartesianMonoidalCategory.hom_ext
      · ext
        simp only [Over.comp_left, Over.homMk_left, Over.id_left, Category.assoc, Category.id_comp]
        rw [hkπ, hπ]
      · ext
        simp only [Over.comp_left, Over.homMk_left, Over.id_left, Category.assoc, Category.id_comp]
        rw [hkφ, hF]
    exact congrArg (fun f => Over.Hom.left f) e1
  have hscal : ∀ (b : L) (i : (PPx x).ι),
      scal x b i = constFn (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left ((PPx x).U i) b :=
    fun _ _ => rfl
  have hle : ∀ j, m1.cm.F ⁻¹ᵁ Xo.univ.t.PP.L.U j ≤ k ⁻¹ᵁ (PPx x).U (fun _ => j) := by
    intro j y hy
    have e : (k ≫ (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left) y ∈ Xo.univ.t.PP.L.U j := by
      rw [hkφ]; exact hy
    show k y ∈ (PPx x).U (fun _ => j)
    exact Set.mem_iInter.2 fun _ => e
  refine ⟨thfPull1 Xo.univ.t.PP.L h hF su, fun s'' => ?_⟩
  have hσ : ∀ (y : t'.G.left) (j j' : Xo.univ.t.PP.L.ι), m1.cm.F y ∈ Xo.univ.t.PP.L.U j →
      m1.cm.F y ∈ Xo.univ.t.PP.L.U j' →
      gs (𝟙 _) y _ ((k.appLE _ _ (hle j)).hom (s''.f fun _ => j)) =
        (gm m1.cm.F y (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j')).val *
          gs (𝟙 _) y _ ((k.appLE _ _ (hle j')).hom (s''.f fun _ => j')) := fun y j j' h1 h2 =>
    (gs_appLE k _ _ (hle j) (𝟙 _) y h1 _).trans ((gs_compat s'' (𝟙 _ ≫ k) y (hle j h1) (hle j' h2)).trans
      (congrArg₂ (· * ·) (congrArg Units.val ((gm_linComb Xo.univ.t.PP.L
        (fun _ : Fin 1 => (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left) (fun _ => (1 : ℤ))
        (𝟙 _ ≫ k) y (fun _ => j) (fun _ => j') (hle j h1) (hle j' h2)).trans
          (by rw [Fin.prod_univ_one, zpow_one, Category.id_comp, hkφ])))
        (gs_appLE k _ _ (hle j') (𝟙 _) y h2 _).symm))
  obtain ⟨s', hs'⟩ := sec_down hw Xo.univ.t.PP.isLB t'.PP.isLB
    (fun j => (k.appLE _ _ (hle j)).hom (s''.f fun _ => j)) hσ
  obtain ⟨a, ha, hau⟩ := hgen s'
  refine ⟨a, fun i => ?_, fun b hb => hau b fun k' => ?_⟩
  · obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    refine fn_ext fun y hy => ?_
    have hφy := LB.wchart_le Xo.univ.t.PP.L
      (fun _ : Fin 1 => (CartesianMonoidalCategory.snd (Over.mk x) Xo.univ.t.G).left) (fun _ => j) 0 hy
    have hFy : m1.cm.F (h y) ∈ Xo.univ.t.PP.L.U j := by
      have e : (h ≫ m1.cm.F) y ∈ Xo.univ.t.PP.L.U j := by rw [hF]; exact hφy
      exact e
    obtain ⟨k', hk'⟩ : ∃ k', h y ∈ t'.PP.L.U k' := by
      have : h y ∈ (⨆ k', t'.PP.L.U k') := by rw [t'.PP.isLB.cover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 this
    have hL : gs (𝟙 _) y _ (s''.f fun _ => j) = (gw w h y j k').val *
        (cst (CartesianMonoidalCategory.fst (Over.mk x) Xo.univ.t.G).left y a * gs h y _ (σ'.f k')) := by
      have e0 : gs (𝟙 (Gx x)) y ((PPx x).U fun _ => j) (s''.f fun _ => j) =
          gs (h ≫ k) y ((PPx x).U fun _ => j) (s''.f fun _ => j) := by rw [hhk]
      rw [e0, ← gs_appLE k _ _ (hle j) h y hFy, hs' _ h y j k' hFy hk', ha k', gs_mul h y _ hk',
        gs_constFn _ _ h y hk' a, hπ]
    rw [hL, gs_mul (𝟙 _) y _ hy]
    erw [hscal]
    rw [gs_constFn _ _ (𝟙 _) y hy a, Category.id_comp, mul_left_comm]
    congr 1
    symm
    refine (gs_appLE h _ _ (chart_le_pullback_open Xo.univ.t.PP.L h hF (fun _ => j)) (𝟙 _) y hy (su.f fun _ => j)).trans ?_
    rw [Category.id_comp]
    exact hsu _ h y (fun _ => j) k' (chart_le_pullback_open Xo.univ.t.PP.L h hF (fun _ => j) hy) hk'
  · refine fn_ext fun y hy => ?_
    obtain ⟨j, hj⟩ : ∃ j, m1.cm.F y ∈ Xo.univ.t.PP.L.U j := by
      have : m1.cm.F y ∈ (⨆ j, Xo.univ.t.PP.L.U j) := by rw [Xo.univ.t.PP.isLB.cover]; trivial
      exact TopologicalSpace.Opens.mem_iSup.1 this
    have hky : k y ∈ (PPx x).U (fun _ => j) := hle j hj
    have hd := hs' _ (𝟙 _) y j k' hj hy
    have hL : gs (𝟙 _) y _ ((k.appLE _ _ (hle j)).hom (s''.f fun _ => j)) =
        cst t'.G.hom y b * ((gw w (𝟙 _) y j k').val * gs (𝟙 _) y _ (σ'.f k')) := by
      rw [gs_appLE k _ _ (hle j) (𝟙 _) y hj, Category.id_comp, hb (fun _ => j), gs_mul k y _ hky]
      erw [hscal]
      rw [gs_constFn _ _ k y hky b, hkπ]
      congr 1
      refine (gs_appLE h _ _ (chart_le_pullback_open Xo.univ.t.PP.L h hF (fun _ => j)) k y hky (su.f fun _ => j)).trans ?_
      rw [hkh]
      exact hsu _ (𝟙 _) y (fun _ => j) k' (Set.mem_iInter.2 fun _ => hj) hy
    rw [gs_mul (𝟙 _) y _ hy, gs_constFn _ _ (𝟙 _) y hy b, Category.id_comp]
    apply (Units.mul_right_inj (gw w (𝟙 _) y j k')).1
    exact hd.symm.trans (hL.trans (by ring))

theorem gfp_gen (hT : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt) {L : Type} [Field L] (x : Sp L ⟶ Xo.X) :
    ∃ s : LB.Sec (PPx x), ∀ s'' : LB.Sec (PPx x), ∃! a : L, ∀ i, s''.f i = scal x a i * s.f i := by
  obtain ⟨PP', cub, sym, adj, prim, m1, -⟩ := sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull x Xo.univ.t
  obtain ⟨σ', hgen⟩ := globalSections_rank_one_fibre hT amplePt Xo.univ m1
  exact gfp_gen_of x m1 σ' hgen

end Formalism.L2.Pj
