import Formalism.LocalToGlobal.ProjectiveLattices.ThetaFramePf

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

set_option maxHeartbeats 400000 in

theorem frame_of_gen (Xo : Moduli Dw l) {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (t' : SAB H (Sp S))
    (m1 : SABMap t' Xo.univ.t x) (σ' : LB.Sec t'.PP.L)
    (hgen : ∀ s' : LB.Sec t'.PP.L, ∃! a : S, ∀ i, s'.f i = constFn t'.G.hom _ a * σ'.f i) :
    ∃ (s : LB.Sec (PPx x)) (w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)),
      RigIso m1 w1 ∧ IsoMaps w1 σ' s1 ∧
      (∀ g : t'.G.left ⟶ Gx x, g ≫ (snd (Over.mk x) Xo.univ.t.G).left = m1.φ →
        g ≫ (fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom →
        ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx x).U (fun _ => j PUnit.unit)),
          s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) ∧
      ∀ s'' : LB.Sec (PPx x), ∃! a : S, ∀ i, s''.f i = scal x a i * s.f i := by
  obtain ⟨w1, hw1, hrig, -⟩ := m1.lin
  have hPG := (ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff w1).1 hw1
  obtain ⟨s1, hs1⟩ := thf_secUp hPG Xo.univ.t.PP.isLB t'.PP.isLB σ'
  have pb := m1.cart.1
  have hcond : (snd (Over.mk x) Xo.univ.t.G).left ≫ Xo.univ.t.G.hom = (fst (Over.mk x) Xo.univ.t.G).left ≫ x :=
    (Over.w (snd (Over.mk x) Xo.univ.t.G)).trans (Over.w (fst (Over.mk x) Xo.univ.t.G)).symm
  obtain ⟨h, hF, hS⟩ : ∃ h : Gx x ⟶ t'.G.left, h ≫ m1.φ = (snd (Over.mk x) Xo.univ.t.G).left ∧
      h ≫ t'.G.hom = (fst (Over.mk x) Xo.univ.t.G).left :=
    ⟨pb.lift _ _ hcond, pb.lift_fst _ _ hcond, pb.lift_snd _ _ hcond⟩
  obtain ⟨g0, g0F, g0S, hhg⟩ : ∃ g0 : t'.G.left ⟶ Gx x, g0 ≫ (snd (Over.mk x) Xo.univ.t.G).left = m1.φ ∧
      g0 ≫ (fst (Over.mk x) Xo.univ.t.G).left = t'.G.hom ∧ h ≫ g0 = 𝟙 _ := by
    let P : Over Xo.X := Over.mk (m1.φ ≫ Xo.univ.t.G.hom)
    let a : P ⟶ Over.mk x := Over.homMk t'.G.hom pb.w.symm
    let b : P ⟶ Xo.univ.t.G := Over.homMk m1.φ rfl
    let hO : (Over.mk x ⊗ Xo.univ.t.G) ⟶ P := Over.homMk h (by
      show h ≫ m1.φ ≫ Xo.univ.t.G.hom = _
      rw [← Category.assoc, hF]
      exact Over.w (snd (Over.mk x) Xo.univ.t.G))
    have e : hO ≫ lift a b = 𝟙 _ := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, lift_fst, Category.id_comp]
        ext
        exact hS
      · rw [Category.assoc, lift_snd, Category.id_comp]
        ext
        exact hF
    exact ⟨(lift a b).left, congrArg (fun f => f.left) (lift_snd (f := a) (g := b)),
      congrArg (fun f => f.left) (lift_fst (f := a) (g := b)), congrArg (fun f => f.left) e⟩
  have hgh0 : g0 ≫ h = 𝟙 _ := pb.hom_ext
    (by rw [Category.assoc, hF, g0F, Category.id_comp])
    (by rw [Category.assoc, hS, g0S, Category.id_comp])
  refine ⟨thfPull1 Xo.univ.t.PP.L h hF s1, w1, s1, ⟨hw1, hrig⟩, ?_, ?_, ?_⟩
  · intro i k
    refine fn_ext fun y hy => ?_
    have key := hs1 _ (𝟙 _) y i k hy.1 hy.2
    rw [gs_res (𝟙 _) y _ hy, key, gs_mul (𝟙 _) y _ hy, gs_res (𝟙 _) y _ hy]
    congr 1
    exact (gs_unit (𝟙 _) y _ hy (w1.s (i, k))).symm
  · intro g hgs hgf j hj
    have hgh : g ≫ h = 𝟙 _ := pb.hom_ext
      (by rw [Category.assoc, hF, hgs, Category.id_comp])
      (by rw [Category.assoc, hS, hgf, Category.id_comp])
    refine fn_ext fun y hy => ?_
    have e1 := gs_appLE g _ _ hj (𝟙 _) y hy ((thfPull1 Xo.univ.t.PP.L h hF s1).f (fun _ => j PUnit.unit))
    have e2 : gs g y ((PPx x).U (fun _ => j PUnit.unit)) ((thfPull1 Xo.univ.t.PP.L h hF s1).f (fun _ => j PUnit.unit)) =
        gs (g ≫ h) y _ (s1.f (fun _ => j PUnit.unit)) :=
      gs_appLE h _ _ _ g y (hj hy) _
    rw [Category.id_comp] at e1
    rw [e1, e2, hgh]
    all_goals rfl
  · intro s''
    have hle : ∀ j, m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j ≤ g0 ⁻¹ᵁ (PPx x).U (fun _ => j) := by
      intro j y hy
      have e : (g0 ≫ (snd (Over.mk x) Xo.univ.t.G).left) y ∈ Xo.univ.t.PP.L.U j := by
        rw [g0F]
        exact hy
      show g0.base y ∈ (⋂ k : Fin 1, ((snd (Over.mk x) Xo.univ.t.G).left.base ⁻¹' (Xo.univ.t.PP.L.U j : Set _)))
      exact Set.mem_iInter.2 fun _ => e
    have mm : ∀ (y : t'.G.left) j, m1.φ y ∈ Xo.univ.t.PP.L.U j → g0 y ∈ (PPx x).U (fun _ => j) :=
      fun y j hj => hle j hj
    have hσ : ∀ (y : t'.G.left) (j j' : Xo.univ.t.PP.L.ι), m1.φ y ∈ Xo.univ.t.PP.L.U j →
        m1.φ y ∈ Xo.univ.t.PP.L.U j' →
        gs (𝟙 _) y _ ((g0.appLE _ _ (hle j)).hom (s''.f (fun _ => j))) =
          (gm m1.φ y (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j')).val *
            gs (𝟙 _) y _ ((g0.appLE _ _ (hle j')).hom (s''.f (fun _ => j'))) := by
      intro y j j' hj hj'
      have e1 := gs_appLE g0 _ _ (hle j) (𝟙 _) y (show y ∈ m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j from hj) (s''.f (fun _ => j))
      have e2 := gs_appLE g0 _ _ (hle j') (𝟙 _) y (show y ∈ m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j' from hj')
        (s''.f (fun _ => j'))
      have e3 := gs_compat s'' g0 y (mm y j hj) (mm y j' hj')
      have e4 := gm_linComb Xo.univ.t.PP.L (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left) (fun _ => (1 : ℤ))
        g0 y (fun _ => j) (fun _ => j') (mm y j hj) (mm y j' hj')
      simp only [Fin.prod_univ_one, zpow_one, g0F] at e4
      rw [e1, e2, Category.id_comp, e3]
      erw [e4]
    obtain ⟨σ'', hσ''⟩ := sec_down hPG Xo.univ.t.PP.isLB t'.PP.isLB
      (fun j => (g0.appLE _ _ (hle j)).hom (s''.f (fun _ => j))) hσ
    obtain ⟨a, ha, hau⟩ := hgen σ''
    refine ⟨a, fun i => ?_, fun b hb => hau b ?_⟩
    · obtain ⟨j, rfl⟩ : ∃ j, i = fun _ => j := ⟨i 0, funext fun k => congrArg i (Subsingleton.elim _ _)⟩
      refine fn_ext fun y hy => ?_
      obtain ⟨k, hk⟩ : ∃ k, h y ∈ t'.PP.L.U k := by
        have : h y ∈ ⨆ i, t'.PP.L.U i := by
          rw [t'.PP.isLB.cover]
          trivial
        exact TopologicalSpace.Opens.mem_iSup.1 this
      have hF' : m1.φ (h y) ∈ Xo.univ.t.PP.L.U j := by
        have e : (h ≫ m1.φ) y ∈ Xo.univ.t.PP.L.U j := by
          rw [hF]
          exact LB.wchart_le Xo.univ.t.PP.L (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left) (fun _ => j) 0 hy
        exact e
      have eR1 : gs (𝟙 _) y _ (scal x a (fun _ => j)) = cst (fst (Over.mk x) Xo.univ.t.G).left y a := by
        have := gs_constFn (fst (Over.mk x) Xo.univ.t.G).left ((PPx x).U (fun _ => j)) (𝟙 _) y hy a
        rw [Category.id_comp] at this
        exact this
      have eR2 : gs (𝟙 _) y ((PPx x).U (fun _ => j)) ((thfPull1 Xo.univ.t.PP.L h hF s1).f (fun _ => j)) =
          (gw w1 h y j k).val * gs h y _ (σ'.f k) := by
        have := gs_appLE h _ _ (chart_le_pullback_open Xo.univ.t.PP.L h hF (fun _ => j)) (𝟙 _) y hy (s1.f (fun _ => j))
        rw [Category.id_comp] at this
        exact this.trans (hs1 _ h y (fun _ => j) k (mem_pull.2 hF') hk)
      have eL : gs (𝟙 _) y _ (s''.f (fun _ => j)) =
          (gw w1 h y j k).val * (cst (fst (Over.mk x) Xo.univ.t.G).left y a * gs h y _ (σ'.f k)) := by
        have e5 := gs_appLE g0 _ _ (hle j) h y (show h y ∈ m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j from hF') (s''.f (fun _ => j))
        rw [hhg] at e5
        rw [← e5, hσ'' _ h y j k hF' hk, ha k, gs_mul h y _ hk, gs_constFn t'.G.hom _ h y hk a, hS]
      rw [gs_mul (𝟙 _) y _ hy, eR1, eR2, eL, mul_left_comm]
    · intro k
      refine fn_ext fun y hy => ?_
      obtain ⟨j, hj⟩ : ∃ j, m1.φ y ∈ Xo.univ.t.PP.L.U j := by
        have : m1.φ y ∈ ⨆ i, Xo.univ.t.PP.L.U i := by
          rw [Xo.univ.t.PP.isLB.cover]
          trivial
        exact TopologicalSpace.Opens.mem_iSup.1 this
      have e1 := hσ'' _ (𝟙 _) y j k hj hy
      have c1 : gs g0 y _ (scal x b (fun _ => j)) = cst t'.G.hom y b := by
        have := gs_constFn (fst (Over.mk x) Xo.univ.t.G).left ((PPx x).U (fun _ => j)) g0 y (mm y j hj) b
        rw [g0S] at this
        exact this
      have c2 : gs g0 y ((PPx x).U (fun _ => j)) ((thfPull1 Xo.univ.t.PP.L h hF s1).f (fun _ => j)) =
          gs (𝟙 _) y _ (s1.f (fun _ => j)) := by
        have := gs_appLE h _ _ (chart_le_pullback_open Xo.univ.t.PP.L h hF (fun _ => j)) g0 y (mm y j hj) (s1.f (fun _ => j))
        rw [hgh0] at this
        exact this
      have e2 : gs (𝟙 _) y _ ((g0.appLE _ _ (hle j)).hom (s''.f (fun _ => j))) =
          cst t'.G.hom y b * ((gw w1 (𝟙 _) y j k).val * gs (𝟙 _) y _ (σ'.f k)) := by
        rw [gs_appLE g0 _ _ (hle j) (𝟙 _) y (show y ∈ m1.φ ⁻¹ᵁ Xo.univ.t.PP.L.U j from hj), Category.id_comp,
          hb (fun _ => j), gs_mul g0 y _ (mm y j hj), c1, c2, hs1 _ (𝟙 _) y (fun _ => j) k (mem_pull.2 hj) hy]
      have e3 := e1.symm.trans e2
      rw [mul_left_comm] at e3
      rw [gs_mul (𝟙 _) y _ hy, gs_constFn t'.G.hom _ (𝟙 _) y hy b, Category.id_comp]
      exact (Units.mul_right_inj (gw w1 (𝟙 _) y j k)).1 e3

theorem pull_sec {R S : Type} [CommRing R] [CommRing S] (G : SAB H (Sp R)) (t' : SAB H (Sp S)) {f : Sp S ⟶ Sp R}
    (m2 : SABMap t' G f) (θ : LB.Sec G.PP.L) :
    ∃ (w2 : LB.Iso t'.PP.L (G.PP.L.pull m2.φ)) (σ' : LB.Sec t'.PP.L),
      RigIso m2 w2 ∧ IsoMaps w2 σ' (thfPull G.PP.L m2.φ θ) := by
  obtain ⟨w2, hgen, hrig, -⟩ := m2.lin
  obtain ⟨σ', hσ'⟩ := sec_pull_down ((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGen_iff w2).1 hgen) G.PP.isLB t'.PP.isLB θ
  refine ⟨w2, σ', ⟨hgen, hrig⟩, fun i k => fn_ext fun y hy => ?_⟩
  have h1 : m2.φ y ∈ G.PP.L.U (i PUnit.unit) := mem_pull.1 hy.1
  have key := hσ' _ (𝟙 _) y (i PUnit.unit) k h1 hy.2
  have hl : gs (𝟙 _) y _ ((thfPull G.PP.L m2.φ θ).f i) = gs (𝟙 _ ≫ m2.φ) y _ (θ.f (i PUnit.unit)) :=
    gs_appLE m2.φ _ _ _ (𝟙 _) y hy.1 _
  rw [gs_res (𝟙 _) y _ hy, hl, key, gs_mul (𝟙 _) y _ hy, gs_res (𝟙 _) y _ hy]
  congr 1
  exact (gs_unit (𝟙 _) y _ hy (w2.s (i, k))).symm

end Formalism.L2.Pj
