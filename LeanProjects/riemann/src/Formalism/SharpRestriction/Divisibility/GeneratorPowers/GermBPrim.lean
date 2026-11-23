import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBSer

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GermB

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun

attribute [local instance] Over.cartesianMonoidalCategory

section Base

variable {X : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]

def divLinB (φ : K → (X ⟶ X)) (ε : K → ℤ) (w : LB.Gen (LB.div (LB.LinComb L φ ε) L)) :
    LB.Gen (LB.LinComb L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) (Sum.elim (fun _ => 1) fun k => -ε k)) :=
  ⟨fun j => res (fun _ hy => ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k),
      Set.mem_iInter.1 hy (Sum.inl 0)⟩ :
    LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) j ≤ (LB.div (LB.LinComb L φ ε) L).U (j ∘ Sum.inr, j (Sum.inl 0)))
    (w.s (j ∘ Sum.inr, j (Sum.inl 0)))⁻¹⟩

theorem divLinB_isGen (φ : K → (X ⟶ X)) (ε : K → ℤ) (w : LB.Gen (LB.div (LB.LinComb L φ ε) L)) (hw : w.IsGen) :
    (divLinB L φ ε w).IsGen := fun i j => unit_ext fun y hy => by
  have le : ∀ j : Fin 1 ⊕ K → L.ι, LB.wchart L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) j ≤
      (LB.div (LB.LinComb L φ ε) L).U (j ∘ Sum.inr, j (Sum.inl 0)) := fun _ _ hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (Sum.inr k), Set.mem_iInter.1 hy (Sum.inl 0)⟩
  have hi := le i hy.1
  have hj := le j hy.2
  have hij : (𝟙 X : X ⟶ X) y ∈ (LB.div (LB.LinComb L φ ε) L).U (i ∘ Sum.inr, i (Sum.inl 0)) ⊓
      (LB.div (LB.LinComb L φ ε) L).U (j ∘ Sum.inr, j (Sum.inl 0)) := ⟨hi, hj⟩
  have hw' := (gm_res (𝟙 X) y _ hij _).symm.trans ((congrArg (gm (𝟙 X) y _) (hw (i ∘ Sum.inr, i (Sum.inl 0))
    (j ∘ Sum.inr, j (Sum.inl 0)))).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res (𝟙 X) y _ hij _))))
  have hg : gm (𝟙 X) y _ ((LB.div (LB.LinComb L φ ε) L).g (i ∘ Sum.inr, i (Sum.inl 0)) (j ∘ Sum.inr, j (Sum.inl 0))) =
      (gm (𝟙 X) y _ ((LB.LinComb L (Sum.elim (fun _ : Fin 1 => 𝟙 X) φ) (Sum.elim (fun _ => 1) fun k => -ε k)).g i j))⁻¹ := by
    refine (map_mul _ _ _).trans ?_
    refine Eq.trans (congrArg₂ (· * ·) ((gm_res _ y _ hij _).trans (gm_linComb L φ ε (𝟙 _) y _ _ hi.1 hj.1))
      ((map_inv _ _).trans (congrArg _ (gm_res _ y _ hij _)))) ?_
    refine Eq.trans ?_ (congrArg _ (gm_linComb L _ _ (𝟙 _) y i j hy.1 hy.2)).symm
    rw [Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, Fin.prod_univ_one, zpow_one,
      Category.comp_id, Category.id_comp, mul_inv_rev, inv_inv]
    rfl
  refine (gm_res _ y _ hy _).trans ((gm_res _ y _ hy.1 _).trans ((map_inv _ _).trans ?_))
  refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ((gm_res _ y _ hy _).trans
    ((gm_res _ y _ hy.2 _).trans (map_inv _ _))))).symm
  exact (congrArg (·⁻¹) (hw'.trans (congrArg (· * _) hg))).trans
    (by simp only [mul_inv_rev, inv_inv]; exact _root_.mul_comm _ _)

end Base

section Tools

theorem prod_cube3 {X0 : Scheme.{0}} (G : Over X0) [GrpObj G] [IsCommMonObj G] {T : Over X0} {M : Type} [CommGroup M]
    (h : (T ⟶ G) → M) (xs : Fin 3 → (T ⟶ G)) :
    ∏ I : thK, h (psum G xs I.down) ^ thε I =
      (h 1)⁻¹ * h (xs 0 * 1) * h (xs 1 * 1) * h (xs 2 * 1) * (h (xs 0 * (xs 1 * 1)))⁻¹ * (h (xs 0 * (xs 2 * 1)))⁻¹ *
        (h (xs 1 * (xs 2 * 1)))⁻¹ * h (xs 0 * (xs 1 * (xs 2 * 1))) := by
  refine (Fintype.prod_equiv (Equiv.ulift : thK ≃ Finset (Fin 3)) _
    (fun I : Finset (Fin 3) => h (psum G xs I) ^ thε ⟨I⟩) (fun _ => rfl)).trans ?_
  have hu : (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  rw [hu, Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  have c0 : thε (⟨∅⟩ : thK) = -1 := rfl
  have c1 : thε (⟨{0}⟩ : thK) = 1 := rfl
  have c2 : thε (⟨{1}⟩ : thK) = 1 := rfl
  have c3 : thε (⟨{2}⟩ : thK) = 1 := rfl
  have c4 : thε (⟨{0, 1}⟩ : thK) = -1 := rfl
  have c5 : thε (⟨{0, 2}⟩ : thK) = -1 := rfl
  have c6 : thε (⟨{1, 2}⟩ : thK) = -1 := rfl
  have c7 : thε (⟨{0, 1, 2}⟩ : thK) = 1 := rfl
  have p0 : psum G xs ∅ = 1 := rfl
  have p1 : psum G xs {0} = xs 0 * 1 := rfl
  have p2 : psum G xs {1} = xs 1 * 1 := rfl
  have p3 : psum G xs {2} = xs 2 * 1 := rfl
  have p4 : psum G xs {0, 1} = xs 0 * (xs 1 * 1) := rfl
  have p5 : psum G xs {0, 2} = xs 0 * (xs 2 * 1) := rfl
  have p6 : psum G xs {1, 2} = xs 1 * (xs 2 * 1) := rfl
  have p7 : psum G xs {0, 1, 2} = xs 0 * (xs 1 * (xs 2 * 1)) := rfl
  rw [c0, c1, c2, c3, c4, c5, c6, c7, p0, p1, p2, p3, p4, p5, p6, p7]
  simp only [zpow_one, zpow_neg, _root_.mul_assoc]

theorem eta_one {X0 : Scheme.{0}} (G : Over X0) [GrpObj G] : (η[G] : 𝟙_ (Over X0) ⟶ G) = 1 := by
  show η[G] = toUnit _ ≫ η[G]
  rw [toUnit_unique (toUnit (𝟙_ (Over X0))) (𝟙 _), Category.id_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

theorem scale_isGen {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (u : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (hg : g.IsGen) : (scaleGenG t φ ε u g).IsGen := fun i j =>
  unit_ext fun y hy => by
    have e := (gm_res (𝟙 Y) y _ hy _).symm.trans ((congrArg (gm (𝟙 Y) y _) (hg i j)).trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) rfl (gm_res (𝟙 Y) y _ hy _))))
    refine (gm_res _ y _ hy _).trans ((map_mul _ _ _).trans ?_)
    refine Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl ((gm_res _ y _ hy _).trans (map_mul _ _ _)))).symm
    refine (congrArg₂ (· * ·) (gm_res _ y le_top hy.1 u) e).trans ?_
    refine Eq.trans ?_ (congrArg₂ (· * ·) rfl (congrArg₂ (· * ·) (gm_res _ y le_top hy.2 u).symm rfl))
    exact _root_.mul_left_comm _ _ _

theorem val_rigT {S0 : Scheme.{0}} (A : Over S0) [GrpObj A] (L : LB A.left) (rig : LB.Gen (L.pull (eSec A)))
    (T : Over S0) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) (J : (Z ⟶ A.left) → L.ι) (hJ : Good L z J) :
    val (rigT A L rig T 1) r z J = val rig (r ≫ T.hom) z J := by
  rw [val_of rig (r ≫ T.hom) z J (fun _ => J (r ≫ T.hom ≫ eSec A)) (fun _ => by rw [Category.assoc])]
  have hm := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) r
  refine (map_zpow _ _ _).trans ((zpow_one _).trans ((gm_res r z _ hm _).trans ?_))
  exact gm_pull r T.hom z _ (show T.hom (r z) ∈ LB.wchart L (fun _ : PUnit => eSec A) (fun _ => J (r ≫ T.hom ≫ eSec A)) from
    Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hm 0) _

end Tools

section Prim

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

abbrev zz : 𝟙_ (Over X0) ⟶ t.G ⊗ t.G := lift (η[t.G] : 𝟙_ (Over X0) ⟶ t.G) (η[t.G] : 𝟙_ (Over X0) ⟶ t.G)

theorem cube_one_left {T : Over X0} {M : Type} [CommGroup M] (h : (T ⟶ t.G) → M) (b : T ⟶ t.G) :
    ∏ I : ULift (Finset (Fin 2)), h (psum t.G ![1, b] I.down) ^ cε 2 I = 1 := by
  rw [prod_cube2]
  simp

theorem cube_one_right {T : Over X0} {M : Type} [CommGroup M] (h : (T ⟶ t.G) → M) (b : T ⟶ t.G) :
    ∏ I : ULift (Finset (Fin 2)), h (psum t.G ![b, 1] I.down) ^ cε 2 I = 1 := by
  rw [prod_cube2]
  simp

theorem exists_wP : ∃ wP : PrimTyG t, IsPrimG t wP := by
  have hL := t.PP.isLB
  obtain ⟨w, hw⟩ := t.prim
  let w1 : PrimTyG t := divLinB t.PP.L _ _ w
  have hw1 : w1.IsGen := divLinB_isGen t.PP.L _ _ w hw
  have hpt : ∀ I : ULift.{0} (Finset (Fin 2)), eSec t.G ≫ cφG t ![𝟙 t.G, t.act.act H.w0] I =
      (psum t.G ![1, η[t.G] ≫ t.act.act H.w0] I.down).left := by
    intro I
    simp only [cφG, eSec, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · exact (Category.comp_id _).trans (eta_one t.G)
    · rfl
  obtain ⟨u, hu⟩ := exists_ratio t.PP.L hL (φ' := fun _ : PUnit => eSec t.G) (ε' := fun _ => 1)
    (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, zpow_neg, Finset.prod_inv_distrib,
        hpt, Fintype.prod_unique]
      rw [cube_one_left t (fun p => h p.left), inv_one, _root_.mul_one])
    (LB.pullGen t.PP.L _ _ w1 (eSec t.G)) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hw1 _) t.PP.rig t.PP.rigGen
  have hes : eSec t.G ≫ t.G.hom = 𝟙 _ := Over.w η[t.G]
  refine ⟨scaleGenG t _ _ (pullU t.G.hom ⊤ u⁻¹) w1, scale_isGen t _ _ _ w1 hw1, corr_of_val hL fun y J hJ => ?_⟩
  refine (val_pull hJ _ _ _).trans ((val_scale t _ _ _ _ _ y J hJ).trans ?_)
  refine (congrArg₂ (· * ·) ((gm_pull (𝟙 _ ≫ eSec t.G) t.G.hom y ⊤ trivial u⁻¹).trans
    (congrArg (fun r => gm r y ⊤ u⁻¹) (by rw [Category.assoc, hes, Category.comp_id])))
    ((val_pull hJ w1 _ _).symm.trans (hu _ (𝟙 _) y J hJ))).trans ?_
  rw [map_inv, inv_mul_cancel_left]

theorem exists_wL (a : 𝓞 E) : ∃ wL : LB.Gen (LB.LinComb t.PP.L
      (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]))
      (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over X0)).left) (z : Z) (J : (Z ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J →
      val wL (r ≫ (zz t).left) z J = 1 := by
  have hL := t.PP.isLB
  obtain ⟨w, hw⟩ := t.adj a
  let w2 := divLin t.PP.L (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cε 2)
    (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) (cε 2) w
  have hw2 : w2.IsGen := divLin_isGen t.PP.L _ _ _ _ w hw
  have hp1 : ∀ I : ULift.{0} (Finset (Fin 2)), (zz t).left ≫ cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)] I =
      (psum t.G ![1, η[t.G] ≫ t.act.act (H.bar a)] I.down).left := by
    intro I
    simp only [cφG, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · show zz t ≫ fst t.G t.G = 1
      exact (lift_fst _ _).trans (eta_one t.G)
    · show zz t ≫ (snd t.G t.G ≫ t.act.act (H.bar a)) = η[t.G] ≫ t.act.act (H.bar a)
      exact lift_snd_assoc _ _ _
  have hp2 : ∀ I : ULift.{0} (Finset (Fin 2)), (zz t).left ≫ cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G] I =
      (psum t.G ![η[t.G] ≫ t.act.act a, 1] I.down).left := by
    intro I
    simp only [cφG, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · show zz t ≫ (fst t.G t.G ≫ t.act.act a) = η[t.G] ≫ t.act.act a
      exact lift_fst_assoc _ _ _
    · show zz t ≫ snd t.G t.G = 1
      exact (lift_snd _ _).trans (eta_one t.G)
  obtain ⟨s, -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, hp1, hp2, Fintype.prod_empty]
      rw [cube_one_left t (fun p => h p.left), cube_one_right t (fun p => h p.left), inv_one, _root_.mul_one])
    (LB.pullGen t.PP.L _ _ w2 (zz t).left) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hw2 _)
  have le : (⊤ : ((𝟙_ (Over X0)).left).Opens) ≤ LB.wchart t.PP.L (PEmpty.elim : PEmpty → (_ ⟶ t.G.left)) PEmpty.elim :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  let u := res le (s.s PEmpty.elim)
  have hz : (zz t).left ≫ (t.G ⊗ t.G).hom = 𝟙 _ := Over.w (zz t)
  refine ⟨scaleGenG t _ _ (pullU (t.G ⊗ t.G).hom ⊤ u⁻¹) w2, scale_isGen t _ _ _ w2 hw2, fun Z r z J hJ => ?_⟩
  refine (val_scale t _ _ _ _ _ z J hJ).trans ?_
  have e1 : val w2 (r ≫ (zz t).left) z J = gm r z ⊤ u := by
    refine (val_pull hJ w2 _ _).symm.trans ((hv Z r z J hJ).symm.trans ?_)
    rw [val_of s r z J PEmpty.elim (fun k => k.elim)]
    exact (gm_res r z le trivial _).symm
  refine (congrArg₂ (· * ·) ((gm_pull (r ≫ (zz t).left) (t.G ⊗ t.G).hom z ⊤ trivial u⁻¹).trans
    (congrArg (fun q => gm q z ⊤ u⁻¹) (by rw [Category.assoc, hz, Category.comp_id]))) e1).trans ?_
  rw [map_inv, inv_mul_cancel]

end Prim

end Formalism.MainNotions.ModuliIntegralCharts.H1.GermB
