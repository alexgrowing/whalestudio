import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenLevel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

lemma appLE_res {X Y : Scheme.{0}} (i0 : X ⟶ Y) {V1 W : Y.Opens} {V0 : X.Opens} (hV : V0 ≤ i0 ⁻¹ᵁ V1)
    (h1 : V1 ≤ W) (h0 : V0 ≤ i0 ⁻¹ᵁ W) (y : Γ(Y, W)) :
    (i0.appLE V1 V0 hV) ((Y.presheaf.map (homOfLE h1).op).hom y) =
      (X.presheaf.map (homOfLE h0).op).hom ((i0.app W).hom y) := by
  have e1 := i0.map_appLE hV (homOfLE h1).op
  have e2 : i0.app W ≫ X.presheaf.map (homOfLE h0).op = i0.appLE W V0 h0 := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  calc (i0.appLE V1 V0 hV) ((Y.presheaf.map (homOfLE h1).op).hom y)
      = (Y.presheaf.map (homOfLE h1).op ≫ i0.appLE V1 V0 hV).hom y := rfl
    _ = (i0.appLE W V0 h0).hom y := by rw [e1]
    _ = (i0.app W ≫ X.presheaf.map (homOfLE h0).op).hom y := by rw [e2]
    _ = _ := rfl

lemma appLE_pull {X Y Z : Scheme.{0}} (i0 : X ⟶ Y) (m : Y ⟶ Z) (m' : X ⟶ Z) (h : i0 ≫ m = m')
    {V1 : Y.Opens} {V0 : X.Opens} (hV : V0 ≤ i0 ⁻¹ᵁ V1) {W : Z.Opens} (h1 : V1 ≤ m ⁻¹ᵁ W)
    (h0 : V0 ≤ m' ⁻¹ᵁ W) (x : Γ(Z, W)) :
    (i0.appLE V1 V0 hV) ((Y.presheaf.map (homOfLE h1).op).hom ((m.app W).hom x)) =
      (X.presheaf.map (homOfLE h0).op).hom ((m'.app W).hom x) := by
  subst h
  have e1 : m.app W ≫ Y.presheaf.map (homOfLE h1).op = m.appLE W V1 h1 := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  have e2 : (i0 ≫ m).app W ≫ X.presheaf.map (homOfLE h0).op = (i0 ≫ m).appLE W V0 h0 := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  calc (i0.appLE V1 V0 hV) ((Y.presheaf.map (homOfLE h1).op).hom ((m.app W).hom x))
      = ((m.app W ≫ Y.presheaf.map (homOfLE h1).op) ≫ i0.appLE V1 V0 hV).hom x := rfl
    _ = ((i0 ≫ m).appLE W V0 h0).hom x := by rw [e1, Scheme.Hom.appLE_comp_appLE]
    _ = ((i0 ≫ m).app W ≫ X.presheaf.map (homOfLE h0).op).hom x := by rw [e2]
    _ = _ := rfl

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def expL (U : UnifPre I D A G) (e : ℕ) (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι))
    (j₁ : Fin 1 → U.LG.L.ι) (S : Finset D.toPre.X) (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι)
    (σ : H0 U.LG.L 1) : Γ((thickObj R I e G).left, U.expW e p j₁ S jf jt) :=
  (res (inf_le_left.trans inf_le_left :
      U.expW e p j₁ S jf jt ≤ (LB.div (D.toPre.P.L.pull (U.gt e).pG.left)
        (U.LG.L.pull (fstG I e G).left)).U p) ((U.w e).s p)).val ^ 1 *
    ((thickObj R I e G).left.presheaf.map (homOfLE (inf_le_left.trans inf_le_right :
      U.expW e p j₁ S jf jt ≤
        (fstG I e G).left ⁻¹ᵁ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁)).op).hom
      (((fstG I e G).left.app _).hom (σ.f j₁))

def expR (U : UnifPre I D A G) (e : ℕ) (p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι))
    (j₁ : Fin 1 → U.LG.L.ι) (S : Finset D.toPre.X) (jf jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι)
    (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α) : Γ((thickObj R I e G).left, U.expW e p j₁ S jf jt) :=
  ∑ α ∈ S.attach,
    ((thickObj R I e G).left.presheaf.map (homOfLE (U.expW_le_f e p j₁ jf jt α.2)).op).hom
        (((U.gt e).pG.left.app _).hom ((f α.1).f (jf α.1))) *
      (res (U.expWeight_le_chart_weight e p j₁ jf jt α.2) (((U.gt e).t α.1).s (jt α.1))).val

set_option maxHeartbeats 1000000 in

theorem expandsAt_of_div (U : UnifPre I D A G) [Flat G.hom] {ϖ : R} (hϖ : ϖ ≠ 0) (hI : I = Ideal.span {ϖ})
    (σ τ : H0 U.LG.L 1) (hστ : ∀ j, σ.f j = toW G.hom _ ϖ * τ.f j)
    (f g : ∀ α, D.toPre.SecB 1 α) (hfg : ∀ α j, (f α).f j = toW D.toPre.P.A.hom _ ϖ * (g α).f j)
    (e : ℕ) (h : U.ExpandsAt (e + 1) 1 σ f) : U.ExpandsAt e 1 τ g := by
  classical
  obtain ⟨S, hout, hmain⟩ := h
  have hι : thickMap R I e G ≫ pullback.fst G.hom (thick R I (e + 1)) = pullback.fst G.hom (thick R I e) :=
    thickMap_fst e
  have hq : thickMap R I e G ≫ (U.gt (e + 1)).pG.left = (U.gt e).pG.left := U.gt_q e
  have hJ1 : I ^ (e + 1 + 1) ≤ Ideal.span {ϖ ^ (e + 2)} := by
    rw [hI, Ideal.span_singleton_pow]
  have hJ2 : ϖ ^ (e + 1) ∈ I ^ (e + 1) := by
    rw [hI, Ideal.span_singleton_pow]; exact Ideal.subset_span rfl
  have van : ∀ (V : (thickObj R I (e + 1) G).left.Opens) (y : Γ((thickObj R I (e + 1) G).left, V)),
      toW (X := (thickObj R I (e + 1) G).left) ((fstG I (e + 1) G).left ≫ G.hom) V ϖ * y = 0 →
        (thickMap R I e G).app V y = 0 :=
    fun V y hy => vanish_of_mul G.hom hϖ e hJ1 hJ2 (thickMap R I e G) hι V y hy
  refine ⟨S, fun α hα j => ?_, fun p j₁ jf jt hj hcoh => ?_⟩
  · have h1 := hout α hα j
    erw [hfg α j, map_mul, app_toW, toW_congr (pG_struct _)] at h1
    exact app_eq_zero_of_comp hq _ _ (van _ _ h1)
  ·
    have hfam : ∀ z, (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2))) z =
        thickMap R I e G ≫ (Sum.elim (fun _ : PUnit.{1} => (U.gt (e + 1)).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt (e + 1)).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt (e + 1)).pG a.1.1 a.2))) z := by
      rintro (z | z | z)
      · exact hq.symm
      · show (U.gt e).pG.left ≫ D.toPre.famφB z.1.1 z.2 =
          thickMap R I e G ≫ (U.gt (e + 1)).pG.left ≫ D.toPre.famφB z.1.1 z.2
        rw [← Category.assoc, hq]
      · exact (Oφ_thick U e z.1.1 z.2).symm
    have hcoh1 := fun a b (hab : (Sum.elim (fun _ : PUnit.{1} => (U.gt (e + 1)).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt (e + 1)).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt (e + 1)).pG a.1.1 a.2))) a =
        (Sum.elim (fun _ : PUnit.{1} => (U.gt (e + 1)).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt (e + 1)).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt (e + 1)).pG a.1.1 a.2))) b) =>
      hcoh a b (by rw [hfam a, hfam b, hab])
    have E := hmain p j₁ jf jt hj hcoh1
    have E' : expL U (e + 1) p j₁ S jf jt σ = expR U (e + 1) p j₁ S jf jt f := E
    show expL U e p j₁ S jf jt τ = expR U e p j₁ S jf jt g

    have hι' : thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left := thickMap_fst e
    have hV : U.expW e p j₁ S jf jt ≤ thickMap R I e G ⁻¹ᵁ U.expW (e + 1) p j₁ S jf jt := by
      intro x hx
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hx
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · exact wchart_le_preimage D.toPre.P.L (thickMap R I e G) (fun _ => (U.gt (e + 1)).pG.left)
          (fun _ => (U.gt e).pG.left) (fun _ => hq.symm) p.1 h1
      · exact wchart_le_preimage U.LG.L (thickMap R I e G) (fun _ => (fstG I (e + 1) G).left)
          (fun _ => (fstG I e G).left) (fun _ => hι'.symm) p.2 h2
      · show (fstG I (e + 1) G).left.base ((thickMap R I e G).base x) ∈
          LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j₁
        rw [← Scheme.Hom.comp_apply, hι']; exact h3
      · refine WeightPf.mem_finset_inf _ _ _ fun α hα => ?_
        have hx' := WeightPf.mem_of_finset_inf h4 hα
        refine ⟨?_, wchart_le_preimage D.toPre.P.L (thickMap R I e G) (D.toPre.Oφ (U.gt (e + 1)).pG α)
          (D.toPre.Oφ (U.gt e).pG α) (fun k => (Oφ_thick U e α k).symm) (jt α) hx'.2⟩
        show (U.gt (e + 1)).pG.left.base ((thickMap R I e G).base x) ∈
          LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α)
        rw [← Scheme.Hom.comp_apply, hq]; exact hx'.1
    set c1 := toW (X := (thickObj R I (e + 1) G).left) ((fstG I (e + 1) G).left ≫ G.hom)
      (U.expW (e + 1) p j₁ S jf jt) ϖ with hc1
    have hL1 : expL U (e + 1) p j₁ S jf jt σ = c1 * expL U (e + 1) p j₁ S jf jt τ := by
      simp only [expL]
      erw [hστ j₁, map_mul, map_mul, app_toW, toW_res]
      ring
    have hR1 : expR U (e + 1) p j₁ S jf jt f = c1 * expR U (e + 1) p j₁ S jf jt g := by
      simp only [expR, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      erw [hfg α.1 (jf α.1), map_mul, map_mul, app_toW, toW_res, toW_congr (pG_struct _)]
      ring
    have hdiff : c1 * (expL U (e + 1) p j₁ S jf jt τ - expR U (e + 1) p j₁ S jf jt g) = 0 := by
      rw [mul_sub, ← hL1, ← hR1, E', sub_self]
    have hvan := van _ _ hdiff
    have hres : (thickMap R I e G).appLE _ _ hV
        (expL U (e + 1) p j₁ S jf jt τ - expR U (e + 1) p j₁ S jf jt g) = 0 := by
      show ((thickMap R I e G).app _ ≫ (thickObj R I e G).left.presheaf.map (homOfLE hV).op).hom _ = 0
      rw [CommRingCat.comp_apply, hvan, map_zero]
    have h0w : U.expW e p j₁ S jf jt ≤ thickMap R I e G ⁻¹ᵁ
        (LB.div (D.toPre.P.L.pull (U.gt (e + 1)).pG.left) (U.LG.L.pull (fstG I (e + 1) G).left)).U p :=
      fun x hx => (inf_le_left.trans inf_le_left :
        U.expW (e + 1) p j₁ S jf jt ≤ (LB.div (D.toPre.P.L.pull (U.gt (e + 1)).pG.left)
          (U.LG.L.pull (fstG I (e + 1) G).left)).U p) (hV hx)
    have hL2 : (thickMap R I e G).appLE _ _ hV (expL U (e + 1) p j₁ S jf jt τ) = expL U e p j₁ S jf jt τ := by
      simp only [expL, map_mul, map_pow]
      congr 1
      · congr 1
        rw [WeightPf.res_val, appLE_res (thickMap R I e G) hV _ h0w]
        exact congrArg Units.val (U.w_compat e p (U.expW e p j₁ S jf jt) h0w (inf_le_left.trans inf_le_left))
      · exact appLE_pull _ _ _ hι' hV _ _ _
    have ht : ∀ α : S, (thickMap R I e G).appLE _ _ hV
        (res (U.expWeight_le_chart_weight (e + 1) p j₁ jf jt α.2) (((U.gt (e + 1)).t α.1).s (jt α.1))).val =
        (res (U.expWeight_le_chart_weight e p j₁ jf jt α.2) (((U.gt e).t α.1).s (jt α.1))).val := by
      intro α
      have hfun : (fun k => thickMap R I e G ≫ D.toPre.Oφ (U.gt (e + 1)).pG α.1 k) =
          D.toPre.Oφ (U.gt e).pG α.1 := funext (Oφ_thick U e α.1)
      have hW : U.expW e p j₁ S jf jt ≤
          LB.wchart D.toPre.P.L (fun k => thickMap R I e G ≫ D.toPre.Oφ (U.gt (e + 1)).pG α.1 k) (jt α.1) := by
        rw [hfun]; exact U.expWeight_le_chart_weight e p j₁ jf jt α.2
      have hcohE : ∀ k1 k2, D.toPre.Oφ (U.gt e).pG α.1 k1 = D.toPre.Oφ (U.gt e).pG α.1 k2 →
          jt α.1 k1 = jt α.1 k2 :=
        fun k1 k2 h => hcoh (Sum.inr (Sum.inr (α, k1))) (Sum.inr (Sum.inr (α, k2))) h
      have C2 := LBVal.corr_val D.toPre.P.L _ _ _ _ _ _ (U.gt_t e α.1) (jt α.1) (jt α.1)
        (fun k1 k2 h => hcohE k1 k2 ((Oφ_thick U e α.1 k1).symm.trans (h.trans (Oφ_thick U e α.1 k2)))) hcohE
        (fun k k' h => hcohE k k' ((Oφ_thick U e α.1 k).symm.trans h)) (U.expW e p j₁ S jf jt)
        (le_inf hW (U.expWeight_le_chart_weight e p j₁ jf jt α.2))
      show ((thickObj R I (e + 1) G).left.presheaf.map (homOfLE (U.expWeight_le_chart_weight (e + 1) p j₁ jf jt α.2)).op ≫
          (thickMap R I e G).appLE _ _ hV).hom (((U.gt (e + 1)).t α.1).s (jt α.1)).val =
        ((thickObj R I e G).left.presheaf.map (homOfLE (U.expWeight_le_chart_weight e p j₁ jf jt α.2)).op).hom
          (((U.gt e).t α.1).s (jt α.1)).val
      erw [Scheme.Hom.map_appLE]
      rw [← LBVal.pullGen_val (L := D.toPre.P.L) _ _ ((U.gt (e + 1)).t α.1) (thickMap R I e G) (jt α.1) _ hW]
      exact C2
    have hR2 : (thickMap R I e G).appLE _ _ hV (expR U (e + 1) p j₁ S jf jt g) = expR U e p j₁ S jf jt g := by
      simp only [expR, map_sum, map_mul]
      refine Finset.sum_congr rfl fun α _ => ?_
      congr 1
      · exact appLE_pull _ _ _ hq hV _ _ _
      · exact ht α
    rw [map_sub, hL2, hR2, sub_eq_zero] at hres
    exact hres

end ReciprocityTheory.ChartRestriction.G.DVR.TG

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

lemma flat_G (U : UnifPre I D A G) : Flat G.hom := by
  haveI := U.smooth
  exact AlgebraicGeometry.instFlatOfSmooth _

lemma flat_B : Flat D.toPre.P.A.hom := by
  haveI := D.toPre.P.smoothDim
  haveI : AlgebraicGeometry.Smooth D.toPre.P.A.hom :=
    AlgebraicGeometry.SmoothOfRelativeDimension.smooth D.toPre.P.g _
  exact AlgebraicGeometry.instFlatOfSmooth _

theorem expandsAt_scale (U : UnifPre I D A G) (c : R) (τ τ' : H0 U.LG.L 1)
    (hτ : ∀ j, τ'.f j = toW G.hom _ c * τ.f j)
    (g g' : ∀ α, D.toPre.SecB 1 α) (hg : ∀ α j, (g' α).f j = toW D.toPre.P.A.hom _ c * (g α).f j)
    (e : ℕ) (h : U.ExpandsAt e 1 τ g) : U.ExpandsAt e 1 τ' g' := by
  obtain ⟨S, hout, hmain⟩ := h
  refine ⟨S, fun α hα j => ?_, fun p j₁ jf jt hj hcoh => ?_⟩
  · erw [hg α j, map_mul, hout α hα j, mul_zero]
  · have E : expL U e p j₁ S jf jt τ = expR U e p j₁ S jf jt g := hmain p j₁ jf jt hj hcoh
    show expL U e p j₁ S jf jt τ' = expR U e p j₁ S jf jt g'
    set c1 := toW (X := (thickObj R I e G).left) ((fstG I e G).left ≫ G.hom) (U.expW e p j₁ S jf jt) c
    have hL : expL U e p j₁ S jf jt τ' = c1 * expL U e p j₁ S jf jt τ := by
      simp only [expL]
      erw [hτ j₁, map_mul, map_mul, app_toW, toW_res]
      ring
    have hR : expR U e p j₁ S jf jt g' = c1 * expR U e p j₁ S jf jt g := by
      simp only [expR, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      erw [hg α.1 (jf α.1), map_mul, map_mul, app_toW, toW_res, toW_congr (pG_struct _)]
      ring
    rw [hL, hR, E]

theorem expand_div_one (U : UnifPre I D A G) (hWI : WeightIndepSt) {ϖ : R} (hϖ : ϖ ≠ 0)
    (hI : I = Ideal.span {ϖ}) (σ τ : H0 U.LG.L 1) (hστ : ∀ j, σ.f j = toW G.hom _ ϖ * τ.f j)
    (f : ∀ α, D.toPre.SecB 1 α) (hf : ∀ e, U.ExpandsAt e 1 σ f) :
    ∃ g : ∀ α, D.toPre.SecB 1 α, (∀ α j, (f α).f j = toW D.toPre.P.A.hom _ ϖ * (g α).f j) ∧
      ∀ e, U.ExpandsAt e 1 τ g := by
  have := flat_G U
  have := flat_B (D := D)
  have hϖI : ϖ ∈ I ^ (0 + 1) := by rw [hI, zero_add, pow_one]; exact Ideal.mem_span_singleton_self ϖ
  have hσ0 : ∀ j, ((fstG I 0 G).left.app _).hom (σ.f j) = 0 := by
    intro j
    rw [hστ, map_mul]
    erw [app_toW_of_mem G.hom (I ^ (0 + 1)) _ hϖI, zero_mul]
  have hpG := hWI R I D A G U 0 1 σ f hσ0 (hf 0)
  have hB : ∀ α j, (pullback.fst D.toPre.P.A.hom (thick R I 0)).app _ ((f α).f j) = 0 := by
    intro α j
    have := (U.gt 0).q_flat
    have := (U.gt 0).q_surj
    apply app_injective_of_flat_surj (U.gt 0).q.left
    rw [map_zero]
    have h := hpG α j
    have e : (U.gt 0).pG.left = (U.gt 0).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R I 0) := rfl
    rw [e, Scheme.Hom.comp_app] at h
    exact h
  choose g hg using fun α => sec_div D.toPre.P.A.hom (f α) hϖ (J := I ^ (0 + 1))
    (by rw [hI, zero_add, pow_one]) (hB α)
  exact ⟨g, hg, fun e => expandsAt_of_div U hϖ hI σ τ hστ f g hg e (hf (e + 1))⟩

theorem expand_div_pow (U : UnifPre I D A G) (hWI : WeightIndepSt) {ϖ : R} (hϖ : ϖ ≠ 0)
    (hI : I = Ideal.span {ϖ}) (n : ℕ) : ∀ (σ τ : H0 U.LG.L 1), (∀ j, σ.f j = toW G.hom _ (ϖ ^ n) * τ.f j) →
    ∀ (f : ∀ α, D.toPre.SecB 1 α), (∀ e, U.ExpandsAt e 1 σ f) →
    ∃ g : ∀ α, D.toPre.SecB 1 α, (∀ α j, (f α).f j = toW D.toPre.P.A.hom _ (ϖ ^ n) * (g α).f j) ∧
      ∀ e, U.ExpandsAt e 1 τ g := by
  induction n with
  | zero =>
    intro σ τ hστ f hf
    refine ⟨f, fun α j => by rw [pow_zero, map_one, _root_.one_mul], fun e => ?_⟩
    have : σ = τ := SecOps.sec_ext fun j => by rw [hστ, pow_zero, map_one, _root_.one_mul]
    rw [← this]; exact hf e
  | succ n ih =>
    intro σ τ hστ f hf
    let σ' : H0 U.LG.L 1 := SecOps.secScale (scal G.hom (ϖ ^ n)) τ
    have h1 : ∀ j, σ.f j = toW G.hom _ ϖ * σ'.f j := fun j => by
      rw [hστ]
      show _ = _ * (toW G.hom _ (ϖ ^ n) * τ.f j)
      rw [pow_succ', map_mul, _root_.mul_assoc]
    obtain ⟨g1, hg1, he1⟩ := expand_div_one U hWI hϖ hI σ σ' h1 f hf
    obtain ⟨g, hg, he⟩ := ih σ' τ (fun j => rfl) g1 he1
    refine ⟨g, fun α j => ?_, he⟩
    rw [hg1, hg, pow_succ', map_mul, _root_.mul_assoc]

end ReciprocityTheory.ChartRestriction.G.DVR.TG
