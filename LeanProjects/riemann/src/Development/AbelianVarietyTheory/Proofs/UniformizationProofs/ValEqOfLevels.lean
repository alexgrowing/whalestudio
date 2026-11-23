import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.MemFinsetInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ESecStruct
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoordLinear

open Geo.Tor

theorem fn_eq_of_levels {R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R]
    (W : (Spec (CommRingCat.of R)).Opens) (hW : W = ⊤) (a b : Γ(Spec (CommRingCat.of R), W))
    (h : ∀ e, ((thick R I e).app W).hom a = ((thick R I e).app W).hom b) : a = b := by
  subst hW
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  have key : ∀ (e : ℕ) (c : Γ(Spec (CommRingCat.of R), ⊤)),
      Ideal.Quotient.mk (I ^ (e + 1)) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) =
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (e + 1)))).hom.hom (((thick R I e).app ⊤).hom c) := fun e c =>
    (congrArg (fun q => q.hom c)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))).symm
  have := IsHausdorff.StrictMono.funext' I (a := fun n => n + 1) (strictMono_id.add_const 1)
    (f := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a)
    (g := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom b)
    (fun n _ => (key n a).trans ((congrArg _ (h n)).trans (key n b).symm))
  exact congrFun this ()

theorem val_eq_of_levels {R : Type} [CommRing R] [IsLocalRing R] (I : Ideal R) [IsHausdorff I R] {X : Scheme.{0}}
    {M : LB X} (hM : M.IsLB) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Spec (CommRingCat.of R) ⟶ X)} {ε : K → ℤ}
    {φ' : K' → (Spec (CommRingCat.of R) ⟶ X)} {ε' : K' → ℤ} (hF : FormEq φ ε φ' ε')
    {u : LB.Gen (LB.LinComb M φ ε)} {u' : LB.Gen (LB.LinComb M φ' ε')} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ e y J, Good M y J → val u (thick R I e) y J = val u' (thick R I e) y J)
    (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (J) (hJ : Good M z J) :
    val u r z J = val u' r z J := by
  obtain ⟨t, ht, hv⟩ := exists_gen hM hF u hu
  choose j hj using fun k => exists_chart hM (φ' k (IsLocalRing.closedPoint R))
  have hW : LB.wchart M φ' j = ⊤ :=
    (IsLocalRing.closedPoint_mem_iff (R := R) (LB.wchart M φ' j)).1 (Set.mem_iInter.2 hj)
  have hm : ∀ y, y ∈ LB.wchart M φ' j := fun y => by rw [hW]; trivial
  have e : t.s j = u'.s j := by
    refine Units.ext (fn_eq_of_levels I _ hW _ _ fun e => ?_)
    refine congrArg Units.val (show pullU (thick R I e) _ (t.s j) = pullU (thick R I e) _ (u'.s j) from
      unit_ext fun y _ => ?_)
    choose I₀ hI₀ using fun χ : Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ X => exists_chart hM (χ y)
    refine (gm_pull _ _ y _ (hm _) _).trans (Eq.trans ?_ (gm_pull _ _ y _ (hm _) _).symm)
    rw [Category.id_comp]
    exact (gen_trans ht _ y (hm _) (Good.mem hI₀ φ' _)).trans
      ((congrArg _ ((hv _ _ y I₀ hI₀).trans (h e y I₀ hI₀))).trans (gen_trans hu' _ y (hm _) (Good.mem hI₀ φ' _)).symm)
  refine (hv Z r z J hJ).symm.trans ?_
  exact (gen_trans ht r z (hJ.mem φ' r) (hm _)).trans
    ((congrArg (fun q => _ * gm r z _ q) e).trans (gen_trans hu' r z (hJ.mem φ' r) (hm _)).symm)

theorem prod_gtT {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T : Over (Spec (CommRingCat.of R))}
    (b : T ⟶ D.P.A) (χ : D.X) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ i, h (DegPre.gtφT D T b χ i) ^ DegPre.gtε i =
      (h (DVR.cP D _ χ * b).left)⁻¹ * h (DVR.cP D _ χ).left * h b.left * (h (1 : T ⟶ D.P.A).left)⁻¹ := by
  rw [Fin.prod_univ_four]
  show h (DVR.cP D _ χ * b).left ^ (-1 : ℤ) * h (DVR.cP D _ χ).left ^ (1 : ℤ) * h b.left ^ (1 : ℤ) *
    h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) = _
  simp only [zpow_neg, zpow_one]

theorem level_ext {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ) {G : Over (Spec (CommRingCat.of R))}
    {Z : Scheme.{0}} {p p' : Z ⟶ (thickObj R I e G).left}
    (h : p ≫ (fstG I e G).left = p' ≫ (fstG I e G).left) : p = p' := by
  have h' : p ≫ pullback.fst G.hom (thick R I e) = p' ≫ pullback.fst G.hom (thick R I e) := h
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact (cancel_mono (pullback.fst G.hom (thick R I e))).1 h'

theorem main : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (ιD : D.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.OLinear O ιD ιA ιG → ∀ (a : O) (x : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) (gp gp' : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))), (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ (x ≫ ιG.act a) ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp'.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp'.s χ) (toUnit (Over.mk (thick R I e))).left)) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (g g' : GtPtF D.toPre F), GtPt.IsPullF F (toUnit (TF (R := R) F)).left gp g → GtPt.IsPullF F (toUnit (TF (R := R) F)).left gp' g' → Geo.Tor.GtAct ιD a g g' := by
  intro hG R _ _ _ I hI _ D A G _ _ U O _ _ _ ιD ιA ιG hlin a x gp gp' h h' F _ _ g g' hg hg'
  have : IsAdicComplete I R := hI.2.2.2
  choose xe hx hb hs using h
  choose xe' hx' hb' hs' using h'
  have hxe : ∀ e, (xe' e).left = (xe e).left ≫ ((Over.pullback (thick R I e)).map (ιG.act a)).left := fun e =>
    level_ext I e ((congrArg (·.left) (hx' e)).trans (Eq.symm ((Category.assoc _ _ _).trans
      ((congrArg (fun q => (xe e).left ≫ q) (DVR.fstG_act I e (ιG.act a))).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ (ιG.act a).left) (hx e)).trans
          (Category.assoc _ _ _)))))))
  have hB : gp'.b = gp.b ≫ ιD.onB.act a := by
    ext1
    refine GlobalTheory.hom_ext_of_isHausdorff I fun e => ?_
    refine (congrArg (·.left) (hb' e)).symm.trans ?_
    refine (congrArg (fun q => q ≫ (U.gt e).pG.left) (hxe e)).trans ((Category.assoc _ _ _).trans ?_)
    refine (congrArg (fun q => (xe e).left ≫ q) (DVR.pG_act U hlin e a)).trans ((Category.assoc _ _ _).symm.trans ?_)
    exact (congrArg (fun q => q.left ≫ (ιD.onB.act a).left) (hb e)).trans (Category.assoc _ _ _)
  have hgb : g.b = toUnit _ ≫ gp.b := Over.OverMorphism.ext hg.1
  have hgb' : g'.b = toUnit _ ≫ gp'.b := Over.OverMorphism.ext hg'.1
  refine ⟨by rw [hgb, hgb', hB, Category.assoc], fun u hu hu₀ χ => corr_of_val D.toPre.P.isLB fun y J hJ => ?_⟩
  have E : ∀ (T : Over (Spec (CommRingCat.of R))) (b : T ⟶ D.toPre.P.A), b = toUnit T ≫ gp.b →
      (lift (toUnit T ≫ D.toPre.c χ) b).left = (toUnit T).left ≫ (lift (DVR.cP D.toPre _ χ) gp.b).left := by
    rintro T b rfl
    rw [← Over.comp_left, comp_lift, DVR.cP, ← Category.assoc, comp_toUnit]
  have key := val_eq_of_levels I D.toPre.P.isLB (K := Fin 4 ⊕ Fin 6) (K' := Fin 4)
    (u := LB.mulGen D.toPre.P.L _ _ _ _ (gp.s (star a • χ))
      (LB.pullGen D.toPre.P.L _ _ u (lift (DVR.cP D.toPre _ χ) gp.b).left)) (u' := gp'.s χ)
    (fun V _ h => by
      refine (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 6) (U := V) _ (prod_gtT gp.b (star a • χ) h)
        (prod_ros _ _ (DVR.cP D.toPre _ χ) gp.b h)).trans (Eq.trans ?_ (prod_gtT gp'.b χ h).symm)
      have hc : DVR.cP D.toPre (𝟙_ _) (star a • χ) = DVR.cP D.toPre _ χ ≫ ιD.onB.act (star a) := by
        rw [DVR.cP, ιD.c_lin, ← Category.assoc]; rfl
      rw [hc, hB]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (gp.isGen _) (DVR.pullGen_isGen _ _ _ _ hu _)) (gp'.isGen χ)
    (fun e z J hJ => by
      have H := val_corr hJ (TLinPf.tLin_of hG R I O D A G U ιD ιA ιG hlin e a u hu hu₀ χ) (xe e).left
      have H₁ := val_corr hJ (hs e (star a • χ)) (𝟙 _)
      have H₂ := val_corr hJ (hs' e χ) (𝟙 _)
      rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at H₁ H₂
      rw [val_mul hJ, val_pull hJ, val_pull hJ, ← hxe, H₁, H₂] at H
      refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg _ ((val_pull hJ _ _ _).trans ?_)) H)
      have E' : xe e ≫ lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG = lift (toUnit _ ≫ D.toPre.c χ) (xe e ≫ (U.gt e).pG) := by
        rw [comp_lift, ← Category.assoc, comp_toUnit]
      exact congrArg (fun q => val u q z J) ((congrArg (·.left) E').trans (E _ _ (hb e))).symm)
    _ (toUnit (TF (R := R) F)).left y J hJ
  have H₁ := val_corr hJ (hg.2 (star a • χ)) (𝟙 _)
  have H₂ := val_corr hJ (hg'.2 χ) (𝟙 _)
  rw [val_pull hJ, Category.id_comp] at H₁ H₂
  refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (((val_mul hJ _ _ _).symm.trans key).trans H₂.symm))
  refine congrArg₂ (· * ·) H₁ ((val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
  exact congrArg (fun q => val u q y J) ((Category.id_comp _).trans (E _ _ hgb))

end GlobalTheory.CoordLinear
