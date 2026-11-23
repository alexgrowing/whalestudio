import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxSec

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.BoxPull

open GlobalTheory.BoxPhi

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {F : Type} [Field F] [Algebra (FractionRing V) F] {O : Type} [CommRing O] [StarRing O]

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  by_cases h : f y ∈ U
  · rw [gs_eq f y U h, map_zero, map_zero]
  · exact dif_neg h

theorem prod_pull_zero (D : DegData V (maximalIdeal V)) [Module O D.toPre.X] (oa : D.toPre.OAct O) (a : O) (k N : ℕ)
    (hN : 1 ≤ N) (χ : D.toPre.X) {U : Type} [CommGroup U] (h : ((TF (R := V) F).left ⟶ D.toPre.P.A.left) → U) :
    ∏ i, h ((DegPre.zF D.toPre F).left ≫ pullφ D F oa a χ i) ^ pullε k N i =
      h (1 : TF (R := V) F ⟶ D.toPre.P.A).left ^ (k * (N - 1)) := by
  have := oa.onB.hom a
  have p₃ := prod_fam D.toPre F (DegPre.zF D.toPre F) (star a • χ) (k * N) h
  have p₄ := prod_fam D.toPre F (DegPre.zF D.toPre F ≫ aF D F oa a) χ k h
  have z₂ : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
  have z₃ : (DegPre.zF D.toPre F ≫ aF D F oa a) ≫ DegPre.prB D.toPre F = 1 := by
    rw [Category.assoc, aF, lift_snd, ← Category.assoc, z₂, MonObj.one_comp]
  rw [z₂, _root_.mul_one] at p₃
  rw [z₃, _root_.mul_one] at p₄
  simp only [Over.comp_left, Category.assoc] at p₄
  refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)).trans ?_
  rw [← zpow_natCast, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hN]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem aF_pr {j : ℕ} {D D' : DegData V (maximalIdeal V)} (pD : IsPowDeg D'.toPre D.toPre j)
    [Module O D.toPre.X] [Module O D'.toPre.X] (oa : D.toPre.OAct O) (oa' : D'.toPre.OAct O) (a : O) (i : Fin j)
    (hact : oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a) :
    (aF D' F oa' a).left ≫ prB pD F i = prB pD F i ≫ (aF D F oa a).left := by
  refine congrArg (fun q => q.left) (?_ : aF D' F oa' a ≫ (TF (R := V) F ◁ pD.pw.pr i) =
    (TF (R := V) F ◁ pD.pw.pr i) ≫ aF D F oa a)
  apply CartesianMonoidalCategory.hom_ext
  · simp [aF]
  · simp [aF, hact]

theorem pullAl_box {j : ℕ} {D D' : DegData V (maximalIdeal V)} (pD : IsPowDeg D'.toPre D.toPre j)
    [Module O D.toPre.X] [Module O D'.toPre.X]
    (hx : ∀ (a : O) (x : D'.toPre.X) (i : Fin j), pD.xe (a • x) i = a • pD.xe x i)
    (oa : D.toPre.OAct O) (oa' : D'.toPre.OAct O)
    (hact : ∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a) (a : O) (N k : ℕ) (hN : 1 ≤ N)
    (s : Fin j → Fam D.toPre F k) (s' : Fin j → Fam D.toPre F (k * N)) (S : Fam D'.toPre F k)
    (S' : Fam D'.toPre F (k * N)) (hs : ∀ i, PullAl D F oa a k N (s i) (s' i)) (hS : IsBoxFam pD F k S s)
    (hS' : IsBoxFam pD F (k * N) S' s') : PullAl D' F oa' a k N S S' := by
  have ht := fun i => aF_pr (F := F) pD oa oa' a i (hact a i)
  refine ⟨fun χ' => ?_, fun β' hβ' => ?_⟩
  · choose u hu hc hr using fun i => (hs i).1 (pD.xe χ' i)
    have hφ : ∀ i b, pullφ D' F oa' a χ' b ≫ (pD.pw.pr i).left =
        prB pD F i ≫ pullφ D F oa a (pD.xe χ' i) b := by
      rintro i (b | b)
      · exact ((hS' (star a • χ')).choose i b).trans (by rw [hx]; rfl)
      · show ((aF D' F oa' a).left ≫ DegPre.famφ D'.toPre F χ' b) ≫ _ =
          _ ≫ (aF D F oa a).left ≫ DegPre.famφ D.toPre F (pD.xe χ' i) b
        rw [Category.assoc, (hS χ').choose i b, ← Category.assoc, ht, Category.assoc]
    obtain ⟨v, hv, vv⟩ := exists_box_gen D.toPre.P.isLB D'.toPre.P.isLB pD.w pD.w_gen hφ u hu
    refine ⟨v, hv, corr_of_val D'.toPre.P.isLB fun y J' hJ' => ?_,
      (secRel_iff D'.toPre.P.isLB _ _ _ _ _ _ _ _ _ v).2 fun y J' hJ' => ?_⟩
    · obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at D.toPre.P.isLB y
      have e₂ := vv _ (DegPre.zF D'.toPre F).left y J J' hJ hJ'
      let r : (TF (R := V) F).left ⟶ (TK V).left := 𝟙 (TF (R := V) F).left ≫ jFK (R := V) F
      have e₃ : om pD.w y J J' (1 : TF (R := V) F ⟶ D'.toPre.P.A).left * val D'.toPre.rigK r y J' =
          ∏ _i : Fin j, val D.toPre.rigK r y J := by
        have z : (1 : TF (R := V) F ⟶ D'.toPre.P.A).left = r ≫ (toUnit (TK V)).left ≫ eSec D'.toPre.P.A :=
          (show (1 : TF (R := V) F ⟶ D'.toPre.P.A).left =
              jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D'.toPre.P.A by
            show (toUnit _ ≫ η[D'.toPre.P.A]).left = _
            rw [Over.comp_left]
            rfl).trans (congrArg (· ≫ (toUnit (TK V)).left ≫ eSec D'.toPre.P.A)
            (Category.id_comp (jFK (R := V) F)).symm)
        rw [z]
        exact BoxFamily.rig_val pD hJ hJ' r
      have e₅ : ∀ i, val (u i) ((DegPre.zF D'.toPre F).left ≫ prB pD F i) y J =
          val D.toPre.rigK r y J ^ (k * (N - 1)) := fun i => by
        have := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (hc i) (𝟙 _)).trans
          ((val_pull hJ _ _ _).trans (BoxFamily.val_powGen _ _ _ _ _ _ _)))
        rw [Category.id_comp] at this
        rw [BoxFamily.zF_pr]
        exact this
      rw [prod_pull_zero D' oa' a k N hN χ', Finset.prod_congr rfl (fun i _ => e₅ i), Finset.prod_pow, ← e₃,
        mul_pow] at e₂
      refine (val_pull hJ' _ _ _).trans (Eq.trans ?_
        ((val_pull hJ' _ _ _).trans (BoxFamily.val_powGen _ _ _ _ _ _ _)).symm)
      rw [Category.id_comp]
      exact mul_left_cancel e₂
    · obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at D.toPre.P.isLB y
      have e₁ := fam_val pD hS' (star a • χ') (𝟙 _) y hJ hJ'
      have e₂ := fam_val pD hS χ' (𝟙 _ ≫ (aF D' F oa' a).left) y hJ hJ'
      have e₃ := vv _ (𝟙 _) y J J' hJ hJ'
      have e₄ : ∀ i, sval ((s' i).s (pD.xe (star a • χ') i)) (𝟙 _ ≫ prB pD F i) y J =
          sval ((s i).s (pD.xe χ' i)) ((𝟙 _ ≫ (aF D' F oa' a).left) ≫ prB pD F i) y J *
            (val (u i) (𝟙 _ ≫ prB pD F i) y J).val := fun i => by
        rw [hx, Category.assoc, ht, ← Category.assoc]
        exact (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ (u i)).1 (hr i) _ _ y J hJ
      have e₅ : ∏ b, om pD.w y J J' (𝟙 _ ≫ pullφ D' F oa' a χ' b) ^ pullε k N b =
          (∏ b, om pD.w y J J' (𝟙 _ ≫ DegPre.famφ D'.toPre F (star a • χ') b) ^ DegPre.famε (k * N) b) *
          (∏ b, om pD.w y J J' ((𝟙 _ ≫ (aF D' F oa' a).left) ≫ DegPre.famφ D'.toPre F χ' b) ^
            DegPre.famε k b)⁻¹ := by
        simp only [Category.assoc]
        exact prod_sum₂ (K := Fin 4) (K' := Fin 4) _ rfl (prod_neg _ _ rfl)
      rw [Finset.prod_congr rfl (fun i _ => e₄ i), Finset.prod_mul_distrib, ← e₂, ← Units.coe_prod, ← e₃, e₅] at e₁
      exact alg_fin e₁
  · obtain ⟨i, hi⟩ : ∃ i, ∀ χ, pD.xe β' i ≠ star a • χ := by
      by_contra hne
      push Not at hne
      choose χ hχ using hne
      refine hβ' (pD.xe.symm χ) (pD.xe.injective (funext fun i => ?_))
      rw [hx, AddEquiv.apply_symm_apply, hχ]
    have hz := (hs i).2 _ hi
    intro jj
    refine fn_ext fun y hy => ?_
    obtain ⟨J', hJ', e⟩ := sval_trans D'.toPre.P.isLB (S'.s β') y jj hy
    obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at D.toPre.P.isLB y
    have e₁ := fam_val pD hS' β' (𝟙 _) y hJ hJ'
    have z₀ : sval ((s' i).s (pD.xe β' i)) (𝟙 _ ≫ prB pD F i) y J = 0 := by
      exact (congrArg (gs _ y _) (hz _)).trans (gs_zero' _ y _)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) z₀, Units.mul_right_eq_zero] at e₁
    rw [e₁, mul_zero] at e
    refine e.trans ?_
    exact (gs_zero' _ y _).symm

theorem main : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X], (∀ (a : O) (x : D'.toPre.X) (i : Fin j), pD.xe (a • x) i = a • pD.xe x i) → ∀ (oa : D.toPre.OAct O) (oa' : D'.toPre.OAct O), (∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a) → ∀ (a : O) (N k : ℕ), 1 ≤ N → 1 ≤ k → a * star a = (N : O) → ∀ (s : Fin j → Fam D.toPre F k) (s' : Fin j → Fam D.toPre F (k * N)) (S : Fam D'.toPre F k) (S' : Fam D'.toPre F (k * N)), (∀ i, PullAl D F oa a k N (s i) (s' i)) → IsBoxFam pD F k S s → IsBoxFam pD F (k * N) S' s' → PullAl D' F oa' a k N S S' :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ pD _ _ _ _ _ _ _ _ hx oa oa' hact a N k hN _ _ s s' S S' hs hS hS' =>
    pullAl_box pD hx oa oa' hact a N k hN s s' S S' hs hS hS'

end GlobalTheory.BoxPull
