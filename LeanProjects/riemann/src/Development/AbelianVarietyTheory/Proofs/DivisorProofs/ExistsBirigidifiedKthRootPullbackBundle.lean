import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelOn
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRankAt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeQuotientByFiniteTranslations
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBiduality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeMulNFiniteFlatSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsMonHomFactorOfFlatSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.SharpPull
namespace GlobalTheory.KthRoot

theorem finite_flat_surjective_mulN_any : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A],
    IsAbelianScheme A → ∀ n : ℕ, 0 < n →
      IsFinite (mulN A n).left ∧ Flat (mulN A n).left ∧ Surjective (mulN A n).left := by
  intro S A _ hA n hn
  have hc := hA.comm
  obtain ⟨h1, h2⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA S A hA n hn
  have e : mulN A n = ReciprocityTheory.ChartRestriction.G.Out.mulA A n := GlobalTheory.MulFlatSurj.mulN_eq_pow A n
  rw [e]
  refine ⟨h1, h2, GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => ?_⟩
  have hf : IsFinite ((Over.pullback t).map (ReciprocityTheory.ChartRestriction.G.Out.mulA A n)).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) h1
  rw [GlobalTheory.MulFiniteFlat.pullback_map_mulA] at hf ⊢
  have hB := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback t A hA
  have hBc := hB.comm
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    hB _ (GlobalTheory.AbLaw.MulN.isMonHom_mulA _ n) hf).2

theorem exists_descent_mulN : ∀ (Y : Scheme.{0}) (A D : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj D] (h : A ⟶ D) (k : ℕ) (U : Scheme.{0}) (t : U ⟶ Y) (AU : Over U) [GrpObj AU] [IsCommMonObj AU] (φ : AU.left ⟶ A.left), IsAbelianScheme A → IsMonHom h → 0 < k → IsGrpPullback AU A t φ → (∀ (T : Over Y) (s : T.left ⟶ U), s ≫ t = T.hom → ∀ a : T ⟶ A, a ^ k = 1 → a ≫ h = 1) → ∃ y : AU ⟶ (Over.pullback t).obj D, IsMonHom y ∧ (mulN AU k ≫ y).left ≫ pullback.fst D.hom t = φ ≫ h.left := by
  intro Y A D _ _ _ h k U t AU _ _ φ hA hh hk hpb hker
  have hAU : IsAbelianScheme AU := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hpb
  have hψ := isGrpPullback_pullback D t
  obtain ⟨hU, ehU⟩ := GlobalTheory.SharpPull.exists_lift hpb hψ h
  have : IsMonHom hU := GlobalTheory.SharpPull.isMonHom_lift hpb hψ ehU
  obtain ⟨hfin, hflat, hsurj⟩ := finite_flat_surjective_mulN_any U AU hAU k hk
  have hmon : IsMonHom (mulN AU k) := by
    rw [GlobalTheory.MulFlatSurj.mulN_eq_pow]
    exact GlobalTheory.AbLaw.MulN.isMonHom_mulA AU k
  obtain ⟨⟨y, hy, hyk⟩, -⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective U AU AU _ (mulN AU k) hU hmon
    inferInstance hflat hsurj inferInstance (fun T x hx => by
      apply GlobalTheory.SharpPull.push_inj hψ
      rw [GlobalTheory.SharpPull.push_comp hpb hψ ehU, map_one]
      refine hker (Over.mk (T.hom ≫ t)) T.hom rfl _ ?_
      have ex : x ^ k = x ≫ mulN AU k := by
        rw [GlobalTheory.MulFlatSurj.mulN_eq_pow, MonObj.comp_pow, Category.comp_id]
      rw [← map_pow, ex, hx, map_one])
  exact ⟨y, hy, by rw [hyk, ehU]⟩

theorem exists_birigid_root_of_descent : ∀ (Y : Scheme.{0}) (A D : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj D] (Q : LB (A ⊗ D).left) (h : A ⟶ D) (k : ℕ) (X : Scheme.{0}) (M : LB X) (c : (A ⊗ A).left ⟶ X), GlobalTheory.AbDual.IsDual A D Q → GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) → M.IsLB → LBIso (M.pull c) (Q.pull (lift (fst A A) (snd A A ≫ h)).left) → ∀ (U : Scheme.{0}) (t : U ⟶ Y) (AU : Over U) [GrpObj AU] [IsCommMonObj AU] (φ : AU.left ⟶ A.left) (φ₂ : (G2 AU).left ⟶ (G2 A).left), IsGrpPullback AU A t φ → IsSquare φ φ₂ → ∀ y : AU ⟶ (Over.pullback t).obj D, IsMonHom y → (mulN AU k ≫ y).left ≫ pullback.fst D.hom t = φ ≫ h.left → ∃ P : LB (G2 AU).left, P.IsLB ∧ (∃ t : (P.pull (lift (1 : AU ⟶ AU) (𝟙 AU)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 AU) (1 : AU ⟶ AU)).left).Gen, t.IsGen) ∧ LBIso (M.pull (φ₂ ≫ c)) (lbPow P k) := by
  intro Y A D _ _ _ Q h k X M c hQ hadd hM hiso U t AU _ _ φ φ₂ hpb hsq y hy hyk
  have hψ := isGrpPullback_pullback D t
  let W : Over U := AU ⊗ AU
  let a₁ : Over.mk (W.hom ≫ t) ⟶ A := pushHom hpb W (fst AU AU)
  let d : Over.mk (W.hom ≫ t) ⟶ D := pushHom hψ W (snd AU AU ≫ y)
  let P : LB (G2 AU).left := Q.pull (lift a₁ d).left
  have hP : P.IsLB := pull_isLB hQ.isLB _

  have key : ∀ (T : Over U) (z : T ⟶ W), CechPic.pull z.left (cls P hP) =
      evc hQ.isLB (pushHom hpb T (z ≫ fst AU AU)) (pushHom hψ T (z ≫ snd AU AU ≫ y)) := by
    intro T z
    rw [cls_pull hQ.isLB, ← pull_comp, evc]
    congr 2
    apply left_ext
    · rw [Category.assoc, lift_left_fst, lift_left_fst]
      rfl
    · rw [Category.assoc, lift_left_snd, lift_left_snd]
      rfl

  refine ⟨P, hP, (cls_eq_zero_iff (pull_isLB hP _)).1 ?_, (cls_eq_zero_iff (pull_isLB hP _)).1 ?_, ?_⟩
  · rw [cls_pull hP, key, lift_fst, map_one]
    exact hQ.additive.evc_one hQ.isLB _
  · rw [cls_pull hP, key, lift_snd_assoc, MonObj.one_comp, map_one]
    exact evc_one_right hQ.isLB hQ.zero _
  · have hs : (swap Q).IsLB := pull_isLB hQ.isLB _
    have add2 : ∀ (Z : Over Y) (a : Z ⟶ A) (u v : Z ⟶ D),
        evc hQ.isLB a (u * v) = evc hQ.isLB a u + evc hQ.isLB a v := by
      intro Z a u v
      rw [← evc_swap hQ.isLB hs, ← evc_swap hQ.isLB hs, ← evc_swap hQ.isLB hs]
      exact (isAdditive_iff hs).1 hadd Z u v a
    have pow2 : ∀ (Z : Over Y) (a : Z ⟶ A) (u : Z ⟶ D) (n : ℕ),
        evc hQ.isLB a (u ^ n) = n • evc hQ.isLB a u := by
      intro Z a u n
      induction n with
      | zero => rw [pow_zero, zero_smul]; exact evc_one_right hQ.isLB hQ.zero a
      | succ n ih => rw [pow_succ, add2, ih, succ_nsmul]
    have ep : (𝟙 W ≫ snd AU AU ≫ y) ^ k = snd AU AU ≫ mulN AU k ≫ y := by
      rw [Category.id_comp, ← MonObj.comp_pow, GlobalTheory.MulFlatSurj.mulN_eq_pow, MonObj.pow_comp, Category.id_comp]
    have e1 : cls P hP = CechPic.pull (𝟙 W : W ⟶ W).left (cls P hP) := by rw [Over.id_left, pull_id]
    refine (cls_eq_iff (pull_isLB hM _) (isLB_lbPow hP k)).1 ?_
    rw [cls_lbPow hP, e1, key, ← pow2, ← map_pow, cls_pull hM, pull_comp, ← cls_pull hM c (pull_isLB hM c),
      (cls_eq_iff (pull_isLB hM c) (pull_isLB hQ.isLB _)).2 hiso, cls_pull hQ.isLB, evc, ← pull_comp]
    congr 2
    apply left_ext
    · rw [Category.assoc, lift_left_fst, lift_left_fst, push_left, hsq.1, Category.id_comp]
    · rw [Category.assoc, lift_left_snd, lift_left_snd, push_left, ep, Over.comp_left, Over.comp_left,
        Category.assoc, hyk, ← Category.assoc, hsq.2, Category.assoc]

theorem exists_birigid_kth_root : ∀ (Y : Scheme.{0}) (A D : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj D] (Q : LB (A ⊗ D).left) (h : A ⟶ D) (k : ℕ) (X : Scheme.{0}) (M : LB X) (c : (A ⊗ A).left ⟶ X), IsAbelianScheme A → IsAbelianScheme D → GlobalTheory.AbDual.IsDual A D Q → GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) → IsMonHom h → 0 < k → IsUnit (k : Γ(Y, ⊤)) → M.IsLB → LBIso (M.pull c) (Q.pull (lift (fst A A) (snd A A ≫ h)).left) → ∀ (U : Scheme.{0}) (t : U ⟶ Y) (AU : Over U) [GrpObj AU] [IsCommMonObj AU] (φ : AU.left ⟶ A.left) (φ₂ : (G2 AU).left ⟶ (G2 A).left), IsGrpPullback AU A t φ → IsSquare φ φ₂ → (∀ (T : Over Y) (s : T.left ⟶ U), s ≫ t = T.hom → ∀ a : T ⟶ A, a ^ k = 1 → a ≫ h = 1) → ∃ P : LB (G2 AU).left, P.IsLB ∧ (∃ t : (P.pull (lift (1 : AU ⟶ AU) (𝟙 AU)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 AU) (1 : AU ⟶ AU)).left).Gen, t.IsGen) ∧ LBIso (M.pull (φ₂ ≫ c)) (lbPow P k) := by
  intro Y A D _ _ _ Q h k X M c hA hD hQ hadd hh hk hku hM hiso U t AU _ _ φ φ₂ hpb hsq hker
  obtain ⟨y, hy, hyk⟩ := exists_descent_mulN Y A D h k U t AU φ hA hh hk hpb hker
  exact exists_birigid_root_of_descent Y A D Q h k X M c hQ hadd hM hiso U t AU φ φ₂ hpb hsq y hy hyk

end GlobalTheory.KthRoot
