import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedLiftPullbackOneProdEndomorphism
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAmpleKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOfSqZeroAgreePairsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjEqOneOfPowEqOneOfSqZeroTrivialStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerLiftUnit

open GlobalTheory.AbDual GlobalTheory.CechPic GlobalTheory.PrinThicken in

theorem ker_pow_eq_one_of_lift : ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (A₀ : Over (Sp C₀)) [GrpObj A₀] [IsCommMonObj A₀] (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : A₀.left ⟶ A.left), IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → ∀ (l : (G2 A₀).left ⟶ (G2 A).left), Geo.Tor.IsSquare i l → ∀ (P₀ : LB (G2 A₀).left) (P : LB (G2 A).left), P₀.IsLB → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → LBIso (P.pull l) P₀ → ∀ (e : ℕ), IsUnit (e : C) → (∀ (T : Over (Sp C₀)) (x : T ⟶ A₀), (∃ t : (P₀.pull (lift (snd A₀ T ≫ x) (fst A₀ T)).left).Gen, t.IsGen) → x ^ e = 1) → ∀ (T : Over (Sp C)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  intro C C₀ _ _ _ _ π hπ hsq A₀ _ _ A _ _ i hi hA l hl P₀ P hP₀ hP r₁ r₂ hsymm amp hred e he ker₀
  have csymm : cls P hP = GlobalTheory.CechPic.pull (lift (snd A A) (fst A A)).left (cls P hP) := by
    rw [← cls_pull hP]
    exact (cls_eq_iff hP (pull_isLB hP _)).2 hsymm
  have wS : (lift (snd A₀ A₀) (fst A₀ A₀)).left ≫ l = l ≫ (lift (snd A A) (fst A A)).left := by
    apply GlobalTheory.AbDual.left_ext
    · rw [Category.assoc, hl.1, GlobalTheory.AbDual.lift_left_fst_assoc, Category.assoc, GlobalTheory.AbDual.lift_left_fst, hl.2]
    · rw [Category.assoc, hl.2, GlobalTheory.AbDual.lift_left_snd_assoc, Category.assoc, GlobalTheory.AbDual.lift_left_snd, hl.1]
  have c₀symm : cls P₀ hP₀ = GlobalTheory.CechPic.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left (cls P₀ hP₀) := by
    have e := (cls_eq_iff (pull_isLB hP l) hP₀).2 hred
    rw [cls_pull hP] at e
    rw [← e, ← pull_comp, wS, pull_comp, ← csymm]
  obtain ⟨D, _, Q, hDab, -, q, q'⟩ := GlobalTheory.abelianDualCrystal.1 _ A hA
  obtain ⟨lam, hlam, hiff⟩ := GlobalTheory.PoincarePull.exists_hom_triv_iff C A hA D Q q q' _ (pull_isLB hP _) amp P hP r₁ r₂
  haveI := hlam
  have hiff' : ∀ (T : Over (Sp C)) (x : T ⟶ A),
      (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ≫ lam = 1 := fun T x hx ↦
    (hiff T x).1 ((triv_ev_iff hP _ _).2 ((evc_comm hP csymm _ _).trans ((triv_ev_iff hP _ _).1 hx)))
  have tors₀ : ∀ (T₀ : Over (Sp C₀)) (z : Over.mk (T₀.hom ≫ spMap π) ⟶ A), z ≫ lam = 1 → z ^ e = 1 := by
    intro T₀ z hz
    let z₀ : Over.mk T₀.hom ⟶ A₀ := liftPt hi T₀.hom z.left (Over.w z)
    have hz₀ : z₀.left ≫ i = z.left := liftPt_left hi _ _ _
    have k₁ : z₀ ^ e = 1 := ker₀ _ z₀ (by
      have e1 := evc_trR hi hi hl.1 hl.2 hP hP₀ hred (Over.mk T₀.hom) z₀
      have e0 : evc hP (fst A (Over.mk (T₀.hom ≫ spMap π))) (snd A _ ≫ z) = 0 :=
        (triv_ev_iff hP _ _).1 ((hiff _ z).2 hz)
      rw [show pushP hi (s := T₀.hom) rfl z₀ = z from Over.OverMorphism.ext hz₀] at e1
      obtain ⟨s, hs⟩ : ∃ s, s ≫ (trR hi (Over.mk T₀.hom)).left = 𝟙 _ := ⟨_, trR_section hi _⟩
      have e2 := congrArg (GlobalTheory.CechPic.pull s) (e1.trans e0)
      rw [← GlobalTheory.CechPic.pull_comp, hs, GlobalTheory.CechPic.pull_id, map_zero] at e2
      exact (triv_ev_iff hP₀ _ _).2 ((evc_comm hP₀ c₀symm _ _).symm.trans e2))
    have hp : ∀ m : ℕ, (z₀ ^ m).left ≫ i = (z ^ m).left := by
      intro m
      induction m with
      | zero =>
        simp only [pow_zero]
        exact one_left_comp hi (s := T₀.hom) rfl
      | succ m ih =>
        rw [pow_succ, pow_succ]
        exact mul_left_comp hi (s := T₀.hom) rfl ih hz₀
    apply Over.OverMorphism.ext
    rw [← hp e, k₁]
    exact one_left_comp hi (s := T₀.hom) rfl
  intro T x hx
  have hx0 : x ≫ lam = 1 := hiff' T x hx
  have hw0 : (x ^ e) ≫ lam = 1 := by rw [pow_comp, hx0, one_pow]
  have hwC : ∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ (x ^ e) = 1 := fun T₀ j ↦ by
    rw [comp_pow]
    exact tors₀ T₀ (j ≫ x) (by rw [Category.assoc, hx0, MonObj.comp_one])
  let k := equalizer.ι lam (1 : A ⟶ D)
  have hk : k ≫ lam = 1 := by rw [equalizer.condition, MonObj.comp_one]
  let u : 𝟙_ (Over (Sp C)) ⟶ equalizer lam (1 : A ⟶ D) :=
    equalizer.lift 1 (by rw [MonObj.one_comp, MonObj.comp_one])
  have hww : (x ^ e) ^ e = 1 := by
    have h1 := GlobalTheory.T.comp_eq_of_sqZero_agree_pairs C C₀ π hπ hsq (equalizer lam (1 : A ⟶ D)) A (k ^ e) 1
      (fun T₀ y ↦ by
        rw [comp_pow, MonObj.comp_one]
        exact tors₀ T₀ (y ≫ k) (by rw [Category.assoc, hk, MonObj.comp_one]))
      T (equalizer.lift (x ^ e) (by rw [hw0, MonObj.comp_one])) (toUnit T ≫ u)
      (fun T₀ j ↦ by
        rw [← cancel_mono k, Category.assoc, Category.assoc, Category.assoc,
          show equalizer.lift (x ^ e) _ ≫ k = x ^ e from equalizer.lift_ι _ _,
          show u ≫ k = 1 from equalizer.lift_ι _ _, hwC, MonObj.comp_one, MonObj.comp_one])
      (by rw [comp_pow, MonObj.comp_one, Category.assoc, show u ≫ k = 1 from equalizer.lift_ι _ _,
        MonObj.comp_one, one_pow])
    rw [comp_pow, show equalizer.lift (x ^ e) _ ≫ k = x ^ e from equalizer.lift_ι _ _, MonObj.comp_one] at h1
    exact h1
  exact GlobalTheory.T.grpObj_eq_one_of_pow_eq_one_of_sqZero_trivial C C₀ π hπ hsq A e he T (x ^ e) hwC hww

end GlobalTheory.KerLiftUnit
