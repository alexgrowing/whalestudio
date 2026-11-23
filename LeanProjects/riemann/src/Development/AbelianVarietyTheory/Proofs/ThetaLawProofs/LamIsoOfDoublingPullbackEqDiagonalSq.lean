import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClosedTriv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteFlatSurjectiveMulByNAbelianScheme
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeLocallyTrivialProductLineBu

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.LamOfDouble

open GlobalTheory.CechPic

theorem isIso_of_factor {X Y Z : Scheme.{0}} (y : X ⟶ Z) (j : Z ⟶ Y) [Mono j] [Flat (y ≫ j)]
    [Surjective (y ≫ j)] [QuasiCompact (y ≫ j)] : IsIso j := by
  have : IsRegularEpi (y ≫ j) := inferInstance
  have : StrongEpi (y ≫ j) := inferInstance
  have : StrongEpi j := strongEpi_of_strongEpi y j
  exact isIso_of_mono_of_strongEpi j

theorem triv_of_pull_pow (hL : Out.Laws) {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) (M : LB A.left) (hM : M.IsLB) (ha : Out.RelAmple A M) (n : ℕ) (hn : 1 ≤ n)
    (N : LB (A ⊗ A).left) (hN : N.IsLB)
    (h0 : ∃ t : (N.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)
    (h1 : ∃ t : (N.pull (((𝟙 A) ^ n : A ⟶ A) ▷ A).left).Gen, t.IsGen) : ∃ t : N.Gen, t.IsGen := by
  have hproj : IsProjBy A.hom :=
    (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ A M hA hM ha R (𝟙 _) A.left (𝟙 _) A.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)).1
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.TrivSubscheme.exists_closed_locTriv hL.globalFns R A A hA hproj N hN
  obtain ⟨t, ht⟩ := h1
  obtain ⟨y, hy⟩ := (hH A ((𝟙 A) ^ n)).1 fun p => ⟨⊤, trivial, GlobalTheory.TorsionFixedAut.exists_gen_pull _ t ht _⟩
  obtain ⟨f₁, f₂, f₃⟩ := GlobalTheory.MulAmple.finite_flat_surjective_pow hL R A hA M hM ha n hn
  have e : y.left ≫ j.left = ((𝟙 A) ^ n : A ⟶ A).left := congrArg (·.left) hy
  rw [← e] at f₁ f₂ f₃
  have : IsIso j.left := isIso_of_factor y.left j.left
  have hw : inv j.left ≫ H.hom = A.hom := by rw [← Over.w j, IsIso.inv_hom_id_assoc]
  have hloc := (hH A (𝟙 A)).2 ⟨Over.homMk (inv j.left) hw, Over.OverMorphism.ext (IsIso.inv_hom_id j.left)⟩
  have key : ∃ t : (N.pull (𝟙 A ▷ A).left).Gen, t.IsGen := by
    refine GlobalTheory.exists_gen_of_local_of_section (A ⊗ A).left A.left (fst A A).left
      (lift (𝟙 A) (1 : A ⟶ A)).left _ (pull_isLB hN _)
      (congrArg (·.left) (lift_fst (𝟙 A) (1 : A ⟶ A)))
      (GlobalTheory.BaseChangeFns.app_surjective hL.globalFns _ A hA _ _ A.hom _ _
        (GlobalTheory.SeesawGlobal.isPullback_tensor A A))
      hloc ?_
    rw [← cls_eq_zero_iff (pull_isLB (pull_isLB hN _) _), cls_pull (pull_isLB hN _), cls_pull hN, ← pull_comp,
      ← Over.comp_left, id_whiskerRight, Category.comp_id]
    exact (cls_eq_zero_iff (pull_isLB hN _)).2 h0
  rw [← cls_eq_zero_iff (pull_isLB hN _), cls_pull hN, id_whiskerRight, Over.id_left, pull_id] at key
  exact (cls_eq_zero_iff hN).1 key

section Pair

variable {S : Scheme.{0}} {A T : Over S}

def ev (c : Pic (A ⊗ A).left) (x y : T ⟶ A) : Pic T.left := pull (lift x y).left c

theorem pull_ev {T' : Over S} (h : T' ⟶ T) (c : Pic (A ⊗ A).left) (x y : T ⟶ A) :
    pull h.left (ev c x y) = ev c (h ≫ x) (h ≫ y) := by
  rw [ev, ev, ← pull_comp, ← Over.comp_left, comp_lift]

variable [GrpObj A] [IsCommMonObj A]

def Biadd (c : Pic (A ⊗ A).left) : Prop :=
  ∀ (T : Over S) (x x' y : T ⟶ A), ev c (x * x') y = ev c x y + ev c x' y ∧ ev c y (x * x') = ev c y x + ev c y x'

theorem biadd_of_axes (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) (M : LB A.left) (hM : M.IsLB)
    (ha : Out.RelAmple A M) (N : LB (A ⊗ A).left) (hN : N.IsLB)
    (h₁ : ∃ t : (N.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (h₂ : ∃ t : (N.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) : Biadd (cls N hN) := by
  intro T x x' y
  obtain ⟨a, b⟩ := GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A M hA hM ha N hN h₁ h₂ T x x' y
  rw [← cls_eq_zero_iff (LB.isLB_linComb hN _ _), cls_linComb hN] at a b
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul,
    neg_smul] at a b
  constructor
  · unfold ev
    rw [← sub_eq_zero, ← a]
    abel
  · unfold ev
    rw [← sub_eq_zero, ← b]
    abel

end Pair

theorem lam_iso_of_pull_two : Out.Laws → ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R] (β : o →+* R) (c : SiegPre h k ζ (spMap β)) (L : LB c.A.left), c.Principal → L.IsLB → LBIso (lbPow c.diag 2) (L.pull ((𝟙 c.A) ^ 2 : c.A ⟶ c.A).left) → LBIso (abelian₂ c.A L) c.P := by
  intro hL h k o _ ζ R _ _ _ β c L hc hLB hiso
  have hM : c.diag.IsLB := pull_isLB c.isLB _
  have hΛ : (abelian₂ c.A L).IsLB := LB.isLB_linComb hLB _ _
  have hN : (LB.div (abelian₂ c.A L) c.P).IsLB := LB.isLB_div hΛ c.isLB
  have hPow : (lbPow c.diag 2).IsLB := LB.isLB_linComb hM _ _
  set l := cls L hLB with hl
  set p := cls c.P c.isLB with hp
  have eΛ : cls _ hΛ = lam l (fst c.A c.A) (snd c.A c.A) := cls_cube_two hLB _ _ hΛ
  have eN : ∀ (T : Over (Sp R)) (x y : T ⟶ c.A), ev (cls _ hN) x y = lam l x y - ev p x y := by
    intro T x y
    rw [cls_div hΛ c.isLB, eΛ, ev, map_sub, pull_lam, lift_fst, lift_snd]
    rfl
  have r₁ : ev p (1 : c.A ⟶ c.A) (𝟙 c.A) = 0 := (cls_eq_zero_iff (pull_isLB c.isLB _)).2 c.rig₁
  have r₂ : ev p (𝟙 c.A) (1 : c.A ⟶ c.A) = 0 := (cls_eq_zero_iff (pull_isLB c.isLB _)).2 c.rig₂
  have n₁ : ∃ t : ((LB.div (abelian₂ c.A L) c.P).pull (lift (1 : c.A ⟶ c.A) (𝟙 c.A)).left).Gen, t.IsGen := by
    refine (cls_eq_zero_iff (pull_isLB hN _)).1 ((eN _ _ _).trans ?_)
    rw [r₁, lam_one_left, sub_zero]
  have n₂ : ∃ t : ((LB.div (abelian₂ c.A L) c.P).pull (lift (𝟙 c.A) (1 : c.A ⟶ c.A)).left).Gen, t.IsGen := by
    refine (cls_eq_zero_iff (pull_isLB hN _)).1 ((eN _ _ _).trans ?_)
    rw [r₂, lam_one_right, sub_zero]
  have bN := biadd_of_axes hL.globalFns c.ab _ hM hc.1 _ hN n₁ n₂
  have bP : Biadd p := biadd_of_axes hL.globalFns c.ab _ hM hc.1 _ c.isLB c.rig₁ c.rig₂
  have sy : ∀ (T : Over (Sp R)) (x y : T ⟶ c.A), ev p x y = ev p y x := by
    intro T x y
    have e : p = ev p (snd c.A c.A) (fst c.A c.A) := (cls_eq_iff c.isLB (pull_isLB c.isLB _)).2 c.symm
    calc ev p x y = pull (lift x y).left (ev p (snd c.A c.A) (fst c.A c.A)) := by rw [← e]; rfl
      _ = ev p y x := by rw [pull_ev, lift_fst, lift_snd]
  have dbl : ∀ (T : Over (Sp R)) (x : T ⟶ c.A), pull (x * x).left l = ev p x x + ev p x x := by
    intro T x
    have e : 2 • ev p (𝟙 c.A) (𝟙 c.A) = pull ((𝟙 c.A) ^ 2 : c.A ⟶ c.A).left l :=
      (cls_lbPow hM 2 hPow).symm.trans ((cls_eq_iff hPow (pull_isLB hLB _)).2 hiso)
    have e' := congrArg (pull x.left) e
    rw [map_nsmul, pull_ev, ← pull_comp, ← Over.comp_left, pow_two, MonObj.comp_mul, Category.comp_id,
      two_smul] at e'
    exact e'.symm
  have z : ∀ (T : Over (Sp R)) (x y : T ⟶ c.A), ev (cls _ hN) (x ^ 4) y = 0 := by
    intro T x y
    have a : ev (cls _ hN) (x * x) (y * y) = 0 := by
      have o₁ : ev p (1 : T ⟶ c.A) (1 : T ⟶ c.A) = 0 := by
        have := (bP T 1 1 1).1
        rw [_root_.mul_one] at this
        exact left_eq_add.1 this
      have o₂ := dbl T 1
      rw [_root_.mul_one, o₁] at o₂
      rw [eN, lam, _root_.mul_mul_mul_comm, dbl, dbl, dbl, o₂]
      simp only [(bP T _ _ _).1, (bP T _ _ _).2, sy T y x]
      abel
    rw [show x ^ 4 = x * x * (x * x) by rw [← pow_two, ← pow_two, ← pow_mul]]
    simp only [(bN T _ _ _).1, (bN T _ _ _).2] at a ⊢
    exact a
  have fin := triv_of_pull_pow hL c.A c.ab _ hM hc.1 4 (by norm_num) _ hN n₂ (by
    refine (cls_eq_zero_iff (pull_isLB hN _)).1 (Eq.trans ?_ (z _ (fst c.A c.A) (snd c.A c.A)))
    have e : ((𝟙 c.A) ^ 4 : c.A ⟶ c.A) ▷ c.A = lift (fst c.A c.A ^ 4) (snd c.A c.A) := by
      ext
      · rw [whiskerRight_fst, lift_fst, MonObj.comp_pow, Category.comp_id]
      · rw [whiskerRight_snd, lift_snd]
    rw [e]
    rfl)
  rw [← cls_eq_zero_iff hN, cls_div hΛ c.isLB, sub_eq_zero] at fin
  exact (cls_eq_iff hΛ c.isLB).1 fin

end GlobalTheory.LamOfDouble

end
