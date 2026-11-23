import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.BirigidPow

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem comp_pow_pt {T T' : Over S} (ρ : T' ⟶ T) (x : T ⟶ A) (n : ℕ) : ρ ≫ x ^ n = (ρ ≫ x) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

def val {P : LB (G2 A).left} (hP : P.IsLB) {T : Over S} (x y : T ⟶ A) : CechPic.Pic T.left :=
  CechPic.pull (lift x y).left (CechPic.cls P hP)

variable {P : LB (G2 A).left} (hP : P.IsLB)

theorem val_one_left (h₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) {T : Over S}
    (y : T ⟶ A) : val hP 1 y = 0 := by
  have e : lift (1 : T ⟶ A) y = y ≫ lift (1 : A ⟶ A) (𝟙 A) := by
    rw [comp_lift, MonObj.comp_one, Category.comp_id]
  rw [val, e, Over.comp_left, CechPic.pull_comp, ← CechPic.cls_pull hP _ (pull_isLB hP _),
    (CechPic.cls_eq_zero_iff (pull_isLB hP _)).2 h₁, map_zero]

theorem val_one_right (h₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) {T : Over S}
    (x : T ⟶ A) : val hP x 1 = 0 := by
  have e : lift x (1 : T ⟶ A) = x ≫ lift (𝟙 A) (1 : A ⟶ A) := by
    rw [comp_lift, MonObj.comp_one, Category.comp_id]
  rw [val, e, Over.comp_left, CechPic.pull_comp, ← CechPic.cls_pull hP _ (pull_isLB hP _),
    (CechPic.cls_eq_zero_iff (pull_isLB hP _)).2 h₂, map_zero]

theorem add_of_triv {T : Over S} (a b c : T.left ⟶ (G2 A).left)
    (H : ∃ t : (LB.LinComb P (K := Fin 3) ![a, b, c] ![1, -1, -1]).Gen, t.IsGen) :
    CechPic.pull a (CechPic.cls P hP) = CechPic.pull b (CechPic.cls P hP) + CechPic.pull c (CechPic.cls P hP) := by
  have hL := LB.isLB_linComb hP (![a, b, c] : Fin 3 → _) ![1, -1, -1]
  have z := (CechPic.cls_linComb hP _ _ hL).symm.trans ((CechPic.cls_eq_zero_iff hL).2 H)
  rw [Fin.sum_univ_three] at z
  have z' : (1 : ℤ) • CechPic.pull a (CechPic.cls P hP) + (-1 : ℤ) • CechPic.pull b (CechPic.cls P hP) +
      (-1 : ℤ) • CechPic.pull c (CechPic.cls P hP) = 0 := z
  rw [one_zsmul, neg_one_zsmul, neg_one_zsmul] at z'
  rw [← sub_eq_zero, ← z']
  abel

variable (hA : IsAbelianScheme A)
  (hamp : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left))
  (h₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
  (h₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen)

include hA hamp h₁ h₂

theorem val_mul_left {T : Over S} (x x' y : T ⟶ A) : val hP (x * x') y = val hP x y + val hP x' y :=
  add_of_triv hP _ _ _ (Biadditive.biadditive_of_triv_axes GlobalTheory.laws_without_cohomology.1 S A _ hA
    (pull_isLB hP _) hamp P hP h₁ h₂ T x x' y).1

theorem val_mul_right {T : Over S} (x y y' : T ⟶ A) : val hP x (y * y') = val hP x y + val hP x y' :=
  add_of_triv hP _ _ _ (Biadditive.biadditive_of_triv_axes GlobalTheory.laws_without_cohomology.1 S A _ hA
    (pull_isLB hP _) hamp P hP h₁ h₂ T y y' x).2

theorem val_pow_left {T : Over S} (x y : T ⟶ A) (n : ℕ) : val hP (x ^ n) y = n • val hP x y := by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact val_one_left hP h₁ y
  | succ n ih => rw [pow_succ, val_mul_left hP hA hamp h₁ h₂, ih, succ_nsmul]

theorem val_pow_right {T : Over S} (x y : T ⟶ A) (n : ℕ) : val hP x (y ^ n) = n • val hP x y := by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact val_one_right hP h₂ x
  | succ n ih => rw [pow_succ, val_mul_right hP hA hamp h₁ h₂, ih, succ_nsmul]

omit hA hamp h₁ h₂ in
theorem cls_lbPow (m : ℕ) (h : (Hecke.lbPow P m).IsLB) : CechPic.cls _ h = m • CechPic.cls P hP := by
  unfold Hecke.lbPow at h ⊢
  rw [CechPic.cls_linComb hP _ _ h]
  simp [CechPic.pull_id]

include hP in

theorem lineBundleIso_tensorPowSq_pullback_mulPair (n : ℕ) :
    LBIso (Hecke.lbPow P (n ^ 2)) (P.pull (Hecke.sq2 ((𝟙 A) ^ n))) := by
  have hL : (Hecke.lbPow P (n ^ 2)).IsLB := LB.isLB_linComb hP _ _
  refine (CechPic.cls_eq_iff hL (pull_isLB hP _)).1 ?_
  rw [cls_lbPow hP, CechPic.cls_pull hP _ (pull_isLB hP _)]
  change _ = val hP (fst A A ≫ (𝟙 A) ^ n) (snd A A ≫ (𝟙 A) ^ n)
  rw [comp_pow_pt, comp_pow_pt, Category.comp_id, Category.comp_id, val_pow_left hP hA hamp h₁ h₂,
    val_pow_right hP hA hamp h₁ h₂, val, lift_fst_snd, Over.id_left, CechPic.pull_id, smul_smul, sq]

omit hP hA hamp h₁ h₂ in

theorem birigidified_pullback_mulPair_iso_tensorPowSq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ P : LB (G2 A).left, P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) →
    ∀ n : ℕ, LBIso (GlobalTheory.UPel.HT.Hecke.lbPow P (n ^ 2)) (P.pull (GlobalTheory.UPel.HT.Hecke.sq2 ((𝟙 A) ^ n))) :=
  fun _ _ _ _ hA _ hP h₁ h₂ hamp n => lineBundleIso_tensorPowSq_pullback_mulPair hP hA hamp h₁ h₂ n

end GlobalTheory.BirigidPow
