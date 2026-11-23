import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawTrivialityOnDenseFibresProductAbelianStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.MulRoot

open CechPic

theorem pull_pow_pol (h : Out.MulPullSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S) (n : ℕ) :
    pull (𝟙 P.A ^ n : P.A ⟶ P.A).left (cls P.L P.isLB) = (n ^ 2) • cls P.L P.isLB := by
  have e := (cls_eq_zero_iff (LB.isLB_linComb P.isLB _ _)).2 (h S P n)
  rw [cls_linComb P.isLB, Fin.sum_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_id, neg_smul, one_smul] at e
  rw [← natCast_zsmul, Nat.cast_pow]
  exact (add_neg_eq_zero.1 e).symm

theorem pull_inv_pol (h : Out.MulPullSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S)
    (hΘ : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen) :
    pull ((𝟙 P.A)⁻¹ : P.A ⟶ P.A).left (cls P.L P.isLB) = cls P.L P.isLB := by
  have := P.isAb.comm
  have h₀ := pull_pow_pol h P 0
  have h₂ := pull_pow_pol h P 2
  have e := lam_mul_left P.isLB hΘ (𝟙 P.A) (𝟙 P.A)⁻¹ (𝟙 P.A)
  rw [mul_inv_cancel, lam_one_left] at e
  rw [pow_zero] at h₀
  rw [pow_two (𝟙 P.A)] at h₂
  simp only [lam, inv_mul_cancel, h₀, h₂, Over.id_left, pull_id] at e
  linear_combination (norm := module) e

theorem lam_eq_zero (laws : Out.Laws) {K : Type} [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K))
    {D : LB P.A.left} (hD : D.IsLB) (hΘ : ∃ t : LB.Gen (Theta P.A D), t.IsGen) {m : ℕ} (hm : 0 < m)
    (h : pull (𝟙 P.A ^ m : P.A ⟶ P.A).left (cls D hD) = 0) {T : Over (Sp K)} (x y : T ⟶ P.A) :
    lam (cls D hD) x y = 0 := by
  have := P.isAb.comm
  have := P.isAb.smooth
  have kill : ∀ {T : Over (Sp K)} (x : T ⟶ P.A), pull (x ^ m).left (cls D hD) = 0 := fun x => by
    have e : x ^ m = x ≫ 𝟙 P.A ^ m := by rw [MonObj.comp_pow, Category.comp_id]
    rw [e, Over.comp_left, pull_comp, h, map_zero]
  have two : ∀ {T : Over (Sp K)} (x y : T ⟶ P.A), lam (cls D hD) (x ^ (m * m)) y = 0 := fun {T} x y => by
    rw [pow_mul, lam_pow_left hD hΘ, ← lam_pow_right hD hΘ]
    have k₁ := kill (1 : T ⟶ P.A)
    rw [one_pow] at k₁
    rw [lam, ← mul_pow, kill, kill, kill, k₁]
    simp
  have hN : (cubeLB P.A ![fst P.A P.A, snd P.A P.A] D).IsLB := LB.isLB_linComb hD _ _
  have val : ∀ {T : Over (Sp K)} (x y : T ⟶ P.A),
      cls _ (pull_isLB hN (lift x y).left) = lam (cls D hD) x y := fun x y => by
    rw [cls_pull hN, cls_cube_two hD, pull_lam, lift_fst, lift_snd]
  have gen : ∀ {T : Over (Sp K)} (x y : T ⟶ P.A), lam (cls D hD) x y = 0 →
      ∃ s : ((cubeLB P.A ![fst P.A P.A, snd P.A P.A] D).pull (lift x y).left).Gen, s.IsGen := fun x y e =>
    (cls_eq_zero_iff _).1 ((val x y).trans e)
  have main := GlobalTheory.T.seesaw_triviality_on_dense_fibres_product_abelian laws.globalFns K P.A P.A _ P.L P.isAb P.isAb P.isLB P.ample hN
    (gen _ _ (lam_one_left _ _)) (by
      have hs : Surjective (𝟙 P.A ^ (m * m)).left := (laws.mulN _ P (m * m) (Nat.mul_pos hm hm)).2.2.1
      refine dense_image_points (𝟙 P.A ^ (m * m)) _ fun u => gen _ _ ?_
      rw [MonObj.comp_pow, MonObj.comp_pow]
      exact two _ _) (gen _ _ (lam_one_right _ _))
  rw [← val, cls_pull hN, (cls_eq_zero_iff hN).2 main, map_zero]

end GlobalTheory.MulRoot

namespace GlobalTheory

open CechPic MulRoot

theorem pol_iso_symmetrised_root : Out.Laws → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N : LB P.A.left) (m : ℕ), Odd m → N.IsLB → LBIso (lbPow P.L (m ^ 2)) (N.pull ((𝟙 P.A) ^ m).left) → LBIso P.L (LB.LinComb N (K := Fin 2) ![𝟙 P.A.left, (GrpObj.inv : P.A ⟶ P.A).left] ![(1 - (m : ℤ)) / 2, ((m : ℤ) + 1) / 2]) := by
  intro laws cube K _ _ P N m hm hN hiso
  have := P.isAb.comm
  have hL := P.isLB
  have hD : (LB.div N P.L).IsLB := LB.isLB_div hN hL
  have hd : cls _ hD = cls N hN - cls P.L hL := cls_div hN hL hD
  have h₁ : pull (𝟙 P.A ^ m : P.A ⟶ P.A).left (cls _ hD) = 0 := by
    have e := (cls_eq_iff (LB.isLB_linComb hL _ _) (pull_isLB hN _)).2 hiso
    rw [cls_lbPow hL, cls_pull hN] at e
    rw [hd, map_sub, ← e, pull_pow_pol laws.mulPull, sub_self]
  have hlam := fun x y : P.A ⟶ P.A => lam_eq_zero laws P hD (cube _ P _ hD) hm.pos h₁ x y
  have h₀ : pull (1 : P.A ⟶ P.A).left (cls _ hD) = 0 := by
    have e : (1 : P.A ⟶ P.A) = 1 ≫ 𝟙 P.A ^ m := by rw [MonObj.comp_pow, Category.comp_id, one_pow]
    rw [e, Over.comp_left, pull_comp, h₁, map_zero]
  have hadd : ∀ x y : P.A ⟶ P.A, pull (x * y).left (cls _ hD) = pull x.left (cls _ hD) + pull y.left (cls _ hD) :=
    fun x y => by
      have e := hlam x y
      rw [lam, h₀] at e
      linear_combination (norm := module) e
  have hpow : ∀ n : ℕ, pull (𝟙 P.A ^ n : P.A ⟶ P.A).left (cls _ hD) = n • cls _ hD := fun n => by
    induction n with
    | zero => rw [pow_zero, h₀, zero_nsmul]
    | succ n ih => rw [pow_succ, hadd, ih, Over.id_left, pull_id, succ_nsmul]
  have hmd : m • cls _ hD = 0 := (hpow m).symm.trans h₁
  have hinv := hadd (𝟙 P.A) (𝟙 P.A)⁻¹
  rw [mul_inv_cancel, h₀, Over.id_left, pull_id] at hinv
  have hsym := pull_inv_pol laws.mulPull P (cube _ P _ hL)
  have ei : ((𝟙 P.A)⁻¹ : P.A ⟶ P.A) = GrpObj.inv := Category.id_comp _
  rw [ei] at hinv hsym
  rw [hd, map_sub, hsym] at hinv
  rw [hd] at hmd
  obtain ⟨k, rfl⟩ := hm
  have a : (1 - ((2 * k + 1 : ℕ) : ℤ)) / 2 = -k := by push_cast; omega
  have b : (((2 * k + 1 : ℕ) : ℤ) + 1) / 2 = k + 1 := by push_cast; omega
  rw [← cls_eq_iff hL (LB.isLB_linComb hN _ _), cls_linComb hN, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_id, a, b]
  linear_combination (norm := module) ((k : ℤ) + 1) • hinv + hmd

end GlobalTheory
