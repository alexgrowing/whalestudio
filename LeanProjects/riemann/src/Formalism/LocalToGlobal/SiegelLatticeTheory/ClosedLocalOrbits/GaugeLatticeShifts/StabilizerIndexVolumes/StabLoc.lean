import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.PairVal
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.CntLocal

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.StabShape

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups

section Gen

variable {K : Type*} [CommRing K] {n : ℕ}

theorem mul_single_mul (l ρ : Matrix (Fin n) (Fin n) K) (i j k m : Fin n) (c : K) :
    (l * Matrix.single i j c * ρ) k m = l k i * c * ρ j m := by
  have h1 : l * Matrix.single i j c = Matrix.of fun k x => if x = j then l k i * c else 0 := by
    ext k x
    rw [Matrix.mul_apply, Matrix.of_apply]
    by_cases hx : x = j
    · subst hx
      rw [if_pos rfl, Finset.sum_eq_single i]
      · simp [Matrix.single_apply]
      · intro y _ hy; simp [Matrix.single_apply, Ne.symm hy]
      · simp
    · rw [if_neg hx]
      exact Finset.sum_eq_zero fun y _ => by simp [Matrix.single_apply, Ne.symm hx]
  rw [h1, Matrix.mul_apply, Finset.sum_eq_single j]
  · simp [mul_assoc]
  · intro y _ hy; simp [hy]
  · simp

theorem pair_unique (l ρ l' ρ' : Matrix (Fin n) (Fin n) K) (hρ : ∀ j, ρ j j = 1) (hρ' : ∀ j, ρ' j j = 1)
    (hl : ∀ i, l i i = 1) (hl' : ∀ i, l' i i = 1) (c : Fin n → Fin n → K) (hc : ∀ i j, IsUnit (c i j))
    (h : ∀ i j, l' * Matrix.single i j (c i j) * ρ' = l * Matrix.single i j (c i j) * ρ) : l' = l ∧ ρ' = ρ := by
  refine ⟨?_, ?_⟩
  · ext k i
    have := congrFun (congrFun (h i i) k) i
    rw [mul_single_mul, mul_single_mul, hρ', hρ] at this
    simp only [mul_one] at this
    exact (hc i i).mul_right_cancel this
  · ext j m
    have := congrFun (congrFun (h j j) j) m
    rw [mul_single_mul, mul_single_mul, hl', hl] at this
    simp only [one_mul] at this
    exact (hc j j).mul_left_cancel this

end Gen

section ModeL

variable {E K : Type*} [Field E] [CommRing K] {r : ℕ}

def zLoc (ι : E →+* K) (cj : K →+* K) (Dd : Fin (r + 1) → K) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of fun a b => Dd b * cj (Dd a) * ι (Z a b)

def lL (ι : E →+* K) (cj : K →+* K) (Dd : Fin (r + 1) → K) (a : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of fun i j => cj (Dd i) * ι (a i j) * Ring.inverse (cj (Dd j))

def ρL (ι : E →+* K) (Dd : Fin (r + 1) → K) (b : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of fun i j => Ring.inverse (Dd i) * ι ((-1) ^ (r - i.val) * b i j * (-1) ^ (r - j.val)) * Dd j

theorem zLoc_move (ι : E →+* K) (cj : K →+* K) (Dd : Fin (r + 1) → K) (hD : ∀ i, IsUnit (Dd i))
    (a b Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    zLoc ι cj Dd (ZhatOM (a * ZhatOM Z * b)) = lL ι cj Dd a * zLoc ι cj Dd Z * ρL ι Dd b := by
  have hc : ∀ i, cj (Dd i) * Ring.inverse (cj (Dd i)) = 1 := fun i => Ring.mul_inverse_cancel _ ((hD i).map cj)
  have hc' : ∀ i, Ring.inverse (cj (Dd i)) * cj (Dd i) = 1 := fun i => Ring.inverse_mul_cancel _ ((hD i).map cj)
  have hd : ∀ i, Dd i * Ring.inverse (Dd i) = 1 := fun i => Ring.mul_inverse_cancel _ (hD i)
  ext x y
  simp only [zLoc, lL, ρL, ZhatOM, Matrix.of_apply, Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  have e1 : Ring.inverse (cj (Dd c)) * cj (Dd c) = 1 := hc' c
  have e2 : Dd d * Ring.inverse (Dd d) = 1 := hd d
  set L0 := Dd y * cj (Dd x) * (ι ((-1) ^ (r - y.val)) * (ι (a x c) * (ι ((-1) ^ (r - d.val)) * ι (Z c d)) * ι (b d y)))
  linear_combination (-(L0 * (Dd d * Ring.inverse (Dd d)))) * e1 + (-L0) * e2

end ModeL

section ModeG

variable {E F K : Type*} [Field E] [Field F] [CommRing K] [Algebra F K] {r : ℕ}

def linG (e : K ≃ₐ[F] F × F) (q : F) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of fun a b => e.symm ((e (Zh a b)).1 / q, -((e (Zh b a)).2 / q))

def lG (e : K ≃ₐ[F] F × F) (ι : E →+* K) (Dd : Fin (r + 1) → K) (a b : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of fun i j => e.symm ((e (Dd i)).2 * (e (ι (a i j))).1 / (e (Dd j)).2,
    (e (ι ((-1) ^ (r - j.val) * b j i * (-1) ^ (r - i.val)))).2 * (e (Dd i)).2 / (e (Dd j)).2)

def ρG (e : K ≃ₐ[F] F × F) (ι : E →+* K) (Dd : Fin (r + 1) → K) (a b : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of fun i j => e.symm ((e (ι ((-1) ^ (r - i.val) * b i j * (-1) ^ (r - j.val)))).1 * (e (Dd j)).1 / (e (Dd i)).1,
    (e (ι (a j i))).2 * (e (Dd j)).1 / (e (Dd i)).1)

theorem linG_move (e : K ≃ₐ[F] F × F) (cj : K →+* K) (he : ∀ x, e (cj x) = (e x).swap) (ι : E →+* K)
    (Dd : Fin (r + 1) → K) (hx : ∀ i, (e (Dd i)).1 ≠ 0) (hy : ∀ i, (e (Dd i)).2 ≠ 0) (q : F) (hq : q ≠ 0)
    (a b Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    linG e q (zLoc ι cj Dd (ZhatOM (a * ZhatOM Z * b))) = lG e ι Dd a b * linG e q (zLoc ι cj Dd Z) * ρG e ι Dd a b := by
  ext x y
  apply e.injective
  simp only [linG, lG, ρG, zLoc, ZhatOM, Matrix.of_apply, Matrix.mul_apply, AlgEquiv.apply_symm_apply, map_sum,
    map_mul, he]
  ext
  · simp only [Prod.fst_sum, Prod.fst_mul, Prod.swap, Finset.sum_div, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
    have h1 := hy c
    have h2 := hx d
    first | (field_simp; done) | (field_simp; ring)
  · simp only [Prod.snd_sum, Prod.snd_mul, Prod.swap, Finset.sum_div, Finset.mul_sum, Finset.sum_mul, Prod.snd_neg,
      neg_div, mul_neg, neg_mul]
    rw [← Finset.sum_neg_distrib]
    simp only [← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
    have h1 := hy c
    have h2 := hx d
    first | (field_simp; done) | (field_simp; ring)

theorem constG (e : K ≃ₐ[F] F × F) (ι : E →+* K) (Dd : Fin (r + 1) → K) (hx : ∀ i, (e (Dd i)).1 ≠ 0)
    (hy : ∀ i, (e (Dd i)).2 ≠ 0) (a b : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (ha : IsLoUni a) (hb : IsUpUni b)
    (c : K) :
    lG e ι Dd a b * Matrix.single (Fin.last r) (Fin.last r) c * ρG e ι Dd a b =
      Matrix.single (Fin.last r) (Fin.last r) c := by
  ext x y
  rw [mul_single_mul]
  have hl : lG e ι Dd a b x (Fin.last r) = if x = Fin.last r then 1 else 0 := by
    apply e.injective
    simp only [lG, Matrix.of_apply, AlgEquiv.apply_symm_apply]
    by_cases hxl : x = Fin.last r
    · subst hxl
      rw [if_pos rfl, (ha _ _).2 rfl, (hb _ _).2 rfl]
      simp [Fin.val_last, div_self (hy _)]
    · rw [if_neg hxl, (ha _ _).1 (lt_of_le_of_ne (Fin.le_last x) hxl), (hb _ _).1 (lt_of_le_of_ne (Fin.le_last x) hxl)]
      simp
  have hr : ρG e ι Dd a b (Fin.last r) y = if y = Fin.last r then 1 else 0 := by
    apply e.injective
    simp only [ρG, Matrix.of_apply, AlgEquiv.apply_symm_apply]
    by_cases hyl : y = Fin.last r
    · subst hyl
      rw [if_pos rfl, (ha _ _).2 rfl, (hb _ _).2 rfl]
      simp [Fin.val_last, div_self (hx _)]
    · rw [if_neg hyl, (hb _ _).1 (lt_of_le_of_ne (Fin.le_last y) hyl), (ha _ _).1 (lt_of_le_of_ne (Fin.le_last y) hyl)]
      simp
  rw [hl, hr, Matrix.single_apply]
  by_cases hxl : x = Fin.last r <;> by_cases hyl : y = Fin.last r
  · subst hxl; subst hyl; simp
  · subst hxl; simp [hyl, Ne.symm hyl]
  · subst hyl; simp [hxl, Ne.symm hxl]
  · simp [hxl, hyl, Ne.symm hxl]

end ModeG

section Record

open Formalism.L2.SG.PairVal Formalism.L2.SG.CntLocal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (δ : ∀ p : PlF D, (D.s.atP p).Fp)
  (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)

def lOf (p : PlF D) (a b : MatR D) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  match (M p).split with
  | none => lL (D.s.atP p).ιE ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) (frFac δ p) a
  | some g => lG g.e (D.s.atP p).ιE (frFac δ p) a b

def ρOf (p : PlF D) (a b : MatR D) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep :=
  match (M p).split with
  | none => ρL (D.s.atP p).ιE (frFac δ p) b
  | some g => ρG g.e (D.s.atP p).ιE (frFac δ p) a b

theorem unitAt_ne (p : PlF D) : (uP p : D.host.E) ≠ 0 := by
  have h1 : (gpart p : ℚ) ≠ 0 := by
    unfold gpart; split_ifs
    · exact_mod_cast (D.host.g_prime 0).ne_zero
    · exact_mod_cast (D.host.g_prime 1).ne_zero
    · norm_num
  have h2 : (Lat.gS D : ℚ) ≠ 0 := by
    unfold Lat.gS
    push_cast
    exact mul_ne_zero (by exact_mod_cast (D.host.g_prime 0).ne_zero) (by exact_mod_cast (D.host.g_prime 1).ne_zero)
  unfold uP
  exact_mod_cast div_ne_zero h1 h2

theorem frFac_unit {p : PlF D} (hA : Agree δ M p) (i : Fin (D.R.rS + 1)) : IsUnit (frFac δ p i) := by
  unfold frFac
  rw [isUnit_ringInverse]
  refine IsUnit.pow _ (IsUnit.mul ?_ ?_)
  · exact (isUnit_iff_ne_zero.2 hA.2.1).map _
  · exact (isUnit_iff_ne_zero.2 (unitAt_ne p)).map _

theorem zhatLoc_eq (p : PlF D) (Z : MatZ D) :
    ZhatLoc M δ p Z = zLoc (D.s.atP p).ιE ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) (frFac δ p) Z := by
  ext a b; rfl

variable (u u' : D.what₂.Word)

theorem zzp_none {p : PlF D} (h : (M p).split = none) (Z : MatZ D) :
    ZZP (M := M) δ u u' p Z = zLoc (D.s.atP p).ιE ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) (frFac δ p) Z := by
  rw [← zhatLoc_eq]
  unfold ZZP Loc.HermSp.ZZplusOf
  rw [h]

theorem zzp_some {p : PlF D} {g : Loc.SplitG (M p).L} (h : (M p).split = some g) (Z : MatZ D) :
    ZZP (M := M) δ u u' p Z = linG g.e (g.q : (D.s.atP p).Fp)
        (zLoc (D.s.atP p).ιE ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) (frFac δ p) Z) -
      Matrix.single (Fin.last D.R.rS) (Fin.last D.R.rS)
        (g.e.symm (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp),
          (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp))) := by
  rw [← zhatLoc_eq]
  unfold ZZP Loc.HermSp.ZZplusOf
  rw [h]
  ext a b
  simp only [Matrix.of_apply, Matrix.sub_apply, linG, Matrix.single_apply]
  congr 1
  by_cases ha : a = Fin.last D.R.rS <;> by_cases hb : b = Fin.last D.R.rS <;> simp [ha, hb, eq_comm]

theorem split_units {p : PlF D} (hA : Agree δ M p) (g : Loc.SplitG (M p).L) (i : Fin (D.R.rS + 1)) :
    (g.e (frFac δ p i)).1 ≠ 0 ∧ (g.e (frFac δ p i)).2 ≠ 0 := by
  have hu := (frFac_unit δ M hA i).map g.e
  rw [Prod.isUnit_iff] at hu
  exact ⟨hu.1.ne_zero, hu.2.ne_zero⟩

theorem q_ne {p : PlF D} (g : Loc.SplitG (M p).L) : (g.q : (D.s.atP p).Fp) ≠ 0 := by
  intro h0
  apply g.q_irr.ne_zero
  exact Subtype.ext h0

theorem move {p : PlF D} (hA : Agree δ M p) (a b : MatR D) (ha : IsLoUni a) (hb : IsUpUni b) (Z : MatZ D) :
    ZZP (M := M) δ u u' p (ZhatOM (a * ZhatOM Z * b)) = lOf δ M p a b * ZZP (M := M) δ u u' p Z * ρOf δ M p a b := by
  cases h : (M p).split with
  | none =>
    simp only [lOf, ρOf, h]
    rw [zzp_none δ M u u' h, zzp_none δ M u u' h]
    exact zLoc_move _ _ _ (frFac_unit δ M hA) a b Z
  | some g =>
    simp only [lOf, ρOf, h]
    rw [zzp_some δ M u u' h, zzp_some δ M u u' h]
    have hx := fun i => (split_units δ M hA g i).1
    have hy := fun i => (split_units δ M hA g i).2
    rw [linG_move g.e _ g.e_cj _ _ hx hy _ (q_ne M g), Matrix.mul_sub, Matrix.sub_mul,
      constG g.e _ _ hx hy a b ha hb]

theorem zLoc_single {E K : Type*} [Field E] [CommRing K] {r : ℕ} (ι : E →+* K) (cj : K →+* K) (Dd : Fin (r + 1) → K)
    (i j : Fin (r + 1)) : zLoc ι cj Dd (Matrix.single i j 1) = Matrix.single i j (Dd j * cj (Dd i)) := by
  ext x y
  simp only [zLoc, Matrix.of_apply, Matrix.single_apply]
  by_cases h : i = x ∧ j = y
  · obtain ⟨rfl, rfl⟩ := h; simp
  · simp [h]

theorem zLoc_zero {E K : Type*} [Field E] [CommRing K] {r : ℕ} (ι : E →+* K) (cj : K →+* K) (Dd : Fin (r + 1) → K) :
    zLoc ι cj Dd (0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) = 0 := by
  ext x y; simp [zLoc]

theorem lOf_diag {p : PlF D} (hA : Agree δ M p) (a b : MatR D) (ha : IsLoUni a) (hb : IsUpUni b) (i) :
    lOf δ M p a b i i = 1 := by
  cases h : (M p).split with
  | none =>
    simp only [lOf, h, lL, Matrix.of_apply, (ha i i).2 rfl, map_one, mul_one]
    exact Ring.mul_inverse_cancel _ ((frFac_unit δ M hA i).map _)
  | some g =>
    simp only [lOf, h, lG, Matrix.of_apply, (ha i i).2 rfl, (hb i i).2 rfl]
    apply g.e.injective
    have := split_units δ M hA g i
    simp [div_self this.2, ← pow_add, ← two_mul, pow_mul]

theorem ρOf_diag {p : PlF D} (hA : Agree δ M p) (a b : MatR D) (ha : IsLoUni a) (hb : IsUpUni b) (i) :
    ρOf δ M p a b i i = 1 := by
  cases h : (M p).split with
  | none =>
    simp only [ρOf, h, ρL, Matrix.of_apply, (hb i i).2 rfl, mul_one]
    rw [← pow_add, ← two_mul, pow_mul]
    simp only [neg_one_sq, one_pow, map_one, mul_one]
    exact Ring.inverse_mul_cancel _ (frFac_unit δ M hA i)
  | some g =>
    simp only [ρOf, h, ρG, Matrix.of_apply, (ha i i).2 rfl, (hb i i).2 rfl]
    apply g.e.injective
    have := split_units δ M hA g i
    simp [div_self this.1, ← pow_add, ← two_mul, pow_mul]

theorem linG_zero {F K : Type*} [Field F] [CommRing K] [Algebra F K] {r : ℕ} (e : K ≃ₐ[F] F × F) (q : F) :
    linG e q (0 : Matrix (Fin (r + 1)) (Fin (r + 1)) K) = 0 := by
  ext a b
  simp only [linG, Matrix.of_apply, Matrix.zero_apply, map_zero, Prod.fst_zero, Prod.snd_zero, zero_div, neg_zero]
  exact map_zero e.symm

def cx {F K : Type*} [Field F] [CommRing K] [Algebra F K] {r : ℕ} (e : K ≃ₐ[F] F × F) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) F := A.map ((RingHom.fst F F).comp (e : K →+* F × F))

def cy {F K : Type*} [Field F] [CommRing K] [Algebra F K] {r : ℕ} (e : K ≃ₐ[F] F × F) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) F := A.map ((RingHom.snd F F).comp (e : K →+* F × F))

theorem cx_mul {F K : Type*} [Field F] [CommRing K] [Algebra F K] {r : ℕ} (e : K ≃ₐ[F] F × F)
    (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : cx e (A * B) = cx e A * cx e B := Matrix.map_mul

theorem cy_mul {F K : Type*} [Field F] [CommRing K] [Algebra F K] {r : ℕ} (e : K ≃ₐ[F] F × F)
    (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) K) : cy e (A * B) = cy e A * cy e B := Matrix.map_mul

theorem eq_of_cxy {F K : Type*} [Field F] [CommRing K] [Algebra F K] {r : ℕ} (e : K ≃ₐ[F] F × F)
    {A B : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (hx : cx e A = cx e B) (hy : cy e A = cy e B) : A = B := by
  ext i j
  apply e.injective
  have h1 := congrFun (congrFun hx i) j
  have h2 := congrFun (congrFun hy i) j
  simp only [cx, cy, Matrix.map_apply, RingHom.comp_apply, RingHom.coe_fst, RingHom.coe_snd] at h1 h2
  exact Prod.ext h1 h2

theorem uniq {p : PlF D} (hA : Agree δ M p) (a b : MatR D) (ha : IsLoUni a) (hb : IsUpUni b)
    (l ρ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep) (hl : ∀ i, l i i = 1) (hρ : ∀ i, ρ i i = 1)
    (h : ∀ Z : MatZ D, ZZP (M := M) δ u u' p (ZhatOM (a * ZhatOM Z * b)) = l * ZZP (M := M) δ u u' p Z * ρ) :
    l = lOf δ M p a b ∧ ρ = ρOf δ M p a b := by
  have hm := fun Z => (h Z).symm.trans (move δ M u u' hA a b ha hb Z)
  cases hs : (M p).split with
  | none =>
    have key : ∀ i j, l * Matrix.single i j (frFac δ p j * (M p).L.cj (frFac δ p i)) * ρ =
        lOf δ M p a b * Matrix.single i j (frFac δ p j * (M p).L.cj (frFac δ p i)) * ρOf δ M p a b := by
      intro i j
      have := hm (Matrix.single i j 1)
      rw [zzp_none δ M u u' hs, zLoc_single] at this
      exact this
    exact pair_unique _ _ _ _ (ρOf_diag δ M hA a b ha hb) hρ (lOf_diag δ M hA a b ha hb) hl _
      (fun i j => (frFac_unit δ M hA j).mul ((frFac_unit δ M hA i).map _)) key
  | some g =>
    set C := Matrix.single (Fin.last D.R.rS) (Fin.last D.R.rS)
        (g.e.symm (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp),
          (((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (g.q : (D.s.atP p).Fp))) with hC
    set Lz := fun Z : MatZ D => linG g.e (g.q : (D.s.atP p).Fp)
        (zLoc (D.s.atP p).ιE ((M p).L.cj : (D.s.atP p).Ep →+* (D.s.atP p).Ep) (frFac δ p) Z) with hLz
    have hm' : ∀ Z, l * (Lz Z - C) * ρ = lOf δ M p a b * (Lz Z - C) * ρOf δ M p a b := by
      intro Z; have := hm Z; rw [zzp_some δ M u u' hs] at this; exact this
    have h0 := hm' 0
    simp only [hLz, zLoc_zero, linG_zero, zero_sub, Matrix.mul_neg, Matrix.neg_mul, neg_inj] at h0
    have hL : ∀ Z, l * Lz Z * ρ = lOf δ M p a b * Lz Z * ρOf δ M p a b := by
      intro Z
      have := hm' Z
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_mul, h0] at this
      exact sub_left_injective this
    have hx := fun i => (split_units δ M hA g i).1
    have hy := fun i => (split_units δ M hA g i).2
    have hq := q_ne M g
    have Lx : ∀ i j, cx g.e (Lz (Matrix.single i j 1)) = Matrix.single i j
        ((g.e (frFac δ p j)).1 * (g.e (frFac δ p i)).2 / (g.q : (D.s.atP p).Fp)) := by
      intro i j
      ext x y
      simp only [cx, hLz, linG, zLoc_single, Matrix.map_apply, Matrix.of_apply, RingHom.comp_apply, RingHom.coe_fst,
        RingHom.coe_coe, AlgEquiv.apply_symm_apply, Matrix.single_apply]
      by_cases hxy : i = x ∧ j = y
      · obtain ⟨rfl, rfl⟩ := hxy; simp [g.e_cj]
      · simp [hxy]
    have Ly : ∀ i j, cy g.e (Lz (Matrix.single j i 1)) = Matrix.single i j
        (-((g.e (frFac δ p i)).2 * (g.e (frFac δ p j)).1 / (g.q : (D.s.atP p).Fp))) := by
      intro i j
      ext x y
      simp only [cy, hLz, linG, zLoc_single, Matrix.map_apply, Matrix.of_apply, RingHom.comp_apply, RingHom.coe_snd,
        RingHom.coe_coe, AlgEquiv.apply_symm_apply, Matrix.single_apply]
      by_cases hxy : i = x ∧ j = y
      · obtain ⟨rfl, rfl⟩ := hxy; simp [g.e_cj]
      · have : ¬ (j = y ∧ i = x) := fun h' => hxy ⟨h'.2, h'.1⟩
        simp [hxy, this]
    have diagx : ∀ (A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep), (∀ i, A i i = 1) →
        ∀ i, cx g.e A i i = 1 := by
      intro A hA' i; simp [cx, hA' i]
    have diagy : ∀ (A : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep), (∀ i, A i i = 1) →
        ∀ i, cy g.e A i i = 1 := by
      intro A hA' i; simp [cy, hA' i]
    have ux : ∀ i j, IsUnit ((g.e (frFac δ p j)).1 * (g.e (frFac δ p i)).2 / (g.q : (D.s.atP p).Fp)) :=
      fun i j => isUnit_iff_ne_zero.2 (div_ne_zero (mul_ne_zero (hx j) (hy i)) hq)
    have uy : ∀ i j, IsUnit (-((g.e (frFac δ p i)).2 * (g.e (frFac δ p j)).1 / (g.q : (D.s.atP p).Fp))) :=
      fun i j => isUnit_iff_ne_zero.2 (neg_ne_zero.2 (div_ne_zero (mul_ne_zero (hy i) (hx j)) hq))
    have kx : ∀ i j, cx g.e l * Matrix.single i j ((g.e (frFac δ p j)).1 * (g.e (frFac δ p i)).2 / (g.q : (D.s.atP p).Fp)) *
        cx g.e ρ = cx g.e (lOf δ M p a b) *
          Matrix.single i j ((g.e (frFac δ p j)).1 * (g.e (frFac δ p i)).2 / (g.q : (D.s.atP p).Fp)) *
            cx g.e (ρOf δ M p a b) := by
      intro i j
      have := congrArg (cx g.e) (hL (Matrix.single i j 1))
      rwa [cx_mul, cx_mul, cx_mul, cx_mul, Lx] at this
    have ky : ∀ i j, cy g.e l * Matrix.single i j (-((g.e (frFac δ p i)).2 * (g.e (frFac δ p j)).1 / (g.q : (D.s.atP p).Fp))) *
        cy g.e ρ = cy g.e (lOf δ M p a b) *
          Matrix.single i j (-((g.e (frFac δ p i)).2 * (g.e (frFac δ p j)).1 / (g.q : (D.s.atP p).Fp))) *
            cy g.e (ρOf δ M p a b) := by
      intro i j
      have := congrArg (cy g.e) (hL (Matrix.single j i 1))
      rwa [cy_mul, cy_mul, cy_mul, cy_mul, Ly] at this
    obtain ⟨lx, ρx⟩ := pair_unique _ _ _ _ (diagx _ (ρOf_diag δ M hA a b ha hb)) (diagx _ hρ)
      (diagx _ (lOf_diag δ M hA a b ha hb)) (diagx _ hl) _ ux kx
    obtain ⟨ly, ρy⟩ := pair_unique _ _ _ _ (diagy _ (ρOf_diag δ M hA a b ha hb)) (diagy _ hρ)
      (diagy _ (lOf_diag δ M hA a b ha hb)) (diagy _ hl) _ uy ky
    exact ⟨eq_of_cxy g.e lx ly, eq_of_cxy g.e ρx ρy⟩

theorem mem_stabIntSet_iff (hA : ∀ p, Agree δ M p) (w : Formalism.MainNotions.S.Point D.host.E (D.R.rS + 1)) (a : GLR D) :
    a ∈ stabIntSet D u u' δ M w ↔ IsLoUni (a : MatR D) ∧ ∃ b : MatR D, IsUpUni b ∧
      (a : MatR D) * ptMat w * b = ptMat w ∧
      ∀ p, Formalism.MainNotions.S.TieN.IntLow (M p) (lOf δ M p a b) ∧ Formalism.MainNotions.S.TieN.IntUp (M p) (ρOf δ M p a b) := by
  constructor
  · rintro ⟨ha, b, hb, hW, hp⟩
    refine ⟨ha, b, hb, hW, fun p => ?_⟩
    obtain ⟨l, ρ, hl, hρ, hZ⟩ := hp p
    obtain ⟨e1, e2⟩ := uniq δ M u u' (hA p) a b ha hb l ρ (fun i => hl.1 i) (fun i => hρ.1 i) hZ
    rw [← e1, ← e2]
    exact ⟨hl, hρ⟩
  · rintro ⟨ha, b, hb, hW, hp⟩
    exact ⟨ha, b, hb, hW, fun p => ⟨_, _, (hp p).1, (hp p).2, move δ M u u' (hA p) a b ha hb⟩⟩

end Record

end Formalism.L2.SG.Pf.StabShape
