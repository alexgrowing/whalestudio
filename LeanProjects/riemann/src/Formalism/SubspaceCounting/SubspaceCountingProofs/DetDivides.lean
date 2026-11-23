import Formalism.SubspaceCounting.StatementW

noncomputable section
open scoped BigOperators
open Polynomial

namespace Formalism.G0.DetDividesP
open Formalism.G0

variable {L : Type} [Field L] {r : ℕ}

lemma lastIdx_iff (hr : 0 < r) (a : Fin r) : a.val + 1 = r ↔ a = ⟨r - 1, by omega⟩ := by
  constructor
  · intro h; ext; simp; omega
  · intro h; subst h; simp; omega

lemma prod_lastX (hr : 0 < r) {R : Type} [CommRing R] (u : R) :
    (∏ a : Fin r, if a.val + 1 = r then u else 1) = u := by
  have : (fun a : Fin r => if a.val + 1 = r then u else 1) =
      fun a => if (⟨r - 1, by omega⟩ : Fin r) = a then u else 1 := by
    funext a; simp only [lastIdx_iff hr, eq_comm]
  rw [this, Finset.prod_ite_eq]; simp

lemma det_msMat (hr : 0 < r) (g : GL (Fin r) L) : (msMat g).det = X := by
  unfold msMat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, prod_lastX hr]
  have h1 : (g.1.map C).det * (((g⁻¹ : GL (Fin r) L)).1.map C).det = 1 := by
    rw [← Matrix.det_mul, ← Matrix.map_mul]
    simp
  calc (g.1.map C).det * X * (((g⁻¹ : GL (Fin r) L)).1.map C).det
      = ((g.1.map C).det * (((g⁻¹ : GL (Fin r) L)).1.map C).det) * X := by ring
    _ = X := by rw [h1, one_mul]

def nMat (g : GL (Fin r) L) : Matrix (Fin r) (Fin r) L[X] :=
  (g.1.map C) * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then 1 else X) *
    ((g⁻¹ : GL (Fin r) L).1.map C)

lemma msMat_mul_nMat (g : GL (Fin r) L) : msMat g * nMat g = (X : L[X]) • (1 : Matrix (Fin r) (Fin r) L[X]) := by
  unfold msMat nMat
  have hgi : ((g⁻¹ : GL (Fin r) L).1.map C) * (g.1.map C) = 1 := by
    rw [← Matrix.map_mul]; simp
  have hgg : (g.1.map C) * ((g⁻¹ : GL (Fin r) L).1.map C) = 1 := by
    rw [← Matrix.map_mul]; simp
  have hdd : Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then X else 1) *
      Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then 1 else X) = (X : L[X]) • (1 : Matrix (Fin r) (Fin r) L[X]) := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
    congr 1; funext a; split_ifs <;> simp
  calc (g.1.map C) * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then X else 1) *
        ((g⁻¹ : GL (Fin r) L).1.map C) * ((g.1.map C) * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then 1 else X) *
    ((g⁻¹ : GL (Fin r) L).1.map C))
      = (g.1.map C) * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then X else 1) *
        (((g⁻¹ : GL (Fin r) L).1.map C) * (g.1.map C)) * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then 1 else X) *
    ((g⁻¹ : GL (Fin r) L).1.map C) := by simp only [Matrix.mul_assoc]
    _ = (g.1.map C) * ((X : L[X]) • (1 : Matrix (Fin r) (Fin r) L[X])) * ((g⁻¹ : GL (Fin r) L).1.map C) := by
        rw [hgi, Matrix.mul_one, Matrix.mul_assoc (g.1.map C), hdd]
    _ = (X : L[X]) • (1 : Matrix (Fin r) (Fin r) L[X]) := by
        rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hgg]

lemma msDualMat_eq (g : GL (Fin r) L) : msDualMat g = (nMat g).transpose := rfl

lemma msDualMat_mul_msMat_transpose (g : GL (Fin r) L) :
    msDualMat g * (msMat g).transpose = (X : L[X]) • (1 : Matrix (Fin r) (Fin r) L[X]) := by
  rw [msDualMat_eq, ← Matrix.transpose_mul, msMat_mul_nMat]; simp

lemma msMat_eval0 (g : GL (Fin r) L) :
    (msMat g).map (Polynomial.evalRingHom 0) =
      g.1 * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then (0 : L) else 1) * (g⁻¹ : GL (Fin r) L).1 := by
  unfold msMat
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_map, Matrix.map_map, Matrix.diagonal_map (by simp)]
  congr 2
  · ext i j; simp
  · congr 1; funext a; split_ifs <;> simp
  · ext i j; simp

end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators
open Polynomial

namespace Formalism.G0.DetDividesP
open Formalism.G0

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

open Classical in

def ptA {L : Type} [Field L] (A : Fin r → ι) (g : GL (Fin r) L) (x : ι × Fin r → L) : ι × Fin r → L[X] :=
  fun p => if p.1 ∈ Set.range A then ∑ b, msMat g p.2 b * C (x (p.1, b)) else C (x p)

def Red (A : Fin r → ι) (G : MvPolynomial (ι × Fin r) K) (n : ℕ) : Prop :=
  ∀ (L : Type) [Field L] [Algebra K L] (g : GL (Fin r) L) (x : ι × Fin r → L),
    MvPolynomial.aeval x (detLetters (K := K) A) ≠ 0 →
      (X : L[X]) ^ n ∣ MvPolynomial.aeval (ptA A g x) G

lemma aeval_detLetters {B : Type} [CommRing B] [Algebra K B] (A : Fin r → ι) (y : ι × Fin r → B) :
    MvPolynomial.aeval y (detLetters (K := K) A) = (Matrix.of fun l a => y (A l, a)).det := by
  unfold detLetters
  rw [AlgHom.map_det]; congr 1; ext l a; simp

lemma aeval_ptA_det (hr : 0 < r) {L : Type} [Field L] [Algebra K L] (A : Fin r → ι) (g : GL (Fin r) L)
    (x : ι × Fin r → L) :
    MvPolynomial.aeval (ptA A g x) (detLetters (K := K) A) =
      C (MvPolynomial.aeval x (detLetters (K := K) A)) * X := by
  rw [aeval_detLetters, aeval_detLetters]
  have : (Matrix.of fun l a => ptA A g x (A l, a)) =
      ((Matrix.of fun l b => x (A l, b)).map C) * (msMat g).transpose := by
    ext l a
    simp [ptA, Matrix.mul_apply, mul_comm]
  rw [this, Matrix.det_mul, Matrix.det_transpose, det_msMat hr, RingHom.map_det]
  rfl

lemma red_of_mul (hr : 0 < r) (A : Fin r → ι) (G' : MvPolynomial (ι × Fin r) K) (n : ℕ)
    (h : Red A (detLetters (K := K) A * G') (n + 1)) : Red A G' n := by
  intro L _ _ g x hx
  have h1 := h L g x hx
  rw [map_mul, aeval_ptA_det hr, pow_succ, mul_comm (C _) X, mul_assoc, mul_comm (X ^ n) X] at h1
  have h2 := (mul_dvd_mul_iff_left (X_ne_zero : (X : L[X]) ≠ 0)).mp h1
  exact (IsUnit.dvd_mul_left (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hx))).mp h2

end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators
open Polynomial

namespace Formalism.G0.DetDividesP
open Formalism.G0

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

lemma aeval_weighted_scale {σ : Type} {B : Type} [CommSemiring B] [Algebra K B] (w : σ → ℕ)
    {φ : MvPolynomial σ K} {n : ℕ} (hφ : MvPolynomial.IsWeightedHomogeneous w φ n) (t : B) (z : σ → B) :
    MvPolynomial.aeval (fun p => t ^ (w p) * z p) φ = t ^ n * MvPolynomial.aeval z φ := by
  conv_lhs => rw [φ.as_sum]
  conv_rhs => rw [φ.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
  have hw : Finsupp.weight w m = n := hφ (MvPolynomial.mem_support_iff.mp hm)
  have : (m.prod fun p k => (t ^ w p * z p) ^ k) = t ^ n * m.prod fun p k => z p ^ k := by
    simp only [mul_pow, Finsupp.prod_mul]
    congr 1
    rw [← hw, Finsupp.weight_apply, Finsupp.prod, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_mul, smul_eq_mul, mul_comm]
  rw [this]; ring

lemma aeval_letter_scale {B : Type} [CommSemiring B] [Algebra K B] {G : MvPolynomial (ι × Fin r) K}
    {d : ι → ℕ} (hG : MultiHom G d) (i : ι) (t : B) (z : ι × Fin r → B) :
    MvPolynomial.aeval (fun p => if p.1 = i then t * z p else z p) G = t ^ d i * MvPolynomial.aeval z G := by
  rw [← aeval_weighted_scale _ (hG i) t z]
  have : (fun p : ι × Fin r => if p.1 = i then t * z p else z p) =
      fun p => t ^ (if p.1 = i then 1 else 0) * z p := by
    funext p; split_ifs <;> simp
  rw [this]

lemma aeval_set_scale {B : Type} [CommSemiring B] [Algebra K B] {G : MvPolynomial (ι × Fin r) K}
    {d : ι → ℕ} (hG : MultiHom G d) (U : Finset ι) (t : B) (z : ι × Fin r → B) :
    MvPolynomial.aeval (fun p => if p.1 ∈ U then t * z p else z p) G =
      t ^ (∑ i ∈ U, d i) * MvPolynomial.aeval z G := by
  induction U using Finset.induction_on with
  | empty => simp
  | insert i U hi ih =>
    have : (fun p : ι × Fin r => if p.1 ∈ insert i U then t * z p else z p) =
        fun p => if p.1 = i then t * (if p.1 ∈ U then t * z p else z p)
          else (if p.1 ∈ U then t * z p else z p) := by
      funext p
      by_cases h1 : p.1 = i
      · simp [h1, hi]
      · simp [h1, Finset.mem_insert]
    rw [this, aeval_letter_scale hG, ih, Finset.sum_insert hi, pow_add]; ring

lemma sum_sum_mat {R : Type} [CommSemiring R] (M N : Matrix (Fin r) (Fin r) R) (v : Fin r → R) (a : Fin r) :
    (∑ b, M a b * ∑ c, N b c * v c) = ∑ c, (M * N) a c * v c := by
  simp only [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

lemma sum_smul_one {R : Type} [CommSemiring R] (t : R) (v : Fin r → R) (a : Fin r) :
    (∑ c, ((t • (1 : Matrix (Fin r) (Fin r) R)) a c) * v c) = t * v a := by
  simp [Matrix.smul_apply, Matrix.one_apply]

end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators
open Polynomial

namespace Formalism.G0.DetDividesP
open Formalism.G0

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

lemma sum_split (vec : ι → Bool) (S : Finset ι) (A : Fin r → ι) (d : ι → ℕ)
    (hAS : ∀ l, A l ∈ S ∧ vec (A l) = true) :
    (∑ i ∈ S.filter (fun i => i ∉ Set.range A), d i) =
      (∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) +
        ∑ i ∈ S.filter (fun i => vec i = false), d i := by
  rw [← Finset.sum_filter_add_sum_filter_not (S.filter (fun i => i ∉ Set.range A)) (fun i => vec i = true)]
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i; simp [Finset.mem_filter]; tauto
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i
    simp only [Finset.mem_filter, Bool.not_eq_true]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩
      refine ⟨⟨h1, ?_⟩, h3⟩
      rintro ⟨l, rfl⟩
      have := (hAS l).2; simp_all

theorem red_of_valGE (_hr : 0 < r) (vec : ι → Bool) (S : Finset ι) (A : Fin r → ι) (d : ι → ℕ)
    (G : MvPolynomial (ι × Fin r) K) (th : ℕ)
    (hAS : ∀ l, A l ∈ S ∧ vec (A l) = true) (hG : MultiHom G d) (hV : ValGE vec S d G th)
    (hB : (∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) < th) :
    Red A G (th - ∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) := by
  classical
  intro L _ _ g x hx
  have hv := hV L g
  let y : ι × Fin r → L[X] := fun p =>
    if p.1 ∈ S then
      (if vec p.1 then
        (if p.1 ∈ Set.range A then C (x p) else ∑ c, nMat g p.2 c * C (x (p.1, c)))
       else ∑ c, (msMat g).transpose p.2 c * C (x (p.1, c)))
    else C (x p)
  let ev : MvPolynomial (ι × Fin r) L[X] →ₐ[K] L[X] := (MvPolynomial.aeval y).restrictScalars K
  have h1 := map_dvd ev hv
  have hC : ev (MvPolynomial.C (X ^ (th + ∑ i ∈ S.filter (fun i => vec i = false), d i))) =
      X ^ (th + ∑ i ∈ S.filter (fun i => vec i = false), d i) := by
    simp [ev]
  have hsub : ev (substS (K := K) vec S g G) = MvPolynomial.aeval
      (fun p => if p.1 ∈ S.filter (fun i => i ∉ Set.range A) then X * ptA A g x p else ptA A g x p) G := by
    unfold substS
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
    refine congrArg (fun f => MvPolynomial.aeval f G) ?_
    funext p
    obtain ⟨i, a⟩ := p
    have hev : ∀ (M : Matrix (Fin r) (Fin r) L[X]),
        ev (∑ b, MvPolynomial.C (M a b) * MvPolynomial.X (i, b)) = ∑ b, M a b * y (i, b) := by
      intro M
      simp only [ev, map_sum, map_mul, AlgHom.restrictScalars_apply, MvPolynomial.aeval_C,
        MvPolynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply]
    by_cases hS : i ∈ S
    · by_cases hvi : vec i = true
      · simp only [if_pos hS, if_pos hvi]
        rw [hev]
        by_cases hA : i ∈ Set.range A
        · have hy : ∀ b, y (i, b) = C (x (i, b)) := fun b => by
            simp only [y, if_pos hS, if_pos hvi, if_pos hA]
          have hU : i ∉ S.filter (fun i => i ∉ Set.range A) := by
            simp only [Finset.mem_filter, hA, not_true_eq_false, and_false, not_false_eq_true]
          simp only [hy, if_neg hU, ptA, if_pos hA]
        · have hy : ∀ b, y (i, b) = ∑ c, nMat g b c * C (x (i, c)) := fun b => by
            simp only [y, if_pos hS, if_pos hvi, if_neg hA]
          have hU : i ∈ S.filter (fun i => i ∉ Set.range A) := by
            simp only [Finset.mem_filter, hA, hS, not_false_eq_true, and_self]
          simp only [hy, if_pos hU, ptA, if_neg hA]
          rw [sum_sum_mat, msMat_mul_nMat, sum_smul_one]
      · have hA : i ∉ Set.range A := by
          rintro ⟨l, rfl⟩; exact hvi (hAS l).2
        simp only [if_pos hS, if_neg hvi]
        rw [hev]
        have hy : ∀ b, y (i, b) = ∑ c, (msMat g).transpose b c * C (x (i, c)) := fun b => by
          simp only [y, if_pos hS, if_neg hvi]
        have hU : i ∈ S.filter (fun i => i ∉ Set.range A) := by
          simp only [Finset.mem_filter, hA, hS, not_false_eq_true, and_self]
        simp only [hy, if_pos hU, ptA, if_neg hA]
        rw [sum_sum_mat, msDualMat_mul_msMat_transpose, sum_smul_one]
    · have hA : i ∉ Set.range A := by
        rintro ⟨l, rfl⟩; exact hS (hAS l).1
      have hU : i ∉ S.filter (fun i => i ∉ Set.range A) := by
        simp only [Finset.mem_filter, hS, false_and, not_false_eq_true]
      simp only [if_neg hS, if_neg hU, ptA, if_neg hA, ev, AlgHom.restrictScalars_apply,
        MvPolynomial.aeval_X, y]
  rw [hC, hsub, aeval_set_scale hG, sum_split vec S A d hAS] at h1
  have he : th + ∑ i ∈ S.filter (fun i => vec i = false), d i =
      ((∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) +
        ∑ i ∈ S.filter (fun i => vec i = false), d i) +
      (th - ∑ i ∈ S.filter (fun i => vec i = true ∧ i ∉ Set.range A), d i) := by omega
  rw [he, pow_add] at h1
  exact (mul_dvd_mul_iff_left (pow_ne_zero _ X_ne_zero)).mp h1

end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators

namespace Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

lemma not_mem_vars_of_degreeOf {σ : Type} {p : MvPolynomial σ K} {x : σ} (h : degreeOf x p = 0) :
    x ∉ p.vars := by
  intro hx
  rw [mem_vars_iff_mem_support] at hx
  obtain ⟨d, hd, hxd⟩ := hx
  have h1 := Finset.le_sup (f := fun m : σ →₀ ℕ => m x) hd
  rw [← degreeOf_eq_sup, h] at h1
  rw [Finsupp.mem_support_iff] at hxd
  exact hxd (by simpa using h1)

lemma degreeOf_eq_zero_of_dvd {σ : Type} {p f : MvPolynomial σ K} (x : σ) (hpf : p ∣ f) (hf : f ≠ 0)
    (h : degreeOf x f = 0) : degreeOf x p = 0 := by
  obtain ⟨q, rfl⟩ := hpf
  have hp : p ≠ 0 := left_ne_zero_of_mul hf
  have hq : q ≠ 0 := right_ne_zero_of_mul hf
  rw [degreeOf_mul_eq hp hq] at h
  omega

lemma degreeOf_det_eq_zero {σ : Type} (M : Matrix (Fin r) (Fin r) (MvPolynomial σ K)) (x : σ)
    (h : ∀ i j, degreeOf x (M i j) = 0) : degreeOf x M.det = 0 := by
  rw [Matrix.det_apply]
  apply Nat.eq_zero_of_le_zero
  refine (degreeOf_sum_le _ _ _).trans (Finset.sup_le fun σ' _ => ?_)
  rw [Units.smul_def, zsmul_eq_mul, ← map_intCast (C : K →+* MvPolynomial σ K)]
  refine (degreeOf_C_mul_le _ _ _).trans ?_
  refine (degreeOf_prod_le _ _ _).trans ?_
  simp [h]

lemma isUnit_of_degreeOf_eq_zero {σ : Type} {p : MvPolynomial σ K} (hp : p ≠ 0)
    (h : ∀ x, degreeOf x p = 0) : IsUnit p := by
  have hv : p.vars = ∅ := by
    ext x; simp only [Finset.notMem_empty, iff_false]; exact not_mem_vars_of_degreeOf (h x)
  rw [vars_eq_empty_iff_eq_C] at hv
  rw [hv] at hp ⊢
  have : coeff 0 p ≠ 0 := fun h0 => hp (by rw [h0, map_zero])
  exact (isUnit_iff_ne_zero.mpr this).map C

end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators

namespace Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

def Tm (K : Type) [Field K] (A : Fin r → ι) : Matrix (Fin r) (Fin r) (MvPolynomial ((ι × Fin r) ⊕ ι) K) :=
  Matrix.of fun l b => X (Sum.inl (A l, b))

def Wv (K : Type) [Field K] (A : Fin r → ι) : Fin r → MvPolynomial ((ι × Fin r) ⊕ ι) K :=
  fun l => X (Sum.inr (A l))

open Classical in

def evPerm (A : Fin r → ι) (τ : Equiv.Perm (Fin r)) : MvPolynomial ((ι × Fin r) ⊕ ι) K →ₐ[K] K :=
  aeval (Sum.elim (fun q => if h : ∃ l, A l = q.1 then (if q.2 = τ (Classical.choose h) then 1 else 0) else 0)
    (fun _ => 0))

lemma evPerm_Tm (A : Fin r → ι) (hA : Function.Injective A) (τ : Equiv.Perm (Fin r)) :
    (evPerm (K := K) A τ).mapMatrix (Tm K A) = τ.permMatrix K := by
  ext l b
  have h : ∃ l', A l' = A l := ⟨l, rfl⟩
  have hc : Classical.choose h = l := hA (Classical.choose_spec h)
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Tm, Matrix.of_apply, evPerm, aeval_X,
    Sum.elim_inl, dif_pos h, hc]
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, eq_comm]

lemma sign_cast_ne_zero (τ : Equiv.Perm (Fin r)) : ((Equiv.Perm.sign τ : ℤ) : K) ≠ 0 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]

lemma det_Tm_ne_zero (A : Fin r → ι) (hA : Function.Injective A) : (Tm K A).det ≠ 0 := by
  intro h
  have := congrArg (evPerm (K := K) A 1) h
  rw [AlgHom.map_det, evPerm_Tm A hA, Matrix.det_permutation, map_zero] at this
  exact sign_cast_ne_zero (K := K) 1 this

lemma adj_Tm_ne_zero (A : Fin r → ι) (hA : Function.Injective A) (lst l : Fin r) :
    (Tm K A).adjugate lst l ≠ 0 := by
  classical
  intro h
  rw [Matrix.adjugate_apply] at h
  have := congrArg (evPerm (K := K) A (Equiv.swap l lst)) h
  have hm : (evPerm (K := K) A (Equiv.swap l lst)).mapMatrix ((Tm K A).updateRow l (Pi.single lst 1)) =
      (Equiv.swap l lst).permMatrix K := by
    ext i j
    have hT := congrFun (congrFun (evPerm_Tm (K := K) A hA (Equiv.swap l lst)) i) j
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply] at hT
    by_cases hi : i = l
    · subst hi
      simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_self]
      simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Equiv.swap_apply_left,
        Option.mem_def, Option.some.injEq]
      by_cases hj : j = lst
      · subst hj; simp
      · simp [hj, Ne.symm hj]
    · simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateRow_ne hi]
      exact hT
  rw [AlgHom.map_det, hm, Matrix.det_permutation, map_zero] at this
  exact sign_cast_ne_zero (K := K) _ this

end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators

namespace Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

def rho (K : Type) [Field K] (A : Fin r → ι) (l : Fin r) :
    MvPolynomial ((ι × Fin r) ⊕ ι) K →ₐ[K] MvPolynomial ((ι × Fin r) ⊕ ι) K :=
  aeval (Sum.elim (fun q => X (Sum.inl q)) (fun i => if i = A l then 1 else 0))

lemma rho_Tm (A : Fin r → ι) (l : Fin r) : (rho K A l).mapMatrix (Tm K A) = Tm K A := by
  ext i j; simp [rho, Tm]

lemma rho_adj (A : Fin r → ι) (l i j : Fin r) : rho K A l ((Tm K A).adjugate i j) = (Tm K A).adjugate i j := by
  have := RingHom.map_adjugate (rho K A l).toRingHom (Tm K A)
  have h2 : (rho K A l).toRingHom.mapMatrix (Tm K A) = Tm K A := rho_Tm A l
  rw [h2] at this
  exact congrFun (congrFun this i) j

lemma rho_cc (A : Fin r → ι) (hA : Function.Injective A) (lst l : Fin r) :
    rho K A l (((Tm K A).adjugate.mulVec (Wv K A)) lst) = (Tm K A).adjugate lst l := by
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, rho_adj]
  have : ∀ j, rho K A l (Wv K A j) = if j = l then 1 else 0 := by
    intro j; simp [rho, Wv, hA.eq_iff]
  simp only [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma rho_fix (A : Fin r → ι) (l : Fin r) {p : MvPolynomial ((ι × Fin r) ⊕ ι) K}
    (hp : ∀ i, degreeOf (Sum.inr i) p = 0) : rho K A l p = p := by
  have hsub : (p.vars : Set ((ι × Fin r) ⊕ ι)) ⊆ Set.range Sum.inl := by
    intro x hx
    cases x with
    | inl q => exact ⟨q, rfl⟩
    | inr i => exact absurd hx (not_mem_vars_of_degreeOf (hp i))
  obtain ⟨q, rfl⟩ := exists_rename_eq_of_vars_subset_range p Sum.inl Sum.inl_injective hsub
  rw [rho, aeval_rename]
  have : ((Sum.elim (fun q => (X (Sum.inl q) : MvPolynomial ((ι × Fin r) ⊕ ι) K))
      (fun i => if i = A l then 1 else 0)) ∘ Sum.inl) = fun q => X (Sum.inl q) := by
    funext q; simp
  rw [this]
  clear hp hsub this
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp' hq' => rw [map_add, map_add, hp', hq']
  | mul_X p n hp' => rw [map_mul, map_mul, hp', aeval_X, rename_X]

lemma coprime_det_cc (A : Fin r → ι) (hA : Function.Injective A) (lst : Fin r) :
    IsRelPrime (Tm K A).det (((Tm K A).adjugate.mulVec (Wv K A)) lst) := by
  intro p hpD hpc
  have hD := det_Tm_ne_zero (K := K) A hA
  have hp0 : p ≠ 0 := by rintro rfl; exact hD (zero_dvd_iff.mp hpD)
  have hinr : ∀ i, degreeOf (Sum.inr i) p = 0 := fun i =>
    degreeOf_eq_zero_of_dvd _ hpD hD (degreeOf_det_eq_zero _ _ fun a b => by
      simp [Tm, degreeOf_X_of_ne])
  have hrow : ∀ l b, degreeOf (Sum.inl (A l, b)) p = 0 := by
    intro l b
    have h1 : p ∣ (Tm K A).adjugate lst l := by
      have := map_dvd (rho K A l) hpc
      rwa [rho_fix A l hinr, rho_cc A hA] at this
    refine degreeOf_eq_zero_of_dvd _ h1 (adj_Tm_ne_zero A hA lst l) ?_
    rw [Matrix.adjugate_apply]
    refine degreeOf_det_eq_zero _ _ fun i j => ?_
    by_cases hi : i = l
    · subst hi
      rw [Matrix.updateRow_self, Pi.single_apply]
      split_ifs
      · exact degreeOf_one _
      · exact degreeOf_zero _
    · rw [Matrix.updateRow_ne hi]
      simp only [Tm, Matrix.of_apply]
      apply degreeOf_X_of_ne
      intro h
      simp only [Sum.inl.injEq, Prod.mk.injEq] at h
      exact hi (hA h.1).symm
  apply isUnit_of_degreeOf_eq_zero hp0
  intro x
  rcases x with ⟨i, b⟩ | i
  · by_cases hi : i ∈ Set.range A
    · obtain ⟨l, rfl⟩ := hi; exact hrow l b
    · refine degreeOf_eq_zero_of_dvd _ hpD hD (degreeOf_det_eq_zero _ _ fun a c => ?_)
      simp only [Tm, Matrix.of_apply]
      apply degreeOf_X_of_ne
      intro h
      simp only [Sum.inl.injEq, Prod.mk.injEq] at h
      exact hi ⟨a, h.1.symm⟩
  · exact hinr i

end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators

namespace Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

lemma aeval_X_comp {σ τ : Type} (f : σ → τ) (p : MvPolynomial σ K) :
    aeval (fun q => (X (f q) : MvPolynomial τ K)) p = rename f p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp' hq' => rw [map_add, map_add, hp', hq']
  | mul_X p n hp' => rw [map_mul, map_mul, hp', aeval_X, rename_X]

def lst (hr : 0 < r) : Fin r := ⟨r - 1, by omega⟩

section matrices
variable {L : Type} [Field L]

lemma diagonal_last_zero_eq (hr : 0 < r) :
    Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then (0 : L) else 1) =
      1 - Matrix.vecMulVec (Pi.single (lst hr) (1 : L)) (Pi.single (lst hr) 1) := by
  ext a b
  simp only [Matrix.diagonal_apply, lastIdx_iff hr, Matrix.sub_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply, Pi.single_apply, lst]
  split_ifs <;> simp_all

lemma rank_one_conj_eq (i : Fin r) (φ : Fin r → L) (hφ : φ i = 1) :
    (1 - Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1)) *
      (1 - Matrix.vecMulVec (Pi.single i (1 : L)) (Pi.single i 1)) *
      (1 + Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1))
      = 1 - Matrix.vecMulVec (Pi.single i (1 : L)) φ := by
  set e : Fin r → L := Pi.single i 1 with he
  set E := Matrix.vecMulVec e (φ - e) with hE
  set Q := Matrix.vecMulVec e e with hQ
  have hv : (φ - e) ⬝ᵥ e = 0 := by
    rw [he, dotProduct_single]; simp [hφ]
  have hee : e ⬝ᵥ e = 1 := by rw [he, dotProduct_single]; simp
  have hEQ : E * Q = 0 := by rw [hE, hQ, Matrix.vecMulVec_mul_vecMulVec, hv]; simp
  have hEE : E * E = 0 := by rw [hE, Matrix.vecMulVec_mul_vecMulVec, hv]; simp
  have hQE : Q * E = E := by rw [hE, hQ, Matrix.vecMulVec_mul_vecMulVec, hee, one_smul]
  have hsum : Q + E = Matrix.vecMulVec e φ := by
    ext a b; simp [hQ, hE, Matrix.vecMulVec_apply]; ring
  have h1 : (1 - E) * (1 - Q) = 1 - Q - E := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hEQ]; abel
  rw [h1, mul_add, mul_one, sub_mul, sub_mul, one_mul, hQE, hEE, ← hsum]
  abel

lemma E_sq (i : Fin r) (φ : Fin r → L) (hφ : φ i = 1) :
    Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1) *
      Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1) = 0 := by
  rw [Matrix.vecMulVec_mul_vecMulVec, dotProduct_single]; simp [hφ]

def gU (i : Fin r) (φ : Fin r → L) (hφ : φ i = 1) : GL (Fin r) L where
  val := 1 - Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1)
  inv := 1 + Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1)
  val_inv := by
    rw [mul_add, mul_one, sub_mul, one_mul, E_sq i φ hφ]; abel
  inv_val := by
    rw [add_mul, one_mul, mul_sub, mul_one, E_sq i φ hφ]; abel

lemma conj_diagonal_last_zero (hr : 0 < r) (φ : Fin r → L) (hφ : φ (lst hr) = 1) :
    (gU (lst hr) φ hφ).1 * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then (0 : L) else 1) *
      (gU (lst hr) φ hφ)⁻¹.1 = 1 - Matrix.vecMulVec (Pi.single (lst hr) (1 : L)) φ := by
  rw [diagonal_last_zero_eq hr]
  exact rank_one_conj_eq (lst hr) φ hφ

end matrices

end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators

namespace Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

lemma rename_detLetters (A : Fin r → ι) :
    rename Sum.inl (detLetters (K := K) A) = (Tm K A : Matrix (Fin r) (Fin r) (MvPolynomial ((ι × Fin r) ⊕ ι) K)).det := by
  unfold detLetters; rw [AlgHom.map_det]; congr 1; ext l a; simp [Tm]

theorem dvd_of_red_one (hr : 0 < r) (A : Fin r → ι) (hA : Function.Injective A)
    (G : MvPolynomial (ι × Fin r) K) (h : Red A G 1) : detLetters (K := K) A ∣ G := by
  classical
  set F' := MvPolynomial ((ι × Fin r) ⊕ ι) K
  let L := FractionRing F'
  let am : F' →+* L := algebraMap F' L
  have ham : Function.Injective am := IsFractionRing.injective F' L
  set T := Tm K A with hT
  set Dt := T.det with hDt
  set ψ := T.adjugate.mulVec (Wv K A) with hψ
  set c := ψ (lst hr) with hcdef
  have hDt0 : Dt ≠ 0 := det_Tm_ne_zero A hA
  have hc0 : c ≠ 0 := by
    intro h0
    have := rho_cc (K := K) A hA (lst hr) (lst hr)
    rw [← hψ, ← hcdef, h0, map_zero] at this
    exact adj_Tm_ne_zero A hA (lst hr) (lst hr) this.symm
  have hamc : am c ≠ 0 := fun h0 => hc0 (ham (by rw [h0, map_zero]))
  let φ : Fin r → L := fun b => am (ψ b) / am c
  have hφ : φ (lst hr) = 1 := div_self hamc
  let g := gU (lst hr) φ hφ
  let Y : ι × Fin r → L := fun p => am (X (Sum.inl p))
  have hY : MvPolynomial.aeval Y (detLetters (K := K) A) = am Dt := by
    rw [aeval_detLetters, hDt, RingHom.map_det]; congr 1
  have hdiv := h L g Y (by rw [hY]; exact fun h0 => hDt0 (ham (by rw [h0, map_zero])))
  have hM0 : ∀ a b, ((msMat g) a b).eval 0 = (1 - Matrix.vecMulVec (Pi.single (lst hr) (1 : L)) φ) a b := by
    intro a b
    have := congrFun (congrFun (msMat_eval0 g) a) b
    simp only [Matrix.map_apply, Polynomial.coe_evalRingHom] at this
    rw [this, conj_diagonal_last_zero hr φ hφ]
  have h0 : MvPolynomial.aeval (fun p => (ptA A g Y p).eval 0) G = 0 := by
    obtain ⟨q, hq⟩ := hdiv
    have e1 := congrArg (fun z => (Polynomial.aeval (0 : L)).restrictScalars K z) hq
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval] at e1
    simpa [Polynomial.coe_aeval_eq_eval] using e1
  have hTψ : ∀ l, (∑ b, T l b * ψ b) = Dt * Wv K A l := by
    intro l
    have : T.mulVec ψ = Dt • Wv K A := by
      rw [hψ, Matrix.mulVec_mulVec, Matrix.mul_adjugate, ← hDt, Matrix.smul_mulVec, Matrix.one_mulVec]
    have := congrFun this l
    simpa [Matrix.mulVec, dotProduct] using this
  let f : ι × Fin r → Polynomial F' := fun p => Polynomial.C (X (Sum.inl p)) -
    (if p.2 = lst hr ∧ p.1 ∈ Set.range A then Polynomial.C (X (Sum.inr p.1)) * Polynomial.X else 0)
  let Hp : Polynomial F' := MvPolynomial.aeval f G
  have hroot : Polynomial.aeval (am Dt / am c) Hp = 0 := by
    have e1 : Polynomial.aeval (am Dt / am c) Hp =
        MvPolynomial.aeval (fun p => Polynomial.aeval (am Dt / am c) (f p)) G := by
      show ((Polynomial.aeval (am Dt / am c)).restrictScalars K) (MvPolynomial.aeval f G) = _
      rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]; rfl
    rw [e1, ← h0]
    congr 2
    funext p
    obtain ⟨i, a⟩ := p
    by_cases hi : i ∈ Set.range A
    · obtain ⟨l, rfl⟩ := hi
      simp only [ptA, f, Set.mem_range_self, and_true, if_true, Polynomial.eval_finsetSum,
        Polynomial.eval_mul, Polynomial.eval_C, hM0]
      have hsum : ∑ x, (1 - Matrix.vecMulVec (Pi.single (lst hr) (1 : L)) φ) a x * Y (A l, x) =
          Y (A l, a) - ((Pi.single (lst hr) (1 : L) : Fin r → L) a) * ∑ x, φ x * Y (A l, x) := by
        simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply, sub_mul,
          Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
          if_true, mul_assoc]
        rw [Finset.mul_sum]
      have hφY : ∑ x, φ x * Y (A l, x) = am (Dt * Wv K A l) / am c := by
        rw [← hTψ l, map_sum, Finset.sum_div]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [φ, Y, T, Tm, Matrix.of_apply, map_mul]
        ring
      rw [hsum, hφY]
      by_cases ha : a = lst hr
      · subst ha
        simp only [if_true, map_sub, Polynomial.aeval_C, map_mul, Polynomial.aeval_X, Pi.single_eq_same,
          one_mul, Wv, Y]
        rw [mul_div_assoc', mul_comm (am (X (Sum.inr (A l)))) (am Dt)]
      · simp only [if_neg ha, sub_zero, Polynomial.aeval_C, Pi.single_apply, zero_mul, Y]
        rfl
    · have hi' : ¬ (a = lst hr ∧ i ∈ Set.range A) := fun h => hi h.2
      simp only [f, ptA, if_neg hi, if_neg hi', sub_zero, Polynomial.eval_C, Polynomial.aeval_C, Y]
      rfl
  have hsc : Polynomial.aeval (am Dt) (Hp.scaleRoots c) = 0 :=
    Polynomial.scaleRoots_aeval_eq_zero_of_aeval_div_eq_zero ham hroot (mem_nonZeroDivisors_of_ne_zero hc0)
  have hisroot : (Hp.scaleRoots c).IsRoot Dt := by
    rw [Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval] at hsc
    exact ham (by rw [hsc, map_zero])
  have hdvd := Polynomial.dvd_term_of_isRoot_of_dvd_terms 0 hisroot
    (fun j hj => dvd_mul_of_dvd_right (dvd_pow_self Dt hj) _)
  rw [pow_zero, mul_one, Polynomial.coeff_scaleRoots, Polynomial.coeff_zero_eq_eval_zero] at hdvd
  have hHp0 : Hp.eval 0 = rename Sum.inl G := by
    have e2 : Hp.eval 0 = MvPolynomial.aeval (fun p => ((Polynomial.aeval (0 : F')).restrictScalars K) (f p)) G := by
      rw [← MvPolynomial.comp_aeval, AlgHom.comp_apply]
      simp [Hp, Polynomial.coe_aeval_eq_eval]
    rw [e2, ← aeval_X_comp]
    congr 2
    funext p
    simp only [f, AlgHom.restrictScalars_apply, Polynomial.coe_aeval_eq_eval, Polynomial.eval_sub,
      Polynomial.eval_C]
    split_ifs
    · rw [Polynomial.eval_mul, Polynomial.eval_X, mul_zero, sub_zero]
    · rw [Polynomial.eval_zero, sub_zero]
  rw [hHp0] at hdvd
  have hcop := (coprime_det_cc (K := K) A hA (lst hr)).pow_right (n := Hp.natDegree - 0)
  have hD' : Dt ∣ rename Sum.inl G := hcop.dvd_of_dvd_mul_right hdvd
  let ret : F' →ₐ[K] MvPolynomial (ι × Fin r) K := MvPolynomial.aeval (Sum.elim X 0)
  have hret : ∀ q : MvPolynomial (ι × Fin r) K, ret (rename Sum.inl q) = q := by
    intro q
    simp only [ret]
    rw [aeval_rename]
    have : (Sum.elim X 0 : (ι × Fin r) ⊕ ι → MvPolynomial (ι × Fin r) K) ∘ Sum.inl = X := by
      funext p; simp
    rw [this, aeval_X_left_apply]
  have := map_dvd ret hD'
  rwa [hDt, hT, ← rename_detLetters, hret, hret] at this

end Formalism.G0.DetDividesP

end

noncomputable section
open scoped BigOperators

namespace Formalism.G0.DetDividesP
open Formalism.G0

variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}

theorem dvd_pow_of_red (hr : 0 < r) (A : Fin r → ι) (hA : Function.Injective A) :
    ∀ (n : ℕ) (G : MvPolynomial (ι × Fin r) K), Red A G n → detLetters (K := K) A ^ n ∣ G := by
  intro n
  induction n with
  | zero => intro G _; simp
  | succ n ih =>
    intro G h
    have h1 : Red A G 1 := fun L _ _ g x hx =>
      (pow_dvd_pow Polynomial.X (by omega)).trans (h L g x hx)
    obtain ⟨G', rfl⟩ := dvd_of_red_one hr A hA G h1
    have h2 := red_of_mul hr A G' n h
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih G' h2)

end Formalism.G0.DetDividesP

namespace Formalism.G0

theorem det_divides : DetDivides := by
  intro K ι _ _ _ r vec S A d G th hA hAS hG hV hB
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have h1 : detLetters (K := K) A = 1 := by
      unfold detLetters; exact Matrix.det_isEmpty
    rw [h1, one_pow]; exact one_dvd _
  · exact DetDividesP.dvd_pow_of_red hr A hA _ G
      (DetDividesP.red_of_valGE hr vec S A d G th hAS hG hV hB)

end Formalism.G0

end
