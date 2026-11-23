import Formalism.SubspaceCounting.StatementW

noncomputable section
open scoped BigOperators

namespace Formalism.G0.DetValP
open Formalism.G0

variable {K ι : Type} [Field K] [DecidableEq ι]

lemma substS_det {L : Type} [Field L] [Algebra K L] {r : ℕ} (vec : ι → Bool) (S : Finset ι)
    (g : GL (Fin r) L) (A : Fin r → ι) {R : Type} [CommRing R]
    (φ : MvPolynomial (ι × Fin r) (Polynomial L) →+* R) :
    φ (substS (K := K) vec S g (detLetters A)) =
      Matrix.det (Matrix.of fun l a => φ (substS (K := K) vec S g (MvPolynomial.X (A l, a)))) := by
  unfold detLetters
  rw [AlgHom.map_det, RingHom.map_det]
  congr 1

lemma substS_X {L : Type} [Field L] [Algebra K L] {r : ℕ} (vec : ι → Bool) (S : Finset ι)
    (g : GL (Fin r) L) (p : ι × Fin r) :
    substS (K := K) vec S g (MvPolynomial.X p) =
      (if p.1 ∈ S then
      (if vec p.1 then ∑ b, MvPolynomial.C ((msMat g) p.2 b) * MvPolynomial.X (p.1, b)
       else ∑ b, MvPolynomial.C ((msDualMat g) p.2 b) * MvPolynomial.X (p.1, b))
    else MvPolynomial.X p) := by
  simp [substS]

lemma sum_cov_zero {r : ℕ} (vec : ι → Bool) (S : Finset ι) (A : Fin r → ι)
    (hv : ∀ l, vec (A l) = true) :
    ∑ i ∈ S.filter (fun i => vec i = false), (if i ∈ Set.range A then 1 else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_filter] at hi
  have : i ∉ Set.range A := by rintro ⟨l, rfl⟩; simp [hv l] at hi
  simp [this]

lemma msMat_one {L : Type} [Field L] {r : ℕ} :
    msMat (1 : GL (Fin r) L) =
      Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then Polynomial.X else 1) := by
  simp [msMat]

end Formalism.G0.DetValP

namespace Formalism.G0.DetValP
open Formalism.G0

variable {K ι : Type} [Field K] [DecidableEq ι]

lemma prod_last {L : Type} [Field L] {r : ℕ} (hr : 1 ≤ r) :
    ∏ a : Fin r, (if a.val + 1 = r then (Polynomial.X : Polynomial L) else 1) = Polynomial.X := by
  rw [Finset.prod_eq_single (⟨r - 1, by omega⟩ : Fin r)]
  · simp; omega
  · intro b _ hb
    have : b.val + 1 ≠ r := by
      intro h; apply hb; ext; simp; omega
    simp [this]
  · simp

lemma part1a {L : Type} [Field L] [Algebra K L] {r : ℕ} (hr : 1 ≤ r) (vec : ι → Bool)
    (S : Finset ι) (A : Fin r → ι) (hv : ∀ l, vec (A l) = true) (hS : ∀ l, A l ∈ S)
    (g : GL (Fin r) L) :
    MvPolynomial.C Polynomial.X ∣ substS (K := K) vec S g (detLetters A) := by
  have h1 : substS (K := K) vec S g (detLetters A) =
      Matrix.det ((Matrix.of fun (l b : Fin r) =>
          (MvPolynomial.X (A l, b) : MvPolynomial (ι × Fin r) (Polynomial L))) *
        ((msMat g).map MvPolynomial.C).transpose) := by
    have := substS_det (K := K) vec S g A (RingHom.id _)
    simp only [RingHom.id_apply] at this
    rw [this]
    congr 1
    refine Matrix.ext fun l a => ?_
    rw [Matrix.of_apply, substS_X]
    simp only [hS l, hv l, if_true, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply]
    refine Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hC := RingHom.map_det (MvPolynomial.C : Polynomial L →+* MvPolynomial (ι × Fin r) (Polynomial L)) (msMat g)
  rw [RingHom.mapMatrix_apply] at hC
  rw [h1, Matrix.det_mul, Matrix.det_transpose, ← hC]
  apply dvd_mul_of_dvd_right
  apply map_dvd
  unfold msMat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, prod_last hr]
  exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _

end Formalism.G0.DetValP

namespace Formalism.G0.DetValP
open Formalism.G0

variable {K ι : Type} [Field K] [DecidableEq ι]

lemma entry_one_mem {R : Type} [CommRing R] {r : ℕ} (vec : ι → Bool) (S : Finset ι)
    (φ : Polynomial K →+* R) (v : ι × Fin r → R) (i : ι) (hi : i ∈ S) (hvi : vec i = true)
    (a : Fin r) :
    MvPolynomial.eval₂Hom φ v (substS (K := K) vec S (1 : GL (Fin r) K) (MvPolynomial.X (i, a))) =
      φ (if a.val + 1 = r then Polynomial.X else 1) * v (i, a) := by
  rw [substS_X]
  simp only [hi, hvi, if_true, msMat_one, map_sum, map_mul, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X', Matrix.diagonal_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

lemma entry_one_nmem {R : Type} [CommRing R] {r : ℕ} (vec : ι → Bool) (S : Finset ι)
    (φ : Polynomial K →+* R) (v : ι × Fin r → R) (i : ι) (hi : i ∉ S) (a : Fin r) :
    MvPolynomial.eval₂Hom φ v (substS (K := K) vec S (1 : GL (Fin r) K) (MvPolynomial.X (i, a))) =
      v (i, a) := by
  rw [substS_X]
  simp [hi]

lemma part1b {r : ℕ} (hr : 1 ≤ r) (vec : ι → Bool)
    (S : Finset ι) (A : Fin r → ι) (hA : Function.Injective A) (hv : ∀ l, vec (A l) = true)
    (hS : ∀ l, A l ∈ S) :
    ¬ MvPolynomial.C (Polynomial.X ^ 2) ∣
      substS (K := K) vec S (1 : GL (Fin r) K) (detLetters A) := by
  intro h
  let v : ι × Fin r → Polynomial K := fun p => if p.1 = A p.2 then 1 else 0
  have h2 := map_dvd (MvPolynomial.eval₂Hom (RingHom.id (Polynomial K)) v) h
  rw [MvPolynomial.eval₂Hom_C, RingHom.id_apply, substS_det] at h2
  have hM : (Matrix.of fun l a => MvPolynomial.eval₂Hom (RingHom.id (Polynomial K)) v
      (substS (K := K) vec S (1 : GL (Fin r) K) (MvPolynomial.X (A l, a)))) =
      Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then Polynomial.X else 1) := by
    refine Matrix.ext fun l a => ?_
    rw [Matrix.of_apply, entry_one_mem vec S _ v (A l) (hS l) (hv l) a, Matrix.diagonal_apply]
    by_cases hla : l = a
    · subst hla; simp [v]
    · have : A l ≠ A a := fun e => hla (hA e)
      simp [v, this, hla]
  rw [hM, Matrix.det_diagonal, prod_last hr] at h2
  have := Polynomial.natDegree_le_of_dvd h2 Polynomial.X_ne_zero
  simp at this

lemma part2 {r : ℕ} (hr : 1 ≤ r) (vec : ι → Bool)
    (S : Finset ι) (A : Fin r → ι) (hA : Function.Injective A) (hv : ∀ l, vec (A l) = true)
    (hS : ¬ ∀ l, A l ∈ S) :
    ¬ MvPolynomial.C (Polynomial.X ^ 1) ∣
      substS (K := K) vec S (1 : GL (Fin r) K) (detLetters A) := by
  intro h
  obtain ⟨l₀, hl₀⟩ := not_forall.mp hS
  let last : Fin r := ⟨r - 1, by omega⟩
  let τ : Equiv.Perm (Fin r) := Equiv.swap l₀ last
  let v : ι × Fin r → K := fun p => if p.1 = A (τ p.2) then 1 else 0
  have h2 := map_dvd (MvPolynomial.eval₂Hom (Polynomial.evalRingHom (0 : K)) v) h
  rw [MvPolynomial.eval₂Hom_C, substS_det] at h2
  simp only [Polynomial.coe_evalRingHom, pow_one, Polynomial.eval_X, zero_dvd_iff] at h2
  have hM : (Matrix.of fun l a => MvPolynomial.eval₂Hom (Polynomial.evalRingHom (0 : K)) v
      (substS (K := K) vec S (1 : GL (Fin r) K) (MvPolynomial.X (A l, a)))) =
      (1 : Matrix (Fin r) (Fin r) K).submatrix id τ := by
    refine Matrix.ext fun l a => ?_
    rw [Matrix.of_apply, Matrix.submatrix_apply, id, Matrix.one_apply]
    have hvv : v (A l, a) = if l = τ a then 1 else 0 := by
      simp only [v]
      by_cases e : l = τ a
      · simp [e]
      · have : A l ≠ A (τ a) := fun x => e (hA x)
        simp [e, this]
    by_cases hl : A l ∈ S
    · rw [entry_one_mem vec S _ v (A l) hl (hv l) a, hvv]
      by_cases e : l = τ a
      · have ha : a.val + 1 ≠ r := by
          intro ha
          have : a = last := by ext; simp [last]; omega
          apply hl₀
          have hll : l = l₀ := by rw [e, this]; exact Equiv.swap_apply_right l₀ last
          rw [← hll]; exact hl
        simp [e, ha]
      · simp [e]
    · rw [entry_one_nmem vec S _ v (A l) hl a, hvv]
  rw [hM, Matrix.det_permute', Matrix.det_one, mul_one] at h2
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with e | e <;> simp [e] at h2

end Formalism.G0.DetValP

open Formalism.G0.DetValP in
theorem Formalism.G0.det_valuation : Formalism.G0.DetVal := by
  intro K ι _ _ _ r vec S' A hr hA hv
  simp only
  have hsum := sum_cov_zero vec S' A hv
  refine ⟨fun hS => ⟨?_, ?_⟩, fun hS => ?_⟩
  · intro L _ _ g
    rw [hsum]
    simpa using part1a (K := K) hr vec S' A hv hS g
  · intro hval
    have := hval K (1 : GL (Fin r) K)
    rw [hsum] at this
    exact part1b hr vec S' A hA hv hS this
  · intro hval
    have := hval K (1 : GL (Fin r) K)
    rw [hsum] at this
    exact part2 hr vec S' A hA hv hS this
