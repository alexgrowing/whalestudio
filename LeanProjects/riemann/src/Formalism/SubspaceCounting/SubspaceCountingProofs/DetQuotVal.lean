import Formalism.SubspaceCounting.DetQuotVal
import Formalism.SubspaceCounting.SubspaceCountingProofs.DetVal

noncomputable section
open scoped BigOperators

namespace Formalism.G0.DetQuotValP
open Formalism.G0 Formalism.G0.DetValP

variable {K ι : Type} [Field K] [DecidableEq ι]

lemma det_msMat {L : Type} [Field L] {r : ℕ} (hr : 1 ≤ r) (g : GL (Fin r) L) :
    (msMat g).det = Polynomial.X := by
  unfold msMat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, prod_last hr]
  have h1 : (g.1.map Polynomial.C).det * ((g⁻¹ : GL (Fin r) L).1.map Polynomial.C).det = 1 := by
    rw [← Matrix.det_mul, ← Matrix.map_mul, Units.mul_inv]
    simp
  calc (g.1.map Polynomial.C).det * Polynomial.X * ((g⁻¹ : GL (Fin r) L).1.map Polynomial.C).det
      = Polynomial.X * ((g.1.map Polynomial.C).det *
          ((g⁻¹ : GL (Fin r) L).1.map Polynomial.C).det) := by ring
    _ = Polynomial.X := by rw [h1, mul_one]

lemma substS_det_all {L : Type} [Field L] [Algebra K L] {r : ℕ} (hr : 1 ≤ r) (vec : ι → Bool)
    (S : Finset ι) (A : Fin r → ι) (hv : ∀ l, vec (A l) = true) (hS : ∀ l, A l ∈ S)
    (g : GL (Fin r) L) :
    substS (K := K) vec S g (detLetters A) =
      MvPolynomial.C Polynomial.X * Matrix.det (Matrix.of fun (l b : Fin r) =>
          (MvPolynomial.X (A l, b) : MvPolynomial (ι × Fin r) (Polynomial L))) := by
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
  rw [h1, Matrix.det_mul, Matrix.det_transpose, ← hC, det_msMat hr, mul_comm]

lemma not_dvd_detX {L : Type} [Field L] {r : ℕ} (A : Fin r → ι) (hA : Function.Injective A) :
    ¬ (MvPolynomial.C Polynomial.X : MvPolynomial (ι × Fin r) (Polynomial L)) ∣
      Matrix.det (Matrix.of fun (l b : Fin r) =>
          (MvPolynomial.X (A l, b) : MvPolynomial (ι × Fin r) (Polynomial L))) := by
  intro h
  let v : ι × Fin r → L := fun p => ∑ l, if p.1 = A l ∧ p.2 = l then 1 else 0
  have h2 := map_dvd (MvPolynomial.eval₂Hom (Polynomial.evalRingHom (0 : L)) v) h
  rw [MvPolynomial.eval₂Hom_C, RingHom.map_det, RingHom.mapMatrix_apply] at h2
  have hM : (Matrix.of fun (l b : Fin r) =>
      (MvPolynomial.X (A l, b) : MvPolynomial (ι × Fin r) (Polynomial L))).map
        (MvPolynomial.eval₂Hom (Polynomial.evalRingHom (0 : L)) v) = 1 := by
    refine Matrix.ext fun l b => ?_
    simp only [Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval₂Hom_X', Matrix.one_apply, v]
    rw [Finset.sum_eq_single l]
    · by_cases e : b = l
      · subst e; simp
      · simp [e, Ne.symm e]
    · intro k _ hk
      have : A l ≠ A k := fun x => hk (hA x).symm
      simp [this]
    · simp
  rw [hM, Matrix.det_one] at h2
  simp at h2

lemma msMat_eval_zero_mul_eq_mul_diagonal {L : Type} [Field L] {r : ℕ} (g : GL (Fin r) L) :
    (msMat g).map (Polynomial.evalRingHom (0 : L)) * g.1 =
      g.1 * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then (0 : L) else 1) := by
  unfold msMat
  rw [Matrix.map_mul, Matrix.map_mul]
  have e1 : (g.1.map Polynomial.C).map (Polynomial.evalRingHom (0 : L)) = g.1 := by
    ext i j; simp
  have e2 : ((g⁻¹ : GL (Fin r) L).1.map Polynomial.C).map (Polynomial.evalRingHom (0 : L)) =
      (g⁻¹ : GL (Fin r) L).1 := by
    ext i j; simp
  have e3 : (Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then Polynomial.X else 1)).map
      (Polynomial.evalRingHom (0 : L)) =
      Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then (0 : L) else 1) := by
    ext i j
    by_cases h : i = j
    · subst h; by_cases h' : i.val + 1 = r <;> simp [h']
    · simp [h]
  rw [e1, e2, e3, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

lemma not_dvd_substS_det {L : Type} [Field L] [Algebra K L] {r : ℕ} (hr : 1 ≤ r)
    (vec : ι → Bool) (S : Finset ι) (A : Fin r → ι) (hA : Function.Injective A)
    (hv : ∀ l, vec (A l) = true) (hS : ¬ ∀ l, A l ∈ S) (g : GL (Fin r) L) :
    ¬ MvPolynomial.C Polynomial.X ∣ substS (K := K) vec S g (detLetters A) := by
  intro h
  obtain ⟨l₀, hl₀⟩ := not_forall.mp hS
  let last : Fin r := ⟨r - 1, by omega⟩
  let τ : Equiv.Perm (Fin r) := Equiv.swap l₀ last
  let v : ι × Fin r → L := fun p => ∑ l, if p.1 = A l then g.1 p.2 (τ l) else 0
  have hvA : ∀ l b, v (A l, b) = g.1 b (τ l) := by
    intro l b
    simp only [v]
    rw [Finset.sum_eq_single l]
    · simp
    · intro k _ hk
      have : A l ≠ A k := fun x => hk (hA x).symm
      simp [this]
    · simp
  let φ := MvPolynomial.eval₂Hom (Polynomial.evalRingHom (0 : L)) v
  have h2 := map_dvd φ h
  rw [show φ (MvPolynomial.C Polynomial.X) = 0 by simp [φ], substS_det, zero_dvd_iff] at h2
  have hM : (Matrix.of fun l a => φ (substS (K := K) vec S g (MvPolynomial.X (A l, a)))) =
      (g.1.transpose).submatrix τ id := by
    refine Matrix.ext fun l a => ?_
    rw [Matrix.of_apply, Matrix.submatrix_apply, id, Matrix.transpose_apply, substS_X]
    by_cases hl : A l ∈ S
    · simp only [hl, hv l, if_true, map_sum, map_mul, φ, MvPolynomial.eval₂Hom_C,
        MvPolynomial.eval₂Hom_X', hvA]
      have := congrFun (congrFun (msMat_eval_zero_mul_eq_mul_diagonal g) a) (τ l)
      rw [Matrix.mul_apply, Matrix.mul_diagonal] at this
      simp only [Matrix.map_apply, Polynomial.coe_evalRingHom] at this
      simp only [Polynomial.coe_evalRingHom]
      rw [this]
      have hne : (τ l).val + 1 ≠ r := by
        intro e
        have h' : τ l = last := by ext; simp [last]; omega
        have hll : l = l₀ := by
          have := congrArg τ h'
          rw [Equiv.swap_apply_self] at this
          simpa [τ] using this
        exact hl₀ (hll ▸ hl)
      simp [hne]
    · simp only [hl, if_false, φ, MvPolynomial.eval₂Hom_X', hvA]
  rw [hM, Matrix.det_permute, Matrix.det_transpose] at h2
  have hu := Matrix.isUnits_det_units g
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with e | e <;> simp [e, hu.ne_zero] at h2

lemma sum_cov {r : ℕ} (vec : ι → Bool) (S : Finset ι) (A : Fin r → ι)
    (hv : ∀ l, vec (A l) = true) (d : ι → ℕ) (m' : ℕ) :
    ∑ i ∈ S.filter (fun i => vec i = false), (d i + m' * (if i ∈ Set.range A then 1 else 0)) =
      ∑ i ∈ S.filter (fun i => vec i = false), d i := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_cov_zero vec S A hv, mul_zero, add_zero]

end Formalism.G0.DetQuotValP

open Formalism.G0.DetQuotValP in
theorem Formalism.G0.det_quotient_valuation : Formalism.G0.DetQuotVal := by
  intro K ι _ _ _ r vec S' A d H m' th hA hv _ hle hval L _ _ g
  have h := hval L g
  rw [sum_cov vec S' A hv d m'] at h
  set c := ∑ i ∈ S'.filter (fun i => vec i = false), d i
  simp only [map_mul, map_pow] at h ⊢
  set p : MvPolynomial (ι × Fin r) (Polynomial L) := MvPolynomial.C Polynomial.X with hpdef
  have hp : Prime p := (MvPolynomial.prime_C_iff _).mpr Polynomial.prime_X
  have hnd : ∀ (U : MvPolynomial (ι × Fin r) (Polynomial L)), ¬ p ∣ U → ∀ n, p ^ n ∣ U ^ m' *
      substS (K := K) vec S' g H → p ^ n ∣ substS (K := K) vec S' g H := by
    intro U hU n hn
    exact hp.pow_dvd_of_dvd_mul_left n (fun e => hU (hp.dvd_of_dvd_pow e)) hn
  by_cases hall : 1 ≤ r ∧ ∀ l, A l ∈ S'
  · rw [substS_det_all hall.1 vec S' A hv hall.2 g, mul_pow, mul_assoc] at h
    rw [show th + c = m' + (th - m' + c) by omega, pow_add] at h
    have h' := (mul_dvd_mul_iff_left (pow_ne_zero m' hp.ne_zero)).mp h
    exact hnd _ (not_dvd_detX A hA) _ h'
  · have hnot : ¬ p ∣ substS (K := K) vec S' g (detLetters A) := by
      by_cases hr : 1 ≤ r
      · exact not_dvd_substS_det hr vec S' A hA hv (fun x => hall ⟨hr, x⟩) g
      · have hr0 : r = 0 := by omega
        subst hr0
        have : detLetters (K := K) A = 1 := Matrix.det_fin_zero
        rw [this, map_one]
        exact hp.not_dvd_one
    exact (pow_dvd_pow p (by omega)).trans (hnd _ hnot _ h)
