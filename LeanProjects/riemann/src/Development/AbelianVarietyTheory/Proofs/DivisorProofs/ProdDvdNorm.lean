import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjCongr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnramifiedPeriodAinfUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyClosureHomTiltField

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.BKReal Formalism.BasicNotions.Examples₂.LB
open scoped Formalism.Per

namespace GlobalTheory.ConjNorm

theorem det_dvd_det {D : Type*} [CommRing D] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (V : Matrix m n D) (W : Matrix n m D) (M : Matrix n n D) (Y : Matrix m m D) (h1 : V * W = 1)
    (h2 : V * M = Y * V) : Y.det ∣ M.det := by
  have e : M = (1 + W * ((Y - 1) * V)) * ((1 - W * V) * M + W * V) := by
    have h3 : ∀ X : Matrix m n D, V * (W * X) = X := fun X => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_assoc,
      h3, h2]
    abel
  rw [e, Matrix.det_mul, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, h1, Matrix.mul_one, add_sub_cancel]
  exact dvd_mul_right _ _

section Norm

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]

theorem norm_map {A' S' ι : Type*} [CommRing A'] [CommRing S'] [Algebra A' S'] [Fintype ι]
    (b : Module.Basis ι A S) (b' : Module.Basis ι A' S') (f : A →+* A') (F : S →+* S')
    (hf : ∀ a, F (algebraMap A S a) = algebraMap A' S' (f a)) (hb : ∀ i, F (b i) = b' i) (x : S) :
    Algebra.norm A' (F x) = f (Algebra.norm A x) := by
  classical
  have hr : ∀ y i, b'.repr (F y) i = f (b.repr y i) := fun y i => by
    conv_lhs => rw [← b.sum_repr y]
    simp only [map_sum, Algebra.smul_def, map_mul, hf, hb]
    simp [← Algebra.smul_def, Finsupp.single_apply]
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b', RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, ← hb, ← map_mul, hr]

theorem prod_dvd_norm [Module.Free A S] [Module.Finite A S] {D m : Type*} [CommRing D] [Fintype m] [DecidableEq m]
    (φ : m → S →+* D) (ψ : A →+* D) (h : ∀ i a, φ i (algebraMap A S a) = ψ a) (c : m → S)
    (hc : IsUnit (Matrix.of fun i k => φ i (c k)).det) (x : S) : ∏ i, φ i x ∣ ψ (Algebra.norm A x) := by
  classical
  let b := Module.Free.chooseBasis A S
  have hr : ∀ i y, ∑ k, φ i (b k) * ψ (b.repr y k) = φ i y := fun i y => by
    conv_rhs => rw [← b.sum_repr y]
    simp only [map_sum, Algebra.smul_def, map_mul, h, mul_comm]
  rw [Algebra.norm_eq_matrix_det b, RingHom.map_det, ← Matrix.det_diagonal]
  refine det_dvd_det (Matrix.of fun i k => φ i (b k))
    ((Matrix.of fun k j => ψ (b.repr (c j) k)) * (Matrix.of fun i k => φ i (c k))⁻¹) _ _ ?_ ?_
  · rw [← Matrix.mul_assoc, ← Matrix.mul_nonsing_inv _ hc]
    congr 1
    ext i j
    exact hr i (c j)
  · ext i k
    rw [Matrix.diagonal_mul, Matrix.mul_apply, Matrix.of_apply, ← map_mul, ← hr]
    simp only [Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul]

theorem dvd_norm [Module.Free A S] [Module.Finite A S] (x : S) : x ∣ algebraMap A S (Algebra.norm A x) := by
  simpa using prod_dvd_norm (fun _ : Unit => RingHom.id S) (algebraMap A S) (fun _ _ => rfl) (fun _ => 1)
    (by simp) x

theorem mul_dvd_norm [Module.Free A S] [Module.Finite A S] {D : Type*} [CommRing D] (φ₁ φ₂ : S →+* D)
    (h : ∀ a, φ₂ (algebraMap A S a) = φ₁ (algebraMap A S a)) (c : S) (hc : IsUnit (φ₂ c - φ₁ c)) (x : S) :
    φ₁ x * φ₂ x ∣ φ₁ (algebraMap A S (Algebra.norm A x)) := by
  simpa using prod_dvd_norm ![φ₁, φ₂] (φ₁.comp (algebraMap A S)) (fun i a => by fin_cases i <;> simp [h])
    ![1, c] (by simpa [Matrix.det_fin_two] using hc) x

end Norm

variable {l : ℕ} [hl : Fact l.Prime] (K : FinExt l)

theorem norm_unif {π : ↥(OL K)} (hπ : Irreducible π) :
    ∃ u : W0 K, IsUnit u ∧ Algebra.norm (W0 K) π = (l : W0 K) * u := by
  haveI : FaithfulSMul (W0 K) ↥(OL K) := (faithfulSMul_iff_algebraMap_injective _ _).2 (thetaW_injective K)
  haveI : CharZero (W0 K) := (algebraMap (W0 K) ↥(OL K)).charZero
  let P := IsLocalRing.maximalIdeal ↥(OL K)
  let p := IsLocalRing.maximalIdeal (W0 K)
  haveI hlo : P.LiesOver p := by
    constructor
    have : (P.under (W0 K)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P
    exact (IsLocalRing.eq_maximalIdeal this).symm
  have hrel := Ideal.relNorm_eq_pow_of_isMaximal P p
  have hf : P.inertiaDeg (W0 K) = 1 := by
    rw [Ideal.inertiaDeg_eq_of_isMaximal p P]
    letI := Ideal.Quotient.field p
    letI := Ideal.Quotient.field P
    refine Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨RingHom.injective _, fun y => ?_⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨w, hw⟩ := exists_thetaW (card_res K) x
    exact ⟨Ideal.Quotient.mk _ w, hw⟩
  have hP : P = Ideal.span {π} := hπ.maximalIdeal_eq
  have hp : p = Ideal.span {(l : W0 K)} := (WittVector.irreducible l).maximalIdeal_eq
  rw [hf, pow_one, hP, Ideal.relNorm_singleton, hp, Algebra.intNorm_eq_norm] at hrel
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hrel.symm
  exact ⟨u, u.isUnit, hu.symm⟩

theorem exists_lang (u : W0 K) (hu : IsUnit u) :
    ∃ a : Per.Ainf l, IsUnit a ∧ Per.φA l a = wA l (fK K) u * a := by
  obtain ⟨f⟩ := GlobalTheory.Per.nonempty_algClosure_zmod_to_tilt l
  have hr : ∀ x : Fq l (fK K), ∃ y, f y = Fq.val l (fK K) x := fun x => by
    have h1 := one_lt_pow_l l (fK K)
    have hm : (Polynomial.X ^ l ^ fK K - Polynomial.X : Polynomial (AlgebraicClosure (ZMod l))).Monic :=
      Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast h1)
    have h2 := congrArg (Polynomial.eval₂ f (Fq.val l (fK K) x))
      ((IsAlgClosed.splits _).eq_prod_roots_of_monic hm)
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X, ← map_pow, Fq.pow_card, sub_self,
      Polynomial.eval₂_multiset_prod, eq_comm, Multiset.prod_eq_zero_iff, Multiset.map_map] at h2
    obtain ⟨y, -, hy⟩ := Multiset.mem_map.1 h2
    refine ⟨y, ?_⟩
    simp only [Function.comp, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C] at hy
    exact (sub_eq_zero.1 hy).symm
  choose r hr using hr
  let u' : WittVector l (AlgebraicClosure (ZMod l)) := WittVector.mk l fun n => r (u.coeff n)
  have hfu : WittVector.map f u' = wA l (fK K) u := WittVector.ext fun n => hr (u.coeff n)
  have hu' : IsUnit u' := WittVector.isUnit_of_coeff_zero_ne_zero _ fun h => by
    have h0 : u.coeff 0 ≠ 0 := (hu.map (WittVector.constantCoeff (p := l) (R := Fq l (fK K)))).ne_zero
    have h1 := hr (u.coeff 0)
    rw [show r (u.coeff 0) = 0 from h, map_zero, eq_comm, map_eq_zero] at h1
    exact h0 h1
  obtain ⟨w, hw, hφ⟩ := GlobalTheory.MemLoc.exists_unit_frobenius_eq_mul l _ u' hu'
  refine ⟨WittVector.map f w, hw.map _, ?_⟩
  rw [← hfu, ← map_mul, ← hφ]
  refine WittVector.ext fun n => ?_
  have h := GlobalTheory.AinfK.coeff_iter 1 (WittVector.map f w) n
  rw [Function.iterate_one, pow_one] at h
  rw [h, WittVector.map_coeff, WittVector.map_coeff, WittVector.coeff_frobenius_charP, map_pow]

end GlobalTheory.ConjNorm

end
