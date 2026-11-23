import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch

open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory.UnitLemma.SgnBasis

theorem eta_mul_isUnit (K : UQ) (a : K.E) (u : K.O) (hu : IsUnit u) :
    K.eta (a * algebraMap K.O K.E u) = K.eta a := by
  have hv : (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E (algebraMap K.O K.E u) = 1 := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff]
    intro h
    exact (IsDiscreteValuationRing.maximalIdeal K.O).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ h hu)
  simp only [UQ.eta, val, map_mul, hv, mul_one]

private theorem eta_det_trace_matrix_eq_of_span_eq (K : UQ) (B : InvAlg K)
    (e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A)
    (m : Fin (Module.finrank K.E B.A) → B.A)
    (hm : Submodule.span K.O (Set.range m) = Submodule.span K.O (Set.range e)) :
    K.eta (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * m l)).det =
      K.eta (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)).det := by
  classical
  have hP0 : ∀ l, ∃ c : Fin (Module.finrank K.E B.A) → K.O, ∑ j, c j • e j = m l := by
    intro l
    refine (Submodule.mem_span_range_iff_exists_fun K.O).mp ?_
    rw [← hm]
    exact Submodule.subset_span ⟨l, rfl⟩
  have hQ0 : ∀ l, ∃ c : Fin (Module.finrank K.E B.A) → K.O, ∑ j, c j • m j = e l := by
    intro l
    refine (Submodule.mem_span_range_iff_exists_fun K.O).mp ?_
    rw [hm]
    exact Submodule.subset_span ⟨l, rfl⟩
  choose P hP using hP0
  choose Q hQ using hQ0

  have hli : LinearIndependent K.O e :=
    e.linearIndependent.restrict_scalars fun a b h =>
      IsFractionRing.injective K.O K.E (by simpa [Algebra.smul_def] using h)

  have hsum : ∀ l, ∑ i, (∑ j, Q l j * P j i) • e i = e l := by
    intro l
    calc ∑ i, (∑ j, Q l j * P j i) • e i = ∑ j, Q l j • ∑ i, P j i • e i := by
          simp only [Finset.sum_smul, Finset.smul_sum, mul_smul]
          exact Finset.sum_comm
      _ = e l := by simp only [hP, hQ]
  have hQP : Matrix.of Q * Matrix.of P = 1 := by
    ext l i
    have key : ∑ i, ((Matrix.of Q * Matrix.of P) l i - (1 : Matrix _ _ K.O) l i) • e i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, Matrix.mul_apply, Matrix.of_apply,
        Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
        if_true, hsum, sub_self]
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hli _ key i)
  have hunit : IsUnit (Matrix.of P).det := Matrix.isUnit_det_of_left_inverse hQP

  have hmat : (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * m l)) =
      (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)) *
        (Matrix.of P).transpose.map (algebraMap K.O K.E) := by
    ext k l
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
    rw [← hP l]
    simp only [Finset.mul_sum, mul_smul_comm, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul K.E (P l j), map_smul, smul_eq_mul, mul_comm]
  have hdet : ((Matrix.of P).transpose.map (algebraMap K.O K.E)).det =
      algebraMap K.O K.E (Matrix.of P).det := by
    rw [RingHom.map_det, ← Matrix.det_transpose]
    rfl
  rw [hmat, Matrix.det_mul, hdet]
  exact eta_mul_isUnit K _ _ hunit

theorem sgnLat_span_basis (K : UQ) (B : InvAlg K) (e : Module.Basis (Fin (Module.finrank K.E B.A)) K.E B.A) :
    B.sgnLat (Submodule.span K.O (Set.range e)) =
      K.eta (Matrix.of fun k l : Fin (Module.finrank K.E B.A) =>
        Algebra.trace K.E B.A (B.g ^ (k : ℕ) * e l)).det := by
  dsimp only [InvAlg.sgnLat]
  exact eta_det_trace_matrix_eq_of_span_eq K B e _
    (Classical.epsilon_spec (p := fun m : Fin (Module.finrank K.E B.A) → B.A =>
      Submodule.span K.O (Set.range m) = Submodule.span K.O (Set.range e)) ⟨e, rfl⟩)

end GlobalTheory.UnitLemma.SgnBasis
