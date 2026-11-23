import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.SympPure

private theorem trace_tmul_base_change {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] (a : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
  have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

private theorem form_mul_form {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E) (ξ β : Fin n → E) (x y : Fin d → E) :
    form σ J ξ β * form σ K y x = ∑ i, ∑ j, ∑ k, ∑ l, ξ i * y j * J i k * K j l * (σ (β k) * σ (x l)) := by
  simp only [form, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  trans ∑ j, ∑ i, ∑ k, ∑ l, ξ i * y j * J i k * K j l * (σ (β k) * σ (x l))
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  · exact Finset.sum_comm

theorem hTens_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E) (ξ β : Fin n → E) (x y : Fin d → E) (t : AF F) :
    hTens (cA σ) (incM F J) (incM F K) (Matrix.vecMulVec (incV F ξ) (incV F y))
      (Matrix.vecMulVec (t • incV F β) (incV F x)) =
      algebraMap (AF F) (AE F E) t * inclR (AF F) (form σ J ξ β * form σ K y x) := by
  have hc : ∀ e : E, cA σ (inclR (AF F) e) = inclR (AF F) (σ e) := fun e => by simp [cA, inclR]
  have hs : ∀ k, (t • incV F β) k = algebraMap (AF F) (AE F E) t * inclR (AF F) (β k) := fun k => by
    rw [Pi.smul_apply, Algebra.smul_def]; rfl
  rw [form_mul_form]
  simp only [hTens, Matrix.vecMulVec_apply, hs, incM, Matrix.map_apply, map_mul, AlgHom.commutes, hc, map_sum,
    Finset.mul_sum]
  simp only [incV, hc]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => by ring

theorem symp_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (K : Matrix (Fin d) (Fin d) E)
    (ξ β : Fin n → E) (x y : Fin d → E) (t : AF F) :
    symp (cA σ) (-1) (incM F J) (incM F K) (Matrix.vecMulVec (incV F ξ) (incV F y))
      (Matrix.vecMulVec (t • incV F β) (incV F x)) =
      t * algebraMap F (AF F) (Algebra.trace F E (-(form σ J ξ β * form σ K y x))) := by
  rw [symp, hTens_pure, neg_one_mul, ← mul_neg, ← map_neg, ← Algebra.smul_def, map_smul, smul_eq_mul]
  congr 1
  exact (trace_tmul_base_change (AF F) 1 _).trans (one_mul _)

end GlobalTheory.SympPure
