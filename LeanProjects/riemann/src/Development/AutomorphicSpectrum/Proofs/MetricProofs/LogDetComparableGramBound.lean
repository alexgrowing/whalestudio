import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open Matrix
open scoped ComplexOrder

private theorem sum_eq_sum_comp_of_eq_zero_of_forall_ne {ι κ M : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [AddCommMonoid M] (v : κ → ι) (hv : Function.Injective v) (f : ι → M)
    (hf : ∀ i, (∀ a, i ≠ v a) → f i = 0) :
    ∑ i, f i = ∑ a, f (v a) := by
  rw [← Finset.sum_image (f := f) (s := Finset.univ) (g := v) (fun a _ b _ h => hv h)]
  exact (Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => hf i (fun a hia =>
    hi (Finset.mem_image.mpr ⟨a, Finset.mem_univ a, hia.symm⟩)))).symm

theorem gramOf_mul {N : ℕ} (hd : Fin N → ℝ) (u g : Matrix (Fin N) (Fin N) ℂ) :
    gramOf hd (u * g) = gᴴ * gramOf hd u * g := by
  simp only [GlobalTheory.CompanionTheory.Ar.PB.gramOf, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem head_conj_mul {N : ℕ} {P : Type*} [Fintype P] (v : P → Fin N)
    (hv : Function.Injective v) (hdown : ∀ (i : Fin N) (c : P), (∀ a, i ≠ v a) → v c < i)
    (G b : Matrix (Fin N) (Fin N) ℂ) (hb : b.BlockTriangular id) :
    (bᴴ * G * b).submatrix v v = (b.submatrix v v)ᴴ * G.submatrix v v * b.submatrix v v := by
  ext p q
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [sum_eq_sum_comp_of_eq_zero_of_forall_ne v hv]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    congr 1
    rw [sum_eq_sum_comp_of_eq_zero_of_forall_ne v hv]
    intro i hi
    rw [hb (hdown i p hi), star_zero, zero_mul]
  · intro j hj
    rw [hb (hdown j q hj), mul_zero]

theorem gramLog_inv (N : ℕ) (hd : Fin N → ℝ) (k : ℕ) (g u b : Matrix (Fin N) (Fin N) ℂ) :
    (gramOf hd u = diagonal (fun i => ((hd i : ℝ) : ℂ)) → gramLog hd k (u * g) = gramLog hd k g) ∧
    (b.BlockTriangular id → IsUnit b.det → (gramHead hd k g).det ≠ 0 →
      gramLog hd k (g * b) = gramLog hd k g +
        ∑ a : Fin N, if (a : ℕ) < k then Real.log ‖b a a‖ else 0) := by
  constructor
  · intro h
    simp only [GlobalTheory.CompanionTheory.Ar.PB.gramLog, GlobalTheory.CompanionTheory.Ar.PB.gramHead]
    rw [GlobalTheory.CompanionTheory.Ar.PB.gramOf_mul, h, GlobalTheory.CompanionTheory.Ar.PB.gramOf]
  · intro hb hdet hM
    have hdown : ∀ (i : Fin N) (c : {a : Fin N // (a : ℕ) < k}),
        (∀ a : {a : Fin N // (a : ℕ) < k}, i ≠ a.val) → c.val < i := by
      intro i c hi
      have hik : ¬ (i : ℕ) < k := fun h => hi ⟨i, h⟩ rfl
      rw [Fin.lt_def]
      exact lt_of_lt_of_le c.2 (not_lt.mp hik)
    have hbk : (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N)
        Subtype.val).IsUpperTriangular :=
      fun i j hij => hb (Subtype.coe_lt_coe.mpr hij)
    have hdiag : ∀ i, b i i ≠ 0 := by
      intro i hi
      have h0 : b.det = 0 := by
        rw [Matrix.det_of_upperTriangular hb]
        exact Finset.prod_eq_zero (Finset.mem_univ i) hi
      rw [h0] at hdet
      exact not_isUnit_zero hdet
    have hdetk : (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N)
        Subtype.val).det = ∏ a : {a : Fin N // (a : ℕ) < k}, b a a :=
      Matrix.det_of_upperTriangular hbk
    have hminor : GlobalTheory.CompanionTheory.Ar.PB.gramHead hd k (g * b) =
        (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) Subtype.val)ᴴ *
          GlobalTheory.CompanionTheory.Ar.PB.gramHead hd k g *
            b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) Subtype.val := by
      simp only [GlobalTheory.CompanionTheory.Ar.PB.gramHead]
      rw [GlobalTheory.CompanionTheory.Ar.PB.gramOf_mul]
      exact GlobalTheory.CompanionTheory.Ar.PB.head_conj_mul Subtype.val
        Subtype.val_injective hdown _ b hb
    have hB0 : ∏ a : {a : Fin N // (a : ℕ) < k}, b a a ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun a _ => hdiag a)
    have hnorm : ‖(GlobalTheory.CompanionTheory.Ar.PB.gramHead hd k (g * b)).det‖ =
        ‖∏ a : {a : Fin N // (a : ℕ) < k}, b a a‖ ^ 2 *
          ‖(GlobalTheory.CompanionTheory.Ar.PB.gramHead hd k g).det‖ := by
      rw [hminor, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hdetk, norm_mul,
        norm_mul, norm_star]
      ring
    have hsum : (∑ a : Fin N, if (a : ℕ) < k then Real.log ‖b a a‖ else 0) =
        ∑ a : {a : Fin N // (a : ℕ) < k}, Real.log ‖b a a‖ := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (fun a => by simp) _
    simp only [GlobalTheory.CompanionTheory.Ar.PB.gramLog]
    rw [hnorm, Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr hB0)) (norm_ne_zero_iff.mpr hM),
      Real.log_pow, norm_prod, Real.log_prod (s := Finset.univ)
        (f := fun a : {a : Fin N // (a : ℕ) < k} => ‖b a a‖) (fun a _ => norm_ne_zero_iff.mpr (hdiag a)),
      hsum]
    push_cast
    ring

end GlobalTheory.CompanionTheory.Ar.PB
