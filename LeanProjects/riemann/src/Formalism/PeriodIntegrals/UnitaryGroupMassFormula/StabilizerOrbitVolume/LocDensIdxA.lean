import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensIdxH

noncomputable section

namespace PI.VolStabSW

open scoped TensorProduct
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace IdxHW

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E)

theorem crd_sigR (y : Fv F v ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (sigR (Fv F v) σ y) k =
      ∑ l, algebraMap F (Fv F v) (b.repr (σ (b l)) k) *
        (Algebra.TensorProduct.basis (Fv F v) b).repr y l := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    have hs : sigR (Fv F v) σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := by
      simp [sigR, Algebra.TensorProduct.map_tmul]
    rw [hs]
    simp only [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul]
    have he : σ e = ∑ l, b.repr e l • σ (b l) := by
      have h := congrArg σ (b.sum_repr e)
      rw [map_sum] at h
      simp only [map_smul] at h
      exact h.symm
    rw [he, map_sum]
    simp only [map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
      map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  | add x y hx hy =>
    rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add]
    simp only [Finsupp.add_apply, mul_add, Finset.sum_add_distrib]

theorem eventually_int (x : F) :
    ∀ᶠ v in cofinite, algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F :=
  (algebraMap F (FiniteAdeleRing (𝓞 F) F) x).eventually

end IdxHW

theorem fix2 {F : Type} [Field F] (C : Matrix (Fin 2) (Fin 2) F) (hC : C ≠ 1) (u : Fin 2 → F)
    (hu : u ≠ 0) (hCu : Matrix.mulVec C u = u) :
    ∃ k0 k1 : Fin 2, k0 ≠ k1 ∧ u k0 ≠ 0 ∧ ∃ ρ : F, ∀ (K : Type) [Field K] [Algebra F K]
      (x : Fin 2 → K), Matrix.mulVec (C.map (algebraMap F K)) x = x → x k1 = algebraMap F K ρ * x k0 := by
  classical
  obtain ⟨r, hr⟩ : ∃ r : Fin 2, (C - 1) r 0 ≠ 0 ∨ (C - 1) r 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hC
    have : C - 1 = 0 := by
      ext i j
      fin_cases j
      · exact (h i).1
      · exact (h i).2
    exact sub_eq_zero.1 this
  have hrow : ∀ (K : Type) [Field K] [Algebra F K] (x : Fin 2 → K),
      Matrix.mulVec (C.map (algebraMap F K)) x = x →
        algebraMap F K ((C - 1) r 0) * x 0 + algebraMap F K ((C - 1) r 1) * x 1 = 0 := by
    intro K _ _ x hx
    have h := congrFun hx r
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply] at h
    simp only [Matrix.sub_apply, Matrix.one_apply, map_sub]
    fin_cases r <;> simp at h ⊢ <;> linear_combination h
  have hrowu := hrow F u (by simpa using hCu)
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hrowu
  by_cases hβ : (C - 1) r 1 ≠ 0
  · refine ⟨0, 1, by decide, ?_, -((C - 1) r 0) / (C - 1) r 1, fun K _ _ x hx => ?_⟩
    · intro h0
      apply hu
      have h1 : u 1 = 0 := by
        rw [h0, mul_zero, zero_add] at hrowu
        exact (mul_eq_zero.1 hrowu).resolve_left hβ
      ext i
      fin_cases i
      · exact h0
      · exact h1
    · have h := hrow K x hx
      have hβK : algebraMap F K ((C - 1) r 1) ≠ 0 := by
        rw [Ne, map_eq_zero_iff _ (algebraMap F K).injective]; exact hβ
      rw [map_div₀, map_neg]
      field_simp
      linear_combination h
  · push Not at hβ
    have hα : (C - 1) r 0 ≠ 0 := hr.resolve_right (by rw [hβ]; exact fun h => h rfl)
    have hu0 : u 0 = 0 := by
      rw [hβ, zero_mul, add_zero] at hrowu
      exact (mul_eq_zero.1 hrowu).resolve_left hα
    refine ⟨1, 0, by decide, ?_, 0, fun K _ _ x hx => ?_⟩
    · intro h1
      apply hu
      ext i
      fin_cases i
      · exact hu0
      · exact h1
    · have h := hrow K x hx
      rw [hβ, map_zero, zero_mul, add_zero] at h
      have hαK : algebraMap F K ((C - 1) r 0) ≠ 0 := by
        rw [Ne, map_eq_zero_iff _ (algebraMap F K).injective]; exact hα
      rw [map_zero, zero_mul]
      exact (mul_eq_zero.1 h).resolve_left hαK

end PI.VolStabSW
