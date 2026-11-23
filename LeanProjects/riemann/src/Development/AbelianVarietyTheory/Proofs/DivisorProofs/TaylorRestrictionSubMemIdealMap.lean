import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalProperties

open TopologicalSpace TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnPer

section General

variable {R H : Type} [CommRing R] [Algebra ℂ R] [CommRing H] [Algebra ℂ H]

def redCoef (π : R →ₐ[ℂ] ℂ) : R ⊗[ℂ] H →ₐ[ℂ] H :=
  Algebra.TensorProduct.lift ((Algebra.ofId ℂ H).comp π) (AlgHom.id ℂ H) (fun _ _ ↦ Commute.all _ _)

theorem redCoef_tmul (π : R →ₐ[ℂ] ℂ) (d : R) (y : H) :
    redCoef π (d ⊗ₜ[ℂ] y) = algebraMap ℂ H (π d) * y := by
  simp [redCoef, Algebra.TensorProduct.lift_tmul]

theorem sub_redCoef_mem (π : R →ₐ[ℂ] ℂ) (x : R ⊗[ℂ] H) :
    x - 1 ⊗ₜ[ℂ] redCoef π x ∈
      (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] H) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul d y =>
    rw [redCoef_tmul]
    have e : d ⊗ₜ[ℂ] y - (1 : R) ⊗ₜ[ℂ] (algebraMap ℂ H (π d) * y) =
        (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] H) (d - algebraMap ℂ R (π d)) * ((1 : R) ⊗ₜ[ℂ] y) := by
      rw [Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
        TensorProduct.sub_tmul, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul, TensorProduct.smul_tmul]
    rw [e]
    refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes]
    simp
  | add x y hx hy =>
    have e : x + y - 1 ⊗ₜ[ℂ] redCoef π (x + y) = (x - 1 ⊗ₜ[ℂ] redCoef π x) + (y - 1 ⊗ₜ[ℂ] redCoef π y) := by
      rw [map_add, TensorProduct.tmul_add]; abel
    rw [e]; exact Ideal.add_mem _ hx hy

end General

theorem fn_redCoef {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} {R : Type} [CommRing R]
    [Algebra ℂ R] (π : R →ₐ[ℂ] ℂ) (x : R ⊗[ℂ] Hol W) {p : E} (hp : p ∈ W) :
    (redCoef π x).fn p = π (evT R p hp x) := by
  rw [← Hol.ev_apply p hp]
  change ((Hol.ev p hp).comp (redCoef π)) x = (π.comp (evT R p hp)) x
  congr 1
  refine Algebra.TensorProduct.ext' fun d y ↦ ?_
  simp only [AlgHom.comp_apply, redCoef_tmul, evT, Algebra.TensorProduct.lift_tmul, map_mul, AlgHom.commutes,
    AlgHom.id_apply, Algebra.ofId_apply]
  simp

theorem taylor_red {I : Type} [Fintype I] [DecidableEq I] {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ)
    (t : I → R) (π : R →ₐ[ℂ] ℂ) (ht : ∀ i, π (t i) = 0) (f : (I → ℂ) → ℂ) :
    π (GlobalTheory.PeriodFamily.taylor N t f) = f 0 := by
  have h := GlobalTheory.PeriodFamily.taylor_sub_value_mem_span N t f
  have hle : Ideal.span (Set.range t) ≤ RingHom.ker π := by
    rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact ht i
  have := hle h
  rw [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at this
  simpa using this

theorem taylor_reduces_to_slice : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {R : Type} [CommRing R] [Algebra ℂ R] (N : ℕ) (t : I → R) (π : R →ₐ[ℂ] ℂ), (∀ i, π (t i) = 0) → ∀ (W : Opens (Tot I g)) (W₀ : Opens (Tot Empty g)), (∀ p ∈ W₀, (((0 : I → ℂ), p.2) : Tot I g) ∈ W) → ∀ ρ : Hol W →+* R ⊗[ℂ] Hol W₀, IsTay N t ρ → ∀ (h : Hol W) (h₀ : Hol W₀), (∀ p ∈ W₀, h₀.fn p = h.fn (0, p.2)) → ρ h - 1 ⊗ₜ[ℂ] h₀ ∈ (RingHom.ker π).map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol W₀) := by
  intro I _ _ g R _ _ N t π ht W W₀ _ ρ hρ h h₀ hh₀
  have hq : redCoef π (ρ h) = h₀ := Hol.ext_fn fun p hp ↦ by
    rw [fn_redCoef π _ hp, hρ h p hp, taylor_red N t π ht, hh₀ p hp]
  have := sub_redCoef_mem (H := Hol W₀) π (ρ h)
  rwa [hq] at this

end GlobalTheory.AnPer
