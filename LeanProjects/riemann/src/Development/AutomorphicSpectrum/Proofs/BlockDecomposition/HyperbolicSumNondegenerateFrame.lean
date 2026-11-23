import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem hypOne_mul_hypOne_of_mul_eq_one {K : Type} [Field K] {M : ℕ} {A B : Matrix (Fin M) (Fin M) K}
    (h : A * B = 1) : hypOne A * hypOne B = 1 := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_succ, Fin.sum_univ_succ]
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
  all_goals
    simp [hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
      hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one, hypOne_rest_rest, Matrix.one_apply,
      ← Matrix.mul_apply, h, Fin.ext_iff]

theorem isHermND_hypOne {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) : IsHermND σ (hypOne J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i <;>
      refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun j => ?_) j) j
    all_goals first
      | exact hJ.1 i j
      | simp [hypOne_zero_zero, hypOne_zero_one, hypOne_one_zero, hypOne_one_one, hypOne_zero_rest,
          hypOne_one_rest, hypOne_rest_zero, hypOne_rest_one]
  · have hu : IsUnit J.det := isUnit_iff_ne_zero.mpr hJ.2
    have h1 : hypOne J * hypOne J⁻¹ = 1 :=
      hypOne_mul_hypOne_of_mul_eq_one (Matrix.mul_nonsing_inv J hu)
    intro h0
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one h2

theorem e0_mem_framesE {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) :
    e0 E M ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := by
  refine ⟨linearIndependent_unique_iff.2 ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp [e0] at this
  · ext a b
    simp [gramE, hE, hform, e0, Fin.sum_univ_succ, hypOne_zero_zero]

theorem hypOne_isHermND_and_e0_mem (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E) (_hσ : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) :
    IsHermND σ (hypOne J) ∧ e0 E M ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) :=
  ⟨isHermND_hypOne σ hJ, e0_mem_framesE σ J⟩

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep
