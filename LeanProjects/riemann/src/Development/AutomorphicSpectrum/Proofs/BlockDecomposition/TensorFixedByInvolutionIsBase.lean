import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorFieldOrSplitIdempotent
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin

theorem sigR_fixed_eq_algebraMap : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (a : K ⊗[F] E),
    sigR K σ a = a → ∃ x : K, algebraMap K (K ⊗[F] E) x = a := by
  intro F E _ _ _ _ _ σ h K _ _ a ha
  obtain ⟨θ, d, B, hθ, hd, hσθ, hsq, hB0, hB1⟩ := GlobalTheory.CompanionTheory.SaGen.Dichotomy.exists_theta h
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  let C : Module.Basis (Fin 2) K (K ⊗[F] E) := Algebra.TensorProduct.basis K B
  have hC0 : C 0 = 1 := by
    simp only [C, Algebra.TensorProduct.basis_apply, hB0]
    rfl
  have hC1 : C 1 = (1 : K) ⊗ₜ[F] θ := by
    simp only [C, Algebra.TensorProduct.basis_apply, hB1]
  have hsK : ∀ x : K, sigR K σ (algebraMap K (K ⊗[F] E) x) = algebraMap K (K ⊗[F] E) x := by
    intro x
    change Algebra.TensorProduct.map (AlgHom.id F K) σ (algebraMap K (K ⊗[F] E) x) = _
    simp [Algebra.TensorProduct.algebraMap_apply]
  have hsT : sigR K σ ((1 : K) ⊗ₜ[F] θ) = -((1 : K) ⊗ₜ[F] θ) := by
    change Algebra.TensorProduct.map (AlgHom.id F K) σ ((1 : K) ⊗ₜ[F] θ) = _
    rw [Algebra.TensorProduct.map_tmul, hσθ, TensorProduct.tmul_neg]
    rfl
  have hz := C.sum_repr a
  rw [Fin.sum_univ_two, hC0, hC1, Algebra.smul_def, Algebra.smul_def, mul_one] at hz
  generalize C.repr a 0 = x at hz
  generalize C.repr a 1 = y at hz
  subst hz
  rw [map_add, map_mul, hsK, hsK, hsT] at ha
  have h2 : algebraMap K (K ⊗[F] E) 0 + algebraMap K (K ⊗[F] E) (2 * y) * ((1 : K) ⊗ₜ[F] θ) = 0 := by
    rw [map_zero, map_mul, map_ofNat]
    linear_combination -ha
  have hl := Fintype.linearIndependent_iff.1 C.linearIndependent ![0, 2 * y] (by
    rw [Fin.sum_univ_two, hC0, hC1]
    simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Algebra.smul_def, mul_one] using h2)
  have hy : y = 0 := by
    have := hl 1
    simp only [Matrix.cons_val_one] at this
    exact (mul_eq_zero.1 this).resolve_left two_ne_zero
  exact ⟨x, by rw [hy, map_zero, zero_mul, add_zero]⟩

end GlobalTheory.CompanionTheory.KFin

end
