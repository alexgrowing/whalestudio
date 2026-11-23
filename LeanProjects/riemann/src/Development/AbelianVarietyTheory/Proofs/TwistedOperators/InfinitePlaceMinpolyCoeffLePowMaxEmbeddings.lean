import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneLeHtE

open NumberField IsDedekindDomain GlobalTheory.AdelicU
open scoped TensorProduct NNReal
open Classical

namespace GlobalTheory

theorem minpoly_coeff_le_inf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : E) (w : InfinitePlace F) (j : ℕ) :
    w ((minpoly F x).coeff j) ≤ 2 ^ Module.finrank F E *
      ((max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊) : ℝ≥0) : ℝ) ^ Module.finrank F E := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  set M : ℝ≥0 := max 1 (Finset.univ.sup fun τ : EmbOver E w => ‖τ.1 x‖₊) with hM
  set p := minpoly F x
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have h1 : p.Monic := minpoly.monic hx
  have hd : p.natDegree ≤ Module.finrank F E := minpoly.natDegree_le x
  have h3 : ∀ z ∈ (p.map w.embedding).roots, ‖z‖ ≤ (M : ℝ) := by
    intro z hz
    have hz' : z ∈ p.rootSet ℂ := by
      rw [Polynomial.mem_rootSet]
      refine ⟨h1.ne_zero, ?_⟩
      have := (Polynomial.mem_roots (Polynomial.map_monic_ne_zero h1)).1 hz
      rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
      exact this
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly] at hz'
    obtain ⟨ψ, rfl⟩ := hz'
    let τ : EmbOver E w := ⟨ψ.toRingHom, RingHom.ext fun a => ψ.commutes a⟩
    have : ‖ψ x‖₊ ≤ M :=
      le_trans (Finset.le_sup (f := fun τ : EmbOver E w => ‖τ.1 x‖₊) (Finset.mem_univ τ)) (le_max_right _ _)
    exact_mod_cast this
  have key := Polynomial.coeff_le_of_roots_le (f := w.embedding) j h1 (IsAlgClosed.splits _) h3
  rw [Polynomial.coeff_map] at key
  have hw : w (p.coeff j) = ‖w.embedding (p.coeff j)‖ := (InfinitePlace.norm_embedding_eq w _).symm
  rw [hw]
  refine key.trans ?_
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast le_max_left _ _
  have hpow : (M : ℝ) ^ (p.natDegree - j) ≤ (M : ℝ) ^ Module.finrank F E :=
    pow_le_pow_right₀ hM1 (le_trans (Nat.sub_le _ _) hd)
  have hch : ((p.natDegree.choose j : ℕ) : ℝ) ≤ 2 ^ Module.finrank F E := by
    have := (Nat.choose_le_two_pow p.natDegree j).trans (Nat.pow_le_pow_right (by norm_num) hd)
    exact_mod_cast this
  rw [mul_comm]
  exact mul_le_mul hch hpow (by positivity) (by positivity)

end GlobalTheory
