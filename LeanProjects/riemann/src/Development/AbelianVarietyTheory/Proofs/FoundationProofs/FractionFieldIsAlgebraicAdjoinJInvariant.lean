import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralOverJInvariantOfHasSomeLevelOverStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOverStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

def constHom {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) : Ω →+* ring ε.range where
  toFun c := ⟨fun _ => ε c, mem_ring_of_inR ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).2 _ ⟨c, rfl⟩)⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

def evAt (E : Subring ℂ) (τ : ℍ) : ring E →+* ℂ := (Pi.evalRingHom (fun _ : ℍ => ℂ) τ).comp (ring E).subtype

theorem evAt_apply (E : Subring ℂ) (τ : ℍ) (x : ring E) : evAt E τ x = (x : ℍ → ℂ) τ := rfl

theorem evAt_comp_constHom {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (τ : ℍ) :
    (evAt ε.range τ).comp (constHom ε) = ε := by
  ext c; rfl

theorem io_comp_constHom {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Frac Ω ε) :
    T.io.comp (constHom ε) = algebraMap Ω T.K := by
  ext c; exact T.io_c c _ rfl

theorem isIntegral_io_adjoin_j (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε)
    (a : ring ε.range) (ha : (a : ℍ → ℂ) = jT) (b : ring ε.range) :
    IsIntegral (IntermediateField.adjoin Ω {T.io a}) (T.io b) := by
  set L := IntermediateField.adjoin Ω {T.io a}
  obtain ⟨n, c, hc, hrel⟩ := GlobalTheory.T.integral_over_jInvariant_of_hasSomeLevelOver ε.range b (((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 b).1 b.2)
  have hl : ∀ i, c i ∈ Polynomial.lifts ε := fun i =>
    (Polynomial.lifts_iff_coeff_lifts _).2 fun k => RingHom.mem_range.1 (hc i k)
  choose d hd using fun i => (Polynomial.mem_lifts (c i)).1 (hl i)
  let xa : L := ⟨T.io a, IntermediateField.mem_adjoin_simple_self Ω _⟩
  let φ : Polynomial Ω →ₐ[Ω] L := Polynomial.aeval xa

  have hr : b ^ n + ∑ i, (d i).eval₂ (constHom ε) a * b ^ (i : ℕ) = 0 := by
    apply Subtype.ext; funext τ
    have h := hrel τ
    have key : evAt ε.range τ (b ^ n + ∑ i, (d i).eval₂ (constHom ε) a * b ^ (i : ℕ)) = 0 := by
      simp only [map_add, map_sum, map_mul, map_pow, Polynomial.hom_eval₂, evAt_comp_constHom,
        evAt_apply, ha]
      simpa [← Polynomial.eval_map, hd] using h
    simpa [evAt_apply] using key
  have hK : T.io b ^ n + ∑ i, Polynomial.aeval (T.io a) (d i) * T.io b ^ (i : ℕ) = 0 := by
    have := congrArg T.io hr
    simp only [map_add, map_sum, map_mul, map_pow, Polynomial.hom_eval₂, io_comp_constHom, map_zero] at this
    simpa [Polynomial.aeval_def] using this
  refine ⟨Polynomial.X ^ n + ∑ i, Polynomial.C (φ (d i)) * Polynomial.X ^ (i : ℕ),
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _), ?_⟩
  have hφ : ∀ i, algebraMap L T.K (φ (d i)) = Polynomial.aeval (T.io a) (d i) := fun i => by
    show L.val (φ (d i)) = _
    rw [← Polynomial.aeval_algHom_apply L.val xa (d i)]
    rfl
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, hφ]
  exact hK

theorem frac_isAlgebraic_adjoin_j : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε)
    (a : GlobalTheory.FN.ring ε.range), (a : ℍ → ℂ) = jT → ∀ f : T.K, IsAlgebraic (IntermediateField.adjoin Ω {T.io a}) f := by
  intro Ω _ _ _ ε T a ha f
  obtain ⟨x, y, hy, hxy⟩ := T.io_surj f
  have hy' : T.io y ≠ 0 := fun h => hy (T.io_inj (h.trans (map_zero T.io).symm))
  have hf : f = T.io x * (T.io y)⁻¹ := by rw [← hxy, mul_inv_cancel_right₀ hy']
  rw [hf]
  exact (isIntegral_io_adjoin_j Ω ε T a ha x).isAlgebraic.mul (isIntegral_io_adjoin_j Ω ε T a ha y).isAlgebraic.inv

end GlobalTheory.FN
