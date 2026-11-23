import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLinearDisjoint

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_sum_map_mul_eq_zero_of_linearIndependent : ∀ (k Ω D : Type) [Field k] [Field Ω] [Field D] [Algebra k Ω] [IsGalois k Ω] (o : Ω →+* D) (F : Subfield D), (∀ x : Ω, o x ∈ F ↔ x ∈ (algebraMap k Ω).range) → ∀ (m : ℕ) (x : Fin m → Ω), LinearIndependent k x → ∀ b : Fin m → D, (∀ i, b i ∈ F) → ∑ i, o (x i) * b i = 0 → ∀ i, b i = 0 := by
  first | exact @GlobalTheory.GalDisj.galois_linearDisjoint | exact GlobalTheory.GalDisj.galois_linearDisjoint | (intros; apply GlobalTheory.GalDisj.galois_linearDisjoint <;> assumption)
