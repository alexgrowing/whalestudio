import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.HasPres

open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct UpperTheory.KN

theorem _root_.UpperTheory.KN.exists_pow_uniformizer_smul_eq_zero_quotient_lattice :
    ∀ {O LL : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field LL] [Algebra O LL] [IsFractionRing O LL]
      (lam : O), Irreducible lam → ∀ {k : ℕ} {Y : Type} [AddCommGroup Y] [Module O Y] [Module.Finite O Y]
      (φ : Y →ₗ[O] ((Fin k → LL) ⧸ stdG O LL k)), ∃ a : ℕ, ∀ y, lam ^ a • φ y = 0 := by
  classical
  intro O LL _ _ _ _ _ _ lam hlam k Y _ _ _ φ
  have hz : ∀ z : LL, ∃ a : ℕ, ∃ r : O, algebraMap O LL r = lam ^ a • z := by
    intro z
    obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := O) z
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hlam
    refine ⟨m, r * ↑u⁻¹, ?_⟩
    have hU : algebraMap O LL ↑u⁻¹ * algebraMap O LL ↑u = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hU0 : algebraMap O LL ↑u ≠ 0 := right_ne_zero_of_mul_eq_one hU
    have hinv : algebraMap O LL ↑u⁻¹ = (algebraMap O LL ↑u)⁻¹ := eq_inv_of_mul_eq_one_left hU
    have hL0 : algebraMap O LL (lam ^ m) ≠ 0 := by
      rw [map_pow]
      exact pow_ne_zero _ fun h => hlam.ne_zero ((IsFractionRing.injective O LL) (h.trans (map_zero _).symm))
    rw [Algebra.smul_def, map_mul, map_mul, hinv]
    field_simp
  have hq : ∀ x : (Fin k → LL) ⧸ stdG O LL k, ∃ a : ℕ, lam ^ a • x = 0 := by
    intro x
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    choose a r hr using fun i => hz (v i)
    refine ⟨∑ i, a i, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, stdG, LinearMap.mem_range]
    refine ⟨fun i => lam ^ (∑ j, a j - a i) * r i, funext fun i => ?_⟩
    have hle : a i ≤ ∑ j, a j := Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i)
    show algebraMap O LL (lam ^ (∑ j, a j - a i) * r i) = lam ^ (∑ j, a j) • v i
    rw [map_mul, hr i, ← Algebra.smul_def, smul_smul, pow_sub_mul_pow lam hle]
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := O) (M := Y)
  choose a ha using fun y => hq (φ y)
  refine ⟨∑ y ∈ s, a y, fun y => ?_⟩
  have hmem : y ∈ Submodule.span O (s : Set Y) := hs ▸ Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    rw [← pow_sub_mul_pow lam (Finset.single_le_sum (fun j _ => Nat.zero_le (a j)) hx), mul_smul, ha x,
      smul_zero]
  | zero => rw [map_zero, smul_zero]
  | add x z _ _ h1 h2 => rw [map_add, smul_add, h1, h2, add_zero]
  | smul c x _ h => rw [map_smul, smul_comm, h, smul_zero]
