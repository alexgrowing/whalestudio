import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTamagawa
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCountRecursionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCountOneEqResidueOrderStatement
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published

namespace GlobalTheory.TamSU

theorem locVol_selfDual_eq_locFactor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), 2 ≤ r → Unr E → SelfDualLat G Λ →
    ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
      locVol (IsCMField.complexConj E).toAlgHom Gᵀ Λ v = locFactor E r v := by
  intro E _ _ _ r G Λ hr hU hS v
  set q : ℝ := (Ideal.absNorm v.asIdeal : ℝ) with hq
  have hq0 : q ≠ 0 := by
    rw [hq, Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have hconst : ∀ k, 1 ≤ k →
      (locCount (IsCMField.complexConj E).toAlgHom Gᵀ Λ v k : ℝ) / q ^ (k * (r ^ 2 - 1)) = locFactor E r v := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      rw [GlobalTheory.T.local_count_one_eq_residue_order E r G Λ hr hU hS v, one_mul]
      rfl
    | succ k hk ih =>
      rw [← ih, GlobalTheory.T.local_count_recursion E r G Λ hr hU hS v k hk, Nat.cast_mul, Nat.cast_pow, ← hq, add_mul, one_mul, pow_add]
      field_simp
  unfold locVol
  apply Tendsto.limUnder_eq
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact (hconst k hk).symm

end GlobalTheory.TamSU
