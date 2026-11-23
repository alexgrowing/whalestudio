import Mathlib
import Formalism.LocalRingCardinality.DataHost
import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow
import Development.AutomorphicArithmetic.WeightCongruences.ExistsShiftWeightCongruenceLtTorsionOrder
import Development.AutomorphicArithmetic.WeightCongruences.ProdCmTypeEqNormAndWeightCongruenceOne

open NumberField Formalism.BasicNotions

namespace UpperTheory.Mu

variable {R : Ranks} (H : Host R) {ι : Type} [Fintype ι] (eT : ι ≃ R.Psi)

theorem mu_one : MU (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) (fun _ => 1) := (UpperTheory.prod_cmType_eq_norm_and_weightCongruence_one R H ι eT).2

theorem mu_const (c : ℤ) : MU (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) (fun _ => c) := (mu_one H eT).const c

theorem prod_emb_zpow {z : H.E} (hz : ∃ m : ℕ, 0 < m ∧ z ^ m = 1) (c : ℤ) :
    ∏ τ, H.emb ((eT τ : R.Psi) : R.GG) z ^ c = 1 := mu_const H eT c z hz

theorem prod_emb {z : H.E} (hz : ∃ m : ℕ, 0 < m ∧ z ^ m = 1) : ∏ τ, H.emb ((eT τ : R.Psi) : R.GG) z = 1 := by
  simpa using prod_emb_zpow H eT hz 1

theorem prod_emb_inv {z : H.E} (hz : ∃ m : ℕ, 0 < m ∧ z ^ m = 1) : ∏ τ, (H.emb ((eT τ : R.Psi) : R.GG) z)⁻¹ = 1 := by
  rw [Finset.prod_inv_distrib, prod_emb H eT hz, inv_one]

theorem muq_of_const {e : ι → ℚ} (c : ℤ) (he : ∀ τ, e τ = c) : MUQ (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) e :=
  ⟨fun _ => c, he, mu_const H eT c⟩

theorem muq_of_parallel {a : ι → ℤ} (ha : MU (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) a) {e : ι → ℚ} (c : ℤ)
    (he : ∀ τ, e τ = a τ + c) : MUQ (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) e :=
  ⟨fun τ => a τ + c, fun τ => by rw [he]; push_cast; rfl, ha.add_const (mu_one H eT) c⟩

theorem exists_shift [DecidableEq ι] (a : ι → ℤ) (τ₀ : ι) : ∃ s : ℕ, s < Units.torsionOrder H.E ∧
    MU (fun τ => H.emb ((eT τ : R.Psi) : R.GG)) (fun τ => a τ + if τ = τ₀ then (s : ℤ) else 0) :=
  UpperTheory.exists_shift_weightCongruence_lt_torsionOrder H.E ℂ ι _ a τ₀

end UpperTheory.Mu
