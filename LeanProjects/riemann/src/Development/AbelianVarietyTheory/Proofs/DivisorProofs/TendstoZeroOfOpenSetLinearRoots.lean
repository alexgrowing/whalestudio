import Mathlib
import Formalism.DegreeFormula.FlagDegFormula

open MvPolynomial Formalism.DegreeFormula Filter Topology

namespace GlobalTheory

theorem linRoot_add_smul {ι : Type} [Fintype ι] {N : ℕ} (u w : ι → Fin N → ℝ) (t : ℝ) :
    linRoot (u + t • w) = linRoot u + C t * linRoot w := by
  simp only [linRoot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_neg, neg_add, mul_assoc]

theorem linRoot_add_smul_pow {ι : Type} [Fintype ι] {N : ℕ} (u w : ι → Fin N → ℝ) (t : ℝ)
    (d : ℕ) :
    linRoot (u + t • w) ^ d = ∑ k ∈ Finset.range (d + 1),
      (t ^ k * (d.choose k : ℝ)) • (linRoot w ^ k * linRoot u ^ (d - k)) := by
  rw [linRoot_add_smul, add_comm, add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, mul_pow, ← map_pow, map_mul, map_natCast]
  ring

theorem tendsto_zero_linRoot_pow_of_isOpen {α : Type} (l : Filter α) {ι : Type} [Fintype ι]
    {N : ℕ} (Λ : α → MvPolynomial (ι × Fin N) ℝ →ₗ[ℝ] ℝ) (d : ℕ) (U : Set (ι → Fin N → ℝ))
    (hU : IsOpen U) (hne : U.Nonempty)
    (hlim : ∀ u ∈ U, Tendsto (fun a => Λ a (linRoot u ^ d)) l (𝓝 0))
    (v : ι → Fin N → ℝ) : Tendsto (fun a => Λ a (linRoot v ^ d)) l (𝓝 0) := by
  obtain ⟨u₀, hu₀⟩ := hne
  let T : Submodule ℝ (MvPolynomial (ι × Fin N) ℝ) :=
    { carrier := {P | Tendsto (fun a => Λ a P) l (𝓝 0)}
      add_mem' := fun {P Q} hP hQ => by
        simpa only [Set.mem_setOf_eq, map_add, add_zero] using hP.add hQ
      zero_mem' := by simpa only [Set.mem_setOf_eq, map_zero] using tendsto_const_nhds
      smul_mem' := fun c P hP => by
        simpa only [Set.mem_setOf_eq, map_smul, smul_eq_mul, mul_zero] using hP.const_mul c }
  show linRoot v ^ d ∈ T
  by_contra hv
  obtain ⟨φ, hφv, hφT⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hv inferInstance
  have hφ : ∀ P ∈ T, φ P = 0 := fun P hP =>
    (Submodule.mem_bot ℝ).mp (hφT ▸ Submodule.mem_map_of_mem hP)
  set w := v - u₀ with hw
  let q : Polynomial ℝ := ∑ k ∈ Finset.range (d + 1),
    Polynomial.monomial k ((d.choose k : ℝ) * φ (linRoot w ^ k * linRoot u₀ ^ (d - k)))
  have hq : ∀ t : ℝ, q.eval t = φ (linRoot (u₀ + t • w) ^ d) := by
    intro t
    rw [linRoot_add_smul_pow, map_sum]
    simp only [q, Polynomial.eval_finset_sum, Polynomial.eval_monomial, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hopen : {t : ℝ | u₀ + t • w ∈ U} ∈ 𝓝 (0 : ℝ) :=
    (hU.preimage (by fun_prop)).mem_nhds (by simpa using hu₀)
  have hq0 : q = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot q ((infinite_of_mem_nhds (0 : ℝ) hopen).mono ?_)
    intro t ht
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, hq]
    exact hφ _ (hlim _ ht)
  apply hφv
  have h1 := hq 1
  rw [hq0, one_smul, hw, add_sub_cancel, Polynomial.eval_zero] at h1
  exact h1.symm

end GlobalTheory
