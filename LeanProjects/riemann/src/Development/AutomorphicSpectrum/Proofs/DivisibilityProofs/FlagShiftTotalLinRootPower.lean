import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE
open MvPolynomial Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.LinPow

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

theorem degFl_C_mul (c : ℝ) (F : RP Ψ N) : degFl (C c * F) = c * degFl F := by
  unfold degFl
  simp_rw [coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ => by ring

theorem pderiv_linRoot (u : Wt Ψ N) (τ : Ψ) (i : Fin N) :
    pderiv (τ, i) (linRoot u) = -C (u τ i) := by
  simp [linRoot, pderiv_X, Pi.single_apply]

theorem pderiv_linRoot_pow (u : Wt Ψ N) (τ : Ψ) (i : Fin N) (D : ℕ) :
    pderiv (τ, i) (linRoot u ^ (D + 1)) =
      C (-(((D : ℝ) + 1) * u τ i)) * linRoot u ^ D := by
  rw [Derivation.leibniz_pow, pderiv_linRoot]
  simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul]
  simp only [map_neg, map_mul, map_add, map_natCast, map_one]
  push_cast
  ring

private lemma degFl_sum' {ι : Type*} (s : Finset ι) (f : ι → RP Ψ N) :
    degFl (∑ i ∈ s, f i) = ∑ i ∈ s, degFl (f i) := by
  unfold degFl
  simp_rw [coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem degFl_sum_pderiv (u : Wt Ψ N) (τ : Ψ) (s : Finset (Fin N)) :
    degFl (∑ i ∈ s, pderiv (τ, i) (linRoot u ^ (dimFl Ψ N + 1))) =
      -(((dimFl Ψ N : ℝ) + 1) * flagDeg u * ∑ i ∈ s, u τ i) := by
  rw [degFl_sum']
  simp_rw [pderiv_linRoot_pow, degFl_C_mul]
  simp only [flagDeg]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.CompanionTheory.Ar.Top.LinPow

theorem GlobalTheory.CompanionTheory.Ar.Top.Sh_Tot_linRoot_pow :
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (τ : Ψ) (u : Wt Ψ N), Sh j τ (linRoot u ^ (dimFl Ψ N + 1)) = -(((dimFl Ψ N : ℝ) + 1) * flagDeg u * ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), u τ i) ∧ Tot τ (linRoot u ^ (dimFl Ψ N + 1)) = -(((dimFl Ψ N : ℝ) + 1) * flagDeg u * ∑ i, u τ i) := by
  intro Ψ _ _ N j τ u
  exact ⟨GlobalTheory.CompanionTheory.Ar.Top.LinPow.degFl_sum_pderiv u τ _,
    GlobalTheory.CompanionTheory.Ar.Top.LinPow.degFl_sum_pderiv u τ Finset.univ⟩
