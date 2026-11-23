import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJEqSubmatrix
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem xiCoef_self {Ψ : Type} [DecidableEq Ψ] {N : ℕ} (τ : Ψ) (a i : Fin N) :
    xiCoef τ a (τ, i) = xiCoef () a ((), i) := by
  simp [xiCoef]

theorem xiCoef_ne {Ψ : Type} [DecidableEq Ψ] {N : ℕ} {τ τ' : Ψ} (h : τ' ≠ τ) (a i : Fin N) :
    xiCoef τ a (τ', i) = 0 := by
  simp [xiCoef, h]

theorem xi_sum_potentials : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (τ : Ψ) (a b ca cb : Fin N) (Gf hf : Ψ → Matrix (Fin N) (Fin N) ℂ) (u : Ψ × Fin N → ℝ) (t : ℂ) (G₂ : Matrix (Fin 2) (Fin 2) ℂ), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsBlockDiag j (Gf τ) → (Gf τ).PosDef → IsBlockDiag j (hf τ) → (hf τ).det ≠ 0 → (∀ r s : Fin 2, G₂ r s = minorIJ ((hf τ)ᴴ * Gf τ * hf τ) (insert (![ca, cb] r) ((stepCols N j a).erase ca)) (insert (![ca, cb] s) ((stepCols N j a).erase ca)) / minorIJ ((hf τ)ᴴ * Gf τ * hf τ) ((stepCols N j a).erase ca) ((stepCols N j a).erase ca)) → ∑ p, (xiCoef τ a p : ℝ) * (blockPot j p.2 (Gf p.1) (if p.1 = τ then hf τ * (1 + Matrix.single cb ca t) else hf p.1) - u p) = xiPot G₂ t - ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * ((if IsProperStep N j i then 0 else Real.log ‖facOf N j a (hf τ) i‖) + u (τ, i)) := by
  intro Ψ _ _ N j τ a b ca cb Gf hf u t G₂ hj hb hcase hca hcb hG hGp hh hdet hG₂
  obtain ⟨G₃, -, e3, key⟩ := norm_three_steps N j a b ca cb (Gf τ) (hf τ) hj hb hcase hca hcb hG hGp hh hdet
  have hGG : G₃ = G₂ := Matrix.ext fun r s => (e3 r s).trans (hG₂ r s).symm
  subst hGG
  have hsum : ∑ p, (xiCoef τ a p : ℝ) * (blockPot j p.2 (Gf p.1) (if p.1 = τ then hf τ * (1 + Matrix.single cb ca t) else hf p.1) - u p) =
      ∑ i : Fin N, (xiCoef τ a (τ, i) : ℝ) * (blockPot j i (Gf τ) (hf τ * (1 + Matrix.single cb ca t)) - u (τ, i)) := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ]
    · simp
    · intro τ' _ hne
      simp [xiCoef_ne hne]
    · simp
  rw [hsum, ← key t, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [xiCoef_self]
  simp only [facOf]
  ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
