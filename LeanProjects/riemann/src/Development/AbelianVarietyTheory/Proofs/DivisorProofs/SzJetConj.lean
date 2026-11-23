import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastAtEmbeddingRingOps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassEisensteinNonholomorphicIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinJetConjDirectionDiagonalExpansionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormHilbertEisensteinValueLeOfIntegralJStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT)
open ModularForm (E₄ E₆)

namespace GlobalTheory.HilbFam

theorem sz_jet_conj : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ [IsGalois ℚ F] (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (κ : Emb F → ℕ) (y : Fin 2 → ZMod N) (M M' b : ℕ) (e ρ₀ ρ : ℝ), 0 ≤ e → (∀ C, -(padicValRat l (z C / 2 ^ Module.finrank ℚ F) : ℝ) ≤ e) → ¬ l ∣ M → (∀ x ∈ stdLat F, ((M * l ^ b : ℕ) : 𝓞 F) • x ∈ L) → (∀ v ∈ L, ∀ (j : Fin 2) (i : Emb F), Sz l lam ρ₀ ((i (v j) : ℝ) : ℂ)) → Sz l lam ρ₀ (N : ℂ) → b + (padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀ ≤ ρ → 0 ≤ ρ → ¬ l ∣ M' → M' • y = 0 → y ≠ 0 →  ∀ (τ : ℍ) (ω : ℂ), Sz l lam 0 (jT τ) → ω ^ 12 = DD τ → ω ≠ 0 → Sz l lam ρ ((G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N y τ) / ω ^ 2) → Sz l lam (e + s * (padicValInt l (discr F) : ℝ) + 2 * s * b * Module.finrank ℚ F + (∑ i, κ i : ℕ) * ρ) (jet (2 * s) L κ τ 1 (starRingEnd ℂ (τ : ℂ) - τ) * ((Real.pi / τ.im : ℝ) : ℂ) ^ (∑ i, κ i) / (2 * Real.pi * Complex.I) ^ wt (2 * s) κ / ω ^ wt (2 * s) κ) := by
  intro hE F _ _ _ hF s N _ L hs hL _ z hz l _ lam κ y M M' b e ρ₀ ρ he hze hM hML hLv hN hρ hρ0 hM' hy hy0 τ ω hj hω hω0 hst
  obtain ⟨h0, hadd, hmul, hmono, hint, hsum⟩ := GlobalTheory.QFam.SzSum.sz_ring l lam
  have hpow : ∀ (x : ℂ) (n : ℕ), Sz l lam ρ x → Sz l lam (n * ρ) (x ^ n) := by
    intro x n hx
    induction n with
    | zero => simpa using hint 1
    | succ n ih =>
      have := hmul _ _ _ _ ih hx
      rw [pow_succ]
      convert this using 1
      push_cast
      ring
  have hneg : Sz l lam ρ (-((G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N y τ) / ω ^ 2)) := by
    simpa only [zero_sub] using (hadd ρ _ _ (h0 ρ) hst).2
  rw [GlobalTheory.T.eisenstein_jet_conj_direction_diagonal_expansion hE F hF s N L hs (Nat.pos_of_ne_zero (NeZero.ne N)) hL τ κ (wB N y), Finset.sum_div]
  refine hsum _ _ _ _ fun μ hμ ↦ ?_
  have hle : ∀ i, μ i ≤ κ i := Finset.mem_Iic.mp hμ
  have hs' : ∑ i, κ i = ∑ i, (κ i - μ i) + ∑ i, μ i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ (Nat.sub_add_cancel (hle i)).symm
  have hh := GlobalTheory.T.norm_hilbertEisensteinValue_le_of_integral_j hE F hF s N L hs hL z hz l lam μ y M M' b e ρ₀ ρ he hze hM hML hLv hN hρ hρ0 hM' hy hy0 τ ω hj hω
  have key := hmul _ _ _ _ (hmul _ _ _ _ (hint (∏ i, rco (2 * s) (κ i) (μ i))) (hpow _ (∑ i, (κ i - μ i)) hneg)) hh
  rw [GlobalTheory.wB_nonhol_correction N y τ]
  have hw : wt (2 * s) κ = 2 * (∑ i, (κ i - μ i)) + wt (2 * s) μ := by
    unfold wt
    rw [hs']
    ring
  convert key using 1
  · rw [hs']
    push_cast
    ring
  · rw [hw, pow_add, pow_mul, ← neg_div, div_pow]
    field_simp

end GlobalTheory.HilbFam
