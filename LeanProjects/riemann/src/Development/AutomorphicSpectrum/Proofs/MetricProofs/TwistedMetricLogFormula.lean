import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem log_refNorm_blocks {κ : Type} [Fintype κ] {ρ : κ → Type} [∀ k, Fintype (ρ k)] (d : κ → ℤ)
    {z : (Σ k, ρ k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (refNorm d z) = ∑ k, (d k : ℝ) / 2 * Real.log (∑ i, ‖z ⟨k, i⟩‖ ^ 2) := by
  have hpos : ∀ k, 0 < ∑ i, ‖z ⟨k, i⟩‖ ^ 2 := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.mpr hi) 2)
      (Finset.single_le_sum (fun i _ => sq_nonneg ‖z ⟨k, i⟩‖) (Finset.mem_univ i))
  unfold refNorm
  rw [Real.log_prod fun k _ => (Real.rpow_pos_of_pos (hpos k) _).ne']
  exact Finset.sum_congr rfl fun k _ => Real.log_rpow (hpos k) _

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem xiDeg_self (M : FlagModel y Ψ N j) {τ : Ψ} {a : Fin N} {k₀ : K} (hk : M.blk (τ, a) = some k₀) :
    xiDeg M τ a k₀ = -2 := by
  have hd : ∀ p, M.dy p k₀ = if p = (τ, a) then 1 else 0 := fun p => by
    have hn : ¬ ∀ p', M.blk p' ≠ some k₀ := fun h => h _ hk
    unfold FlagModel.dy
    rw [dif_neg hn]
    by_cases hp : p = (τ, a)
    · rw [if_pos (hp ▸ hk), if_pos hp]
    · rw [if_neg fun e => hp (M.blk_inj _ _ k₀ e hk), if_neg hp]
  unfold xiDeg
  simp only [hd, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [xiCoef]

theorem log_potA : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K), M.blk (τ, a) = some k₀ → ∀ zz : (Σ o : Option K, ι (o.getD k₀)) → ℂ, (∀ o, ∃ i, zz ⟨o, i⟩ ≠ 0) → Real.log ((potA M τ a k₀).h zz) = -(1 / 2) * ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h (fstPt k₀ zz)) + Real.log ((fsHerm ι (M.dy p)).h (sndPt k₀ zz))) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a k₀ hk zz hz
  have hf : ∀ k, ∃ i, fstPt k₀ zz ⟨k, i⟩ ≠ 0 := fun k => hz (some k)
  have hs : ∀ k, ∃ i, sndPt k₀ zz ⟨k, i⟩ ≠ 0 := fun k => by
    by_cases e : k = k₀
    · subst e
      obtain ⟨i, hi⟩ := hz none
      refine ⟨i, ?_⟩
      simpa [sndPt, v₁_self] using hi
    · obtain ⟨i, hi⟩ := hz (some k)
      refine ⟨i, ?_⟩
      simpa [sndPt, v₁_ne (p := ⟨k, i⟩) e] using hi
  set A : K → ℝ := fun k => Real.log (∑ i, ‖fstPt k₀ zz ⟨k, i⟩‖ ^ 2) with hA
  set B : K → ℝ := fun k => Real.log (∑ i, ‖sndPt k₀ zz ⟨k, i⟩‖ ^ 2) with hB
  set Ln : ℝ := Real.log (∑ i : ι k₀, ‖zz ⟨none, i⟩‖ ^ 2) with hLn
  have hB₀ : B k₀ = Ln := by
    simp only [hB, hLn, sndPt, Function.comp_apply, v₁_self]
  have hBne : ∀ k, k ≠ k₀ → B k = A k := fun k e => by
    simp only [hA, hB, fstPt, sndPt, Function.comp_apply, v₀]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [v₁_ne (p := ⟨k, i⟩) e]
  have hlhs : Real.log ((potA M τ a k₀).h zz) = 1 / 2 * Ln + ∑ k, (aDeg M τ a k₀ (some k) : ℝ) / 2 * A k := by
    show Real.log (refNorm (aDeg M τ a k₀) zz) = _
    rw [log_refNorm_blocks _ hz, Fintype.sum_option]
    simp only [aDeg, hLn, hA]
    norm_num
    rfl
  have hrhs : ∑ p, (xiCoef τ a p : ℝ) * (Real.log ((fsHerm ι (M.dy p)).h (fstPt k₀ zz)) +
      Real.log ((fsHerm ι (M.dy p)).h (sndPt k₀ zz))) = ∑ k, (xiDeg M τ a k : ℝ) / 2 * (A k + B k) := by
    have hp : ∀ p, Real.log ((fsHerm ι (M.dy p)).h (fstPt k₀ zz)) + Real.log ((fsHerm ι (M.dy p)).h (sndPt k₀ zz)) =
        ∑ k, (M.dy p k : ℝ) / 2 * (A k + B k) := fun p => by
      rw [fsHerm_h, fsHerm_h, log_refNorm_blocks _ hf, log_refNorm_blocks _ hs, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by simp only [hA, hB]; ring
    simp only [hp, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [xiDeg]
    push_cast
    rw [Finset.sum_div, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hlhs, hrhs]
  have hterm : ∀ k, (aDeg M τ a k₀ (some k) : ℝ) / 2 * A k + 1 / 2 * ((xiDeg M τ a k : ℝ) / 2 * (A k + B k)) =
      if k = k₀ then -(1 / 2) * Ln else 0 := fun k => by
    by_cases e : k = k₀
    · subst e
      rw [if_pos rfl, hB₀, xiDeg_self M hk]
      simp only [aDeg, if_true]
      push_cast
      ring
    · rw [if_neg e, hBne k e]
      simp only [aDeg, if_neg e]
      push_cast
      ring
  have hsum := Finset.sum_congr (rfl : (Finset.univ : Finset K) = _) fun k _ => hterm k
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ k₀, if_pos (Finset.mem_univ _)] at hsum
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
