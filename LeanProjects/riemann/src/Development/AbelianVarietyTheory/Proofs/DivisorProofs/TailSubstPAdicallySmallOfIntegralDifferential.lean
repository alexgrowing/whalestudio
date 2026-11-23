import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddMulLeOfPowLeOfLargeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesEvalTruncSubstEqSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffFinsuppProdConstFreeEqZeroOfDegreeLtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowDvdEvalTruncOfHighOrderStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem GlobalTheory.tail_subst_small : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (u : τ → MvPowerSeries σ B) (f : MvPowerSeries τ Q), (∀ j, constantCoeff (u j) = 0) → DIn (⊤ : Ideal B) f → ∀ m : ℕ, ∃ M0 : ℕ, ∀ M ≥ M0, ∀ n : σ →₀ ℕ, ∃ b : B, MvPolynomial.eval (fun i => algebraMap B Q (z i)) (trunc' Q n (subst (up Q u) (f - (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => M) f : MvPowerSeries τ Q)))) = algebraMap B Q (p ^ m * b) := by
  intro p hp B O Q _ _ _ _ θ hF σ _ _ z hz τ _ _ u f hu hD m
  have hpr : p.Prime := hp.out
  obtain ⟨L, hL⟩ := GlobalTheory.T.pow_dvd_eval_trunc_of_high_order p B σ z hz
  obtain ⟨M0, hM0⟩ := GlobalTheory.T.add_mul_le_of_pow_le_of_large p L m hpr.two_le
  refine ⟨M0, fun M hM n => ?_⟩
  set g : MvPowerSeries τ Q := f - (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => M) f : MvPowerSeries τ Q) with hg
  have hfin := Finsupp.finite_of_degree_le (σ := τ) n.degree
  rw [GlobalTheory.T.mvPowerSeries_eval_trunc_subst_eq_sum B Q σ τ z u hu g n hfin.toFinset (fun α hα => by simpa using hα)]

  have key : ∀ α : τ →₀ ℕ, ∃ b : B, coeff α g * algebraMap B Q (MvPolynomial.eval z
      (trunc' B n (α.prod fun j e => u j ^ e))) = algebraMap B Q (p ^ m * b) := by
    intro α
    by_cases hα : α ≤ Finsupp.equivFunOnFinite.symm fun _ => M
    · refine ⟨0, ?_⟩
      have : coeff α g = 0 := by
        simp [hg, coeff_trunc', hα]
      simp [this]
    · have hcg : coeff α g = coeff α f := by
        simp [hg, coeff_trunc', hα]
      rw [hcg]
      obtain ⟨i, hi⟩ : ∃ i, M < α i := by
        by_contra h
        push_neg at h
        exact hα (fun i => by simpa using h i)
      obtain ⟨b, -, hb⟩ := hD α i
      obtain ⟨v, n', hn', hdec⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := α i) (by omega) p hpr.one_lt.ne'
      have hcop : Nat.Coprime n' p := ((Nat.Prime.coprime_iff_not_dvd hpr).2 hn').symm
      obtain ⟨w, hw⟩ := (hF.unit_coprime n' hcop).exists_right_inv
      have hn'pos : 0 < n' := Nat.pos_of_ne_zero (by rintro rfl; simp at hdec; omega)
      have hpv : p ^ v ≤ α.degree := by
        have : p ^ v ≤ α i := by rw [hdec]; exact Nat.le_mul_of_pos_right _ hn'pos
        exact this.trans (Finsupp.le_degree i α)
      have hdeg : (v + m) * L ≤ α.degree :=
        hM0 α.degree v (by have := Finsupp.le_degree i α; omega) hpv
      obtain ⟨c, hc⟩ := hL (v + m) (α.prod fun j e => u j ^ e) (fun β hβ =>
        GlobalTheory.T.coeff_finsuppProd_constFree_eq_zero_of_degree_lt B σ τ u hu α β (by rw [mul_comm] at hβ; omega)) n
      refine ⟨b * w * c, ?_⟩
      rw [hc]
      rw [hdec] at hb
      have hw' := congrArg (algebraMap B Q) hw
      simp only [map_mul, map_pow, map_natCast, map_one, Nat.cast_mul, Nat.cast_pow] at hb hw' ⊢
      linear_combination ((p : Q) ^ m * algebraMap B Q w * algebraMap B Q c) * hb
        - (coeff α f * (p : Q) ^ (v + m) * algebraMap B Q c) * hw'
  choose bb hbb using key
  refine ⟨∑ α ∈ hfin.toFinset, bb α, ?_⟩
  rw [Finset.mul_sum, map_sum]
  exact Finset.sum_congr rfl fun α _ => hbb α
