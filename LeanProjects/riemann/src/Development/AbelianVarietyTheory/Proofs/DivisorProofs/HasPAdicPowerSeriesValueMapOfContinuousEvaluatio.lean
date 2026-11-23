import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory

theorem eval_coe_polynomial_of_isEval {p : ℕ} {B : Type} [CommRing B] {σ : Type}
    (z : σ → B) (E : MvPowerSeries σ B →ₐ[B] B) (hE : IsEval p z E) (P : MvPolynomial σ B) :
    E (P : MvPowerSeries σ B) = MvPolynomial.eval z P := by
  have h : E.comp (MvPolynomial.coeToMvPowerSeries.algHom B) = MvPolynomial.aeval z := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [MvPolynomial.coeToMvPowerSeries.algHom_apply, hE.1 i]
  have := congrArg (fun φ => φ P) h
  simpa [MvPolynomial.coeToMvPowerSeries.algHom_apply] using this

theorem hasVal_map_of_isEval : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) → ∀ E : MvPowerSeries σ B →ₐ[B] B, IsEval p z E → ∀ s : MvPowerSeries σ B, HasVal p z (map (algebraMap B Q) s) (algebraMap B Q (E s)) := by
  intro p _ B O Q _ _ _ _ θ _ σ _ _ z _ E hE s m
  obtain ⟨N, hN⟩ := hE.2 m
  refine ⟨N, fun N' hN' => ?_⟩
  set n : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => N'
  have hdiv : (p : B) ^ m ∣ E (s - (trunc' B n s : MvPowerSeries σ B)) := by
    apply hN
    intro α hα
    have hle : α ≤ n := by
      intro i
      have h1 : α i ≤ α.degree := by
        classical
        rw [Finsupp.degree]
        by_cases hi : i ∈ α.support
        · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi
        · simp [Finsupp.notMem_support_iff.1 hi]
      show α i ≤ N'
      omega
    rw [map_sub, MvPolynomial.coeff_coe, coeff_trunc', if_pos hle, sub_self]
  obtain ⟨b, hb⟩ := hdiv
  refine ⟨b, ?_⟩
  rw [map_sub, eval_coe_polynomial_of_isEval z E hE] at hb
  have key : algebraMap B Q (MvPolynomial.eval z (trunc' B n s)) =
      MvPolynomial.eval₂ (algebraMap B Q) (fun i => algebraMap B Q (z i)) (trunc' B n s) := by
    rw [MvPolynomial.eval, MvPolynomial.coe_eval₂Hom]
    exact MvPolynomial.eval₂_comp_left _ _ _ _
  rw [trunc'_map, MvPolynomial.eval_map, ← key, ← map_sub, hb]

end GlobalTheory
