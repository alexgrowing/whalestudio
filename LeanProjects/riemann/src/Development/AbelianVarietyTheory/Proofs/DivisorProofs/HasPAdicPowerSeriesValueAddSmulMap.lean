import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog.ValLin

lemma eval_map_hom {σ Q Q' : Type} [CommRing Q] [CommRing Q'] (R : Q →+* Q') (x : σ → Q)
    (P : MvPolynomial σ Q) :
    R (MvPolynomial.eval x P) = MvPolynomial.eval (fun i => R (x i)) (MvPolynomial.map R P) := by
  rw [MvPolynomial.eval_map]
  show R (MvPolynomial.eval₂ (RingHom.id Q) x P) = _
  rw [MvPolynomial.hom_eval₂, RingHom.comp_id]

theorem hasVal_add_smul_map : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (z : σ → B) (f g : MvPowerSeries σ Q) (q r : Q), HasVal p z f q → (HasVal p z g r → HasVal p z (f + g) (q + r)) ∧ (∀ c : Q, HasVal p z (c • f) (c * q)) ∧ ∀ (B' Q' : Type) [CommRing B'] [CommRing Q'] [Algebra B' Q'] (ρ : B →+* B') (R : Q →+* Q'), (∀ b, R (algebraMap B Q b) = algebraMap B' Q' (ρ b)) → HasVal p (fun i => ρ (z i)) (map R f) (R q) := by
  intro p _ B O Q _ _ _ _ θ hF σ _ _ z f g q r hf
  refine ⟨?_, ?_, ?_⟩
  · intro hg m
    obtain ⟨N₁, h₁⟩ := hf m
    obtain ⟨N₂, h₂⟩ := hg m
    refine ⟨max N₁ N₂, fun N' hN => ?_⟩
    obtain ⟨b₁, hb₁⟩ := h₁ N' (le_trans (le_max_left _ _) hN)
    obtain ⟨b₂, hb₂⟩ := h₂ N' (le_trans (le_max_right _ _) hN)
    refine ⟨b₁ + b₂, ?_⟩
    rw [map_add, map_add, mul_add, map_add, ← hb₁, ← hb₂]
    ring
  · intro c m
    obtain ⟨k, b₀, hk⟩ := hF.denom c
    obtain ⟨N, h⟩ := hf (m + k)
    refine ⟨N, fun N' hN => ?_⟩
    obtain ⟨b, hb⟩ := h N' hN
    refine ⟨b₀ * b, ?_⟩
    rw [map_smul, MvPolynomial.smul_eval]
    have e : c * q - c * MvPolynomial.eval (fun i => algebraMap B Q (z i))
        (trunc' Q (Finsupp.equivFunOnFinite.symm fun _ => N') f)
        = c * algebraMap B Q (p ^ (m + k) * b) := by rw [← hb]; ring
    rw [e]
    simp only [map_mul, map_pow, map_natCast] at hk ⊢
    rw [← hk]
    ring
  · intro B' Q' _ _ _ ρ R hR m
    obtain ⟨N, h⟩ := hf m
    refine ⟨N, fun N' hN => ?_⟩
    obtain ⟨b, hb⟩ := h N' hN
    refine ⟨ρ b, ?_⟩
    rw [trunc'_map]
    have := congrArg R hb
    rw [map_sub, eval_map_hom, hR] at this
    simp only [hR] at this
    rw [this]
    simp

end GlobalTheory.QLog.ValLin
