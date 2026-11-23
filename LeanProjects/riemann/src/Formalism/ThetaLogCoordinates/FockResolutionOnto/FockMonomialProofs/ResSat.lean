import Formalism.ThetaLogCoordinates.FockResolutionOnto.StatementC
import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.InitPartZeroXMul

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset

theorem restriction_saturation_holds : ResSatOf := by
  intro p _ K r _ LL q J M ρ hK hD x hx hxi
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have key : ∀ n : ℕ, ∀ h ∈ Y p LL J M, h ∈ IntPol p (Fin (K + 1) × Fin r) →
      initPart (Fin.last K, ρ) 0 h = ((p : ℚ_[p]) ^ n) • x →
      ∃ h' ∈ Y p LL J M, h' ∈ IntPol p (Fin (K + 1) × Fin r) ∧ initPart (Fin.last K, ρ) 0 h' = x := by
    intro n
    induction n with
    | zero =>
      intro h hY hi hr
      exact ⟨h, hY, hi, by simpa using hr⟩
    | succ n ih =>
      intro h hY hi hr
      obtain ⟨a, ha, hai⟩ := exists_div (Fin.last K, ρ) h
      have hb : ((p : ℚ_[p]) ^ n) • x ∈ IntPol p (Fin (K + 1) × Fin r) := smul_int _ (norm_p_pow_le n) x hxi
      have hdec : h = X (Fin.last K, ρ) * a + (p : ℚ_[p]) • (((p : ℚ_[p]) ^ n) • x) := by
        rw [smul_smul, ← pow_succ', ← hr]
        exact ha.trans (add_comm _ _)
      obtain ⟨h₁, _, b', hb'i, hXY, hh⟩ := hD h hY hi a (hai hi) _ hb hdec
      have hpb : (p : ℚ_[p]) • b' ∈ Y p LL J M := by
        have : (p : ℚ_[p]) • b' = h - X (Fin.last K, ρ) * h₁ := by
          rw [eq_sub_iff_add_eq]; exact (hh.trans (add_comm _ _)).symm
        rw [this]
        exact Submodule.sub_mem _ hY hXY
      have hbY : b' ∈ Y p LL J M := by
        have := Submodule.smul_mem _ ((p : ℚ_[p])⁻¹) hpb
        rwa [smul_smul, inv_mul_cancel₀ hp0, one_smul] at this
      refine ih b' hbY hb'i ?_
      have h2 : initPart (Fin.last K, ρ) 0 h = (p : ℚ_[p]) • initPart (Fin.last K, ρ) 0 b' := by
        conv_lhs => rw [hh]
        rw [initPart_add, initPart_zero_X_mul, zero_add, initPart_smul]
      rw [hr, pow_succ', ← smul_smul] at h2
      exact (smul_right_injective _ hp0 h2).symm
  obtain ⟨h0, hh0, hr0⟩ := hK x hx
  obtain ⟨n, hn⟩ := exists_pow_smul_intPol h0
  exact key n _ (Submodule.smul_mem _ _ hh0) hn (by rw [initPart_smul, hr0])

end Formalism.InvariantFactorPaths.L4
