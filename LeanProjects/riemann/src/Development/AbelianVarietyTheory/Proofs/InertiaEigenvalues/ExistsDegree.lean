import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open scoped Topology

namespace GlobalTheory.UnramifiedDegree

theorem exists_degree : ∀ (l : ℕ) [Fact l.Prime],
    (∀ n : ℕ, 0 < n → ∀ σ : GQ l, ∃ a : ℕ, ∀ x : Om l, x ^ l ^ n = x → σ x = x ^ l ^ a) →
    (∀ n a b : ℕ, 0 < n → (∀ x : Om l, x ^ l ^ n = x → x ^ l ^ a = x ^ l ^ b) → a ≡ b [MOD n]) →
    ∃ z : GQ l → ℤ_[l], Continuous z ∧ (∀ σ τ, z (σ * τ) = z σ + z τ) ∧
      ∀ (σ : GQ l) (a : ℕ), (∀ n : ℕ, 0 < n → ∀ x : Om l, x ^ l ^ n = x → σ x = x ^ l ^ a) →
        z σ = (a : ℤ_[l]) := by
  intro l hl h1 h2
  have hpos : ∀ k : ℕ, 0 < l ^ k := fun k => pow_pos hl.out.pos k
  choose a ha using fun (σ : GQ l) (k : ℕ) => h1 (l ^ k) (hpos k) σ
  have hdv : ∀ (σ : GQ l) (k : ℕ), (l : ℤ) ^ k ∣ (a σ (k + 1) : ℤ) - (a σ k : ℤ) := by
    intro σ k
    have h := h2 (l ^ k) (a σ k) (a σ (k + 1)) (hpos k) fun x hx => by
      rw [← ha σ k x hx, ← ha σ (k + 1) x (by
        rw [pow_succ l k]; exact GlobalTheory.UnramifiedCrys.pow_pow_mul hx l)]
    exact_mod_cast h.dvd
  obtain ⟨z, hz⟩ : ∃ z : GQ l → ℤ_[l], ∀ σ k, PadicInt.toZModPow k (z σ) = (a σ k : ZMod (l ^ k)) := by
    refine ⟨fun σ => PadicInt.ofIntSeq _
      (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun k => (a σ k : ℤ)) l (hdv σ)), fun σ k => ?_⟩
    rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub (fun k => (a σ k : ℤ)) l (hdv σ) k,
      Int.cast_natCast]
  have key : ∀ (σ : GQ l) (k b : ℕ), (∀ x : Om l, x ^ l ^ l ^ k = x → σ x = x ^ l ^ b) →
      PadicInt.toZModPow k (z σ) = (b : ZMod (l ^ k)) := by
    intro σ k b hb
    rw [hz, ZMod.natCast_eq_natCast_iff]
    exact h2 _ _ _ (hpos k) fun x hx => by rw [← ha σ k x hx, hb x hx]
  refine ⟨z, ?_, fun σ τ => ?_, fun σ b hb => ?_⟩
  · rw [continuous_iff_continuousAt]
    intro σ₀
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt l hε
    have hev : ∀ᶠ σ in 𝓝 σ₀, ∀ x ∈ {y : Om l | y ^ l ^ l ^ k = y}, σ x = σ₀ x := by
      refine (GlobalTheory.UnramifiedCrys.finite_fixedPow (p := l) (R := Om l) (hpos k)).eventually_all.2
        fun x _ => ?_
      have ho := (stabilizer_isOpen_of_isIntegral (K := ℚ_[l]) x).preimage
        (continuous_mul_left σ₀⁻¹)
      filter_upwards [ho.mem_nhds (show σ₀ ∈ _ by simp)] with σ hσ
      have h : σ₀⁻¹ (σ x) = x := hσ
      have h' := congrArg σ₀ h
      rwa [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply] at h'
    filter_upwards [hev] with σ hσ
    refine lt_of_le_of_lt ?_ hk
    rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow,
      RingHom.mem_ker, map_sub, sub_eq_zero, hz σ₀]
    exact key σ k _ fun x hx => by rw [hσ x hx, ha σ₀ k x hx]
  · refine PadicInt.ext_of_toZModPow.mp fun k => ?_
    rw [map_add, hz σ, hz τ, ← Nat.cast_add]
    refine key _ k _ fun x hx => ?_
    rw [AlgEquiv.mul_apply, ha τ k x hx, map_pow, ha σ k x hx, ← pow_mul, ← pow_add]
  · refine PadicInt.ext_of_toZModPow.mp fun k => ?_
    rw [map_natCast]
    exact key σ k b (hb _ (hpos k))

end GlobalTheory.UnramifiedDegree
