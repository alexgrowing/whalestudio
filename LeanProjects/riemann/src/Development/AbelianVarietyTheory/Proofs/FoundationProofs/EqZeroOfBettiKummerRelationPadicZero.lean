import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HsCodiscreteNeBot
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerRootMem
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB

namespace GlobalTheory.KZ.BettiB

theorem gamma_le_gamma_of_dvd {K M : ℕ} (h : K ∣ M) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma M) :
    δ ∈ CongruenceSubgroup.Gamma K := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [map_intCast, map_one] using congrArg (ZMod.castHom h (ZMod K)) h1
  · simpa using congrArg (ZMod.castHom h (ZMod K)) h2
  · simpa using congrArg (ZMod.castHom h (ZMod K)) h3
  · simpa only [map_intCast, map_one] using congrArg (ZMod.castHom h (ZMod K)) h4

theorem mem_gam_of_mem_gamma {N l : ℕ} {δ : SL(2, ℤ)} (hN : δ ∈ CongruenceSubgroup.Gamma N)
    (hl : δ ∈ CongruenceSubgroup.Gamma l) : δ ∈ Gam N l := by
  rw [CongruenceSubgroup.Gamma_mem] at hN hl
  refine ⟨?_, ?_⟩
  · exact (CongruenceSubgroup.Gamma1_mem N δ).2 ⟨hN.1, hN.2.2.2, hN.2.2.1⟩
  · exact CongruenceSubgroup.Gamma0_mem.2 hl.2.2.1

theorem cls_pow_eq_zero {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (n : ℕ) (g : X.Kˣ) : X.cls l n (g ^ (l ^ n)) = 0 := by
  unfold Tower.cls
  rw [Submodule.Quotient.mk_eq_zero]
  have h : ((1 : ℤ_[l]) ⊗ₜ[ℤ] Additive.ofMul (g ^ (l ^ n)) : X.Kl l) =
      ((l : ℤ_[l]) ^ n) • ((1 : ℤ_[l]) ⊗ₜ[ℤ] Additive.ofMul g : X.Kl l) := by
    rw [ofMul_pow, TensorProduct.tmul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  rw [h]
  exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n) Submodule.mem_top

theorem eq_zero_of_btZ_zero : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l : ℕ) [Fact l.Prime], 0 < N → ∀ b : X.Fn l, BtZ X N l b 0 → b = 0 := by
  intro Ω _ _ _ ε X hε hj N l hl hN b hb
  funext u
  apply AdicCompletion.ext
  intro n
  obtain ⟨χ, ⟨f, a, c, M₁, hM₁, hev, ⟨ha, hc, hc0, hroot⟩, hinv⟩, M₂, hM₂, hχ⟩ := hb n u
  have hlpos : 0 < l := hl.out.pos
  obtain ⟨g, hg⟩ := kummer_root_mem ε X hε hj (l ^ n) (pow_pos hlpos n) f a c (M₁ * M₂ * N * l)
    (by positivity) ha hc hc0 hroot (by
      intro γ hγ
      have h1 : γ ∈ CongruenceSubgroup.Gamma M₁ := gamma_le_gamma_of_dvd ⟨M₂ * N * l, by ring⟩ hγ
      have h2 : γ ∈ CongruenceSubgroup.Gamma M₂ := gamma_le_gamma_of_dvd ⟨M₁ * N * l, by ring⟩ hγ
      have h3 : γ ∈ CongruenceSubgroup.Gamma N := gamma_le_gamma_of_dvd ⟨M₁ * M₂ * l, by ring⟩ hγ
      have h4 : γ ∈ CongruenceSubgroup.Gamma l := gamma_le_gamma_of_dvd ⟨M₁ * M₂ * N, by ring⟩ hγ
      have h0 : χ γ = 0 := by
        have := hχ ⟨γ, mem_gam_of_mem_gamma h3 h4⟩ h2
        simpa using this.symm
      refine Filter.Germ.coe_eq.2 (Filter.eventually_of_mem (Filter.self_mem_codiscreteWithin Hs) fun z hz => ?_)
      have := hinv γ h1 z hz
      rw [h0] at this
      simpa using this)
  have : AdicCompletion.eval (idl l) (X.Kl l) n (b u) = 0 := by
    rw [hev, hg, cls_pow_eq_zero]
  exact this

end GlobalTheory.KZ.BettiB
