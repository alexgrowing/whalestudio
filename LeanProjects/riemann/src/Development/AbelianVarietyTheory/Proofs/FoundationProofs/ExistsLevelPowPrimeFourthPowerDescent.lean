import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiagMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassInvariantDescentCoprimeLevelModPowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelMulPowOfInvariantModPowStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES.DescInv

theorem gamma_anti {a b : ℕ} (h : a ∣ b) :
    CongruenceSubgroup.Gamma b ≤ CongruenceSubgroup.Gamma a := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  have key : ∀ (x : ℤ) (c : ZMod b), (x : ZMod b) = c → (x : ZMod a) = ZMod.castHom h (ZMod a) c := by
    intro x c hx; rw [← hx, map_intCast]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key _ _ h1, map_one]
  · simpa using key _ _ h2
  · simpa using key _ _ h3
  · rw [key _ _ h4, map_one]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem lev_of_dvd {X : Tower Ω ε} {a b : ℕ} (h : a ∣ b) {f : X.K} (hf : Lev X a f) : Lev X b f :=
  fun γ hγ => hf γ (gamma_anti h hγ)

theorem exists_dvd_pow_mul_coprime (M : ℕ) (hM : 0 < M) :
    ∀ N : ℕ, 0 < N → ∃ e b : ℕ, 0 < b ∧ Nat.Coprime M b ∧ N ∣ M ^ e * b := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro hN
  by_cases hc : Nat.Coprime M N
  · exact ⟨0, N, hN, hc, by simp⟩
  · have hd0 : Nat.gcd M N ≠ 0 := (Nat.gcd_pos_of_pos_left N hM).ne'
    have hd1 : 1 < Nat.gcd M N := by
      have : Nat.gcd M N ≠ 1 := hc
      omega
    obtain ⟨N', hN'⟩ := Nat.gcd_dvd_right M N
    have hN'pos : 0 < N' := by
      rcases Nat.eq_zero_or_pos N' with h0 | h0
      · rw [h0, mul_zero] at hN'; omega
      · exact h0
    have hlt : N' < N := by
      rw [hN']; nlinarith
    obtain ⟨e, b, hb, hcop, hdiv⟩ := ih N' hlt hN'pos
    refine ⟨e + 1, b, hb, hcop, ?_⟩
    have : M ^ (e + 1) * b = M * (M ^ e * b) := by ring
    rw [this, hN']
    exact Nat.mul_dvd_mul (Nat.gcd_dvd_left M N) hdiv

end GlobalTheory.KZ.ES.DescInv

open GlobalTheory.KZ.ES.DescInv in

theorem GlobalTheory.KZ.ES.desc_pow_four : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (l n M : ℕ), l.Prime → 0 < M → 6 * l ∣ M → ∀ f : X.Kˣ,
    (∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ g : X.Kˣ, X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n)) →
    ∃ (k : ℕ) (h : X.Kˣ), Lev X (M * l ^ k) ((f : X.K) ^ 4 * (h : X.K) ^ (l ^ n)) := by
  intro Ω _ _ _ ε X l n M hl hM h6 f hf
  classical
  obtain ⟨M'', hM''pos, hM''⟩ := X.level (f : X.K)
  haveI : NeZero M'' := ⟨hM''pos.ne'⟩

  have hex : ∀ r : SL(2, ZMod M''), ∃ (g : X.Kˣ) (L : ℕ), 0 < L ∧ Lev X L (g : X.K) ∧
      ∀ γ ∈ CongruenceSubgroup.Gamma M,
        Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M'')) γ = r →
        X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n) := by
    intro r
    by_cases hr : ∃ γ₀ ∈ CongruenceSubgroup.Gamma M,
        Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M'')) γ₀ = r
    · obtain ⟨γ₀, hγ₀, hr0⟩ := hr
      obtain ⟨g, hg⟩ := hf γ₀ hγ₀
      obtain ⟨L, hL, hLg⟩ := X.level (g : X.K)
      refine ⟨g, L, hL, hLg, fun γ _ hrγ => ?_⟩
      have hδ : γ * γ₀⁻¹ ∈ CongruenceSubgroup.Gamma M'' := by
        rw [CongruenceSubgroup.Gamma_mem', map_mul, map_inv, hrγ, hr0, mul_inv_cancel]
      have hγ : γ = (γ * γ₀⁻¹) * γ₀ := by group
      rw [hγ, map_mul, X.sl_mul, hM'' _ hδ, hg]
    · exact ⟨1, 1, one_pos, fun γ _ => by simp, fun γ hγ hrγ => absurd ⟨γ, hγ, hrγ⟩ hr⟩
  choose G L hLpos hLev hG using hex
  set L₀ : ℕ := ∏ r, L r with hL₀
  have hL₀pos : 0 < L₀ := Finset.prod_pos fun r _ => hLpos r
  have hLdvd : ∀ r, L r ∣ L₀ := fun r => Finset.dvd_prod_of_mem L (Finset.mem_univ r)
  obtain ⟨e, b, hb, hcop, hdiv⟩ := exists_dvd_pow_mul_coprime M hM (M'' * L₀) (Nat.mul_pos hM''pos hL₀pos)
  have hdiv' : M'' * L₀ ∣ M ^ (e + 1) * b :=
    hdiv.trans (Nat.mul_dvd_mul_right (pow_dvd_pow M (Nat.le_succ e)) b)
  have hMa : 0 < M ^ (e + 1) := pow_pos hM _
  have hMMa : M ∣ M ^ (e + 1) := dvd_pow_self M (Nat.succ_ne_zero e)
  have h6a : 6 * l ∣ M ^ (e + 1) := h6.trans hMMa
  have hcopa : Nat.Coprime (M ^ (e + 1)) b := Nat.Coprime.pow_left _ hcop
  have hfLev : Lev X (M ^ (e + 1) * b) (f : X.K) :=
    lev_of_dvd ((dvd_mul_right M'' L₀).trans hdiv') hM''
  have hstep : ∀ γ ∈ CongruenceSubgroup.Gamma (M ^ (e + 1)), ∃ g : X.Kˣ, Lev X (M ^ (e + 1) * b) (g : X.K) ∧
      X.sl (ofSL γ) (f : X.K) = f * (g : X.K) ^ (l ^ n) := by
    intro γ hγ
    have hγM : γ ∈ CongruenceSubgroup.Gamma M := gamma_anti hMMa hγ
    let r := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M'')) γ
    exact ⟨G r, lev_of_dvd (((hLdvd r).trans (dvd_mul_left L₀ M'')).trans hdiv') (hLev r), hG r γ hγM rfl⟩
  obtain ⟨h, hh⟩ := GlobalTheory.T.classInvariant_descent_coprimeLevel_modPow ε X l n (M ^ (e + 1)) b hl hMa hb h6a hcopa f hfLev hstep
  have hFstep : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∃ g : X.Kˣ,
      X.sl (ofSL γ) (((f ^ 4 * h ^ (l ^ n) : X.Kˣ)) : X.K) = (f ^ 4 * h ^ (l ^ n) : X.Kˣ) * (g : X.K) ^ (l ^ n) := by
    intro γ hγ
    obtain ⟨g, hg⟩ := hf γ hγ
    have hne : X.sl (ofSL γ) (h : X.K) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (X.sl (ofSL γ)).injective]; exact h.ne_zero
    refine ⟨g ^ 4 * Units.mk0 _ hne * h⁻¹, ?_⟩
    have hh0 : (h : X.K) ≠ 0 := h.ne_zero
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_inv_eq_inv_val, map_mul, map_pow, hg,
      mul_pow, inv_pow]
    have hp : (h : X.K) ^ (l ^ n) ≠ 0 := pow_ne_zero _ hh0
    field_simp
    ring
  obtain ⟨k, h', hh'⟩ := GlobalTheory.T.exists_level_mul_pow_of_invariant_mod_pow ε X l n M (e + 1) hl hM (f ^ 4 * h ^ (l ^ n)) (by simpa using hh) hFstep
  refine ⟨k, h * h', ?_⟩
  convert hh' using 1
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  ring
