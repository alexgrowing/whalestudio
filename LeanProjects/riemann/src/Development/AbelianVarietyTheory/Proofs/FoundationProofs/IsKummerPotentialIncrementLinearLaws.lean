import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralConjugateSL2IntLawsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelAddZeroCongrStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelIntegralMatrixConjStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelPadicIntSmulStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusBasicLawsStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem gamma_mem_of_dvd {M N : ℕ} (hMN : M ∣ N) {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma N) :
    δ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  have key : ∀ k : ℤ, ((k : ZMod N) = 1 → (k : ZMod M) = 1) ∧ ((k : ZMod N) = 0 → (k : ZMod M) = 0) := by
    intro k
    constructor
    · intro h
      have := congrArg (ZMod.castHom hMN (ZMod M)) h
      rwa [map_intCast, map_one] at this
    · intro h
      have := congrArg (ZMod.castHom hMN (ZMod M)) h
      rwa [map_intCast, map_zero] at this
  exact ⟨(key _).1 h1, (key _).2 h2, (key _).2 h3, (key _).1 h4⟩

theorem isKummerPotentialIncrement_linear_laws : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], (∀ (x x' : X.Khat l) (h h' : ℂ → ℤ_[l]), R1 X l x h → R1 X l x' h' → R1 X l (x + x') (h + h')) ∧ R1 X l 0 0 ∧ (∀ (c : ℤ_[l]) (x : X.Khat l) (h : ℂ → ℤ_[l]), R1 X l x h → R1 X l (c • x) (c • h)) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (x : X.Khat l) (h : ℂ → ℤ_[l]), 0 < m.det → R1 X l x h → R1 X l (X.kmap l (X.sl (toGQ m)).toRingEquiv x) (fun z => h (mob (toGQ m) z))) := by
  intro Ω _ _ ε X l _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x x' h h' hx hx' n
    obtain ⟨χ, hK, M, hM, hI⟩ := hx n
    obtain ⟨χ', hK', M', hM', hI'⟩ := hx' n
    refine ⟨χ + χ', ((GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).1 x x' χ χ' hK hK'), M * M', Nat.mul_pos hM hM', ?_⟩
    intro δ hδ z hz
    have e1 := hI δ (gamma_mem_of_dvd (dvd_mul_right M M') hδ) z hz
    have e2 := hI' δ (gamma_mem_of_dvd (dvd_mul_left M' M) hδ) z hz
    have : (h + h') (mob (ofSL δ) z) - (h + h') z = (h (mob (ofSL δ) z) - h z) + (h' (mob (ofSL δ) z) - h' z) := by
      simp only [Pi.add_apply]; ring
    rw [this, map_add, e1, e2, Pi.add_apply]
  · intro n
    refine ⟨0, (GlobalTheory.T.isKummerCharacterAtLevel_add_zero_congr Ω ε X l n).2.1, 1, Nat.one_pos, ?_⟩
    intro δ _ z _
    simp
  · intro c x h hx n
    obtain ⟨χ, hK, M, hM, hI⟩ := hx n
    refine ⟨fun δ => PadicInt.toZModPow n c * χ δ, GlobalTheory.T.isKummerCharacterAtLevel_padicInt_smul Ω ε X l n c x χ hK, M, hM, ?_⟩
    intro δ hδ z hz
    have : (c • h) (mob (ofSL δ) z) - (c • h) z = c * (h (mob (ofSL δ) z) - h z) := by
      simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [this, map_mul, hI δ hδ z hz]
  · intro m x h hm hx n
    obtain ⟨χ, hK, M, hM, hI⟩ := hx n
    refine ⟨fun δ => χ (cj m δ), GlobalTheory.T.isKummerCharacterAtLevel_integral_matrix_conj Ω ε X l n m x χ hm hK, M * m.det.natAbs,
      Nat.mul_pos hM (Int.natAbs_pos.mpr hm.ne'), ?_⟩
    intro δ hδ z hz
    obtain ⟨hc1, hc2⟩ := GlobalTheory.T.integralConjugateSL2Int_laws.1 m M hm δ hδ
    have hmz : mob (toGQ m) z ∈ Hs := GlobalTheory.T.glTwoPosRatMobius_basic_laws.1 (toGQ m) z hz
    have hcomm := GlobalTheory.T.integralConjugateSL2Int_laws.2.2 m δ (cj m δ) hm hc1 z hz
    show PadicInt.toZModPow n (h (mob (toGQ m) (mob (ofSL δ) z)) - h (mob (toGQ m) z)) = χ (cj m δ)
    rw [hcomm]
    exact hI (cj m δ) hc2 (mob (toGQ m) z) hmz

end GlobalTheory.KZ.H3
