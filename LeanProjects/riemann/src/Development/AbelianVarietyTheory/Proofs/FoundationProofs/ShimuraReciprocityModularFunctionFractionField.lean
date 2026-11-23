import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoDiagConjCongruenceLiftLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReciprocityLargeLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldSlRightActionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisExponentRootOfUnityExpTwoPiIStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpTwoPiIRatInFieldRootsOfUnityPropertiesStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNRecip

theorem main : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (M : ℕ) (f : T.K), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) f = f) → ∀ ζ : Ω, IsPrimitiveRoot ζ M → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s ζ = ζ ^ d → ∀ γ γ' : SL(2, ℤ), Cong M d γ γ' → T.gal s (T.sl (ofSL γ) f) = T.sl (ofSL γ') (T.gal s f) := by
  intro Ω _ _ _ ε T M f hM hf ζ hζ s d hsd γ γ' hc
  obtain ⟨N₀, hN₀, hrec⟩ := GlobalTheory.T.exists_level_gal_sl_commute Ω ε T f
  set N := N₀ * M with hNdef
  have hN : 0 < N := Nat.mul_pos hN₀ hM
  obtain ⟨⟨d', hd'⟩, hu⟩ := GlobalTheory.T.galois_exponent_rootOfUnity_expTwoPiI Ω ε s N hN
  obtain ⟨u, hu1, -⟩ := hu d' hd'
  have hunit : IsUnit ((d' : ℤ) : ZMod N) := hu1 ▸ u.isUnit
  set ω := eOm ε (1 / (N : ℚ)) with hω
  have hωp : IsPrimitiveRoot ω N := (GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties Ω ε).2.2.2.2.1 N hN
  have hωM : IsPrimitiveRoot (ω ^ N₀) M := hωp.pow hN rfl
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨i, -, hi⟩ := hωM.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hsζ : s ζ = ζ ^ d' := by
    rw [← hi, map_pow, map_pow, hd', ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul]
    ring_nf
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hM.ne'
  have hdd : (d : ZMod M) = d' := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    have := (hζ.zpow_eq_one_iff_dvd (d' - d)).1 (by
      rw [zpow_sub₀ hζ0, ← hsd, ← hsζ, div_self]; exact (map_ne_zero s).2 hζ0)
    exact this
  obtain ⟨hl1, hl2⟩ := GlobalTheory.T.slTwoDiagConjCongruence_lift_level M N d d' hN (Dvd.intro_left N₀ rfl) hdd hunit
  obtain ⟨γ'', hc'', hκ⟩ := hl1 γ γ' hc
  have hact := GlobalTheory.T.modularFunctionFractionField_sl_rightAction Ω ε T
  have hinv : ∀ δ' ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL δ') (T.gal s f) = T.gal s f := by
    intro δ' hδ'
    obtain ⟨δ, hδ, hcδ⟩ := hl2 δ' hδ'
    have := hrec N hN (Dvd.intro M rfl) s d' hd' δ δ' hcδ
    rw [hf δ hδ] at this
    exact this.symm
  rw [hrec N hN (Dvd.intro M rfl) s d' hd' γ γ'' hc'']
  have hγ' : γ' = (γ' * γ''⁻¹) * γ'' := by group
  rw [hγ', map_mul, hact.2, hinv _ hκ]

end GlobalTheory.FNRecip
