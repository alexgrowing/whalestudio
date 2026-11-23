import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.CrossG
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.UpDownX
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NormVal

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem win_pow_iff (N M f : ℕ) (hf : 0 < f) (hM : M = N ^ f) (a b x y : ℝ) (hx : 0 ≤ x) (hy : y = x ^ f) :
    ((M : ℝ) ^ a < y ∧ y < (M : ℝ) ^ b) ↔ ((N : ℝ) ^ a < x ∧ x < (N : ℝ) ^ b) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have key : ∀ c : ℝ, (M : ℝ) ^ c = ((N : ℝ) ^ c) ^ f := by
    intro c
    rw [hM, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hN, ← Real.rpow_mul hN, mul_comm]
  rw [key, key, hy, pow_lt_pow_iff_left₀ (Real.rpow_nonneg hN _) hx hf.ne',
    pow_lt_pow_iff_left₀ hx (Real.rpow_nonneg hN _) hf.ne']

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winUpDown :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.WinUpDown := by
  intro K L _ _ _ _ _ _ _ _ hp n hn π P hbc t v
  have hn1 : 1 ≤ n := le_trans one_le_two hn
  have hUD := upDown K L hp n hn π P hbc v
  obtain ⟨s, hs⟩ := (suppFacts K n hn1 π v).1
  have hex : ∀ w : GroundTheory.Global.SemiLocal.PlacesOver L v, ∃ s', SuppAt P w.1 s' := fun w => (suppFacts L n hn1 P w.1).1
  choose s' hs' using hex
  have hX := upDownX K L hp n hn π P hbc v s s' hs hs'
  refine ⟨fun hW w => ?_, fun hW => ?_⟩
  · refine ⟨⟨(hUD.1 hW.1 w).1, fun s₁ hs₁ ζ hζ => ?_⟩, (hUD.1 hW.1 w).2⟩
    have e : s₁ = s' w := (suppFacts L n hn1 P w.1).2.1 _ _ hs₁ (hs' w)
    rw [e] at hζ
    obtain ⟨ξ, hξ, rfl⟩ := hX.1 hW.1 w ζ hζ
    have hv := normVal K L v w ξ
    exact (win_pow_iff _ _ _ hv.2.2.1 hv.2.2.2 _ _ _ _ (norm_nonneg _) (hv.2.1 hξ.choose)).2 (hW.2 s hs ξ hξ)
  · refine ⟨hUD.2 fun w => ⟨(hW w).1.1, (hW w).2⟩, fun s₁ hs₁ ξ hξ => ?_⟩
    have e : s₁ = s := (suppFacts K n hn1 π v).2.1 _ _ hs₁ hs
    rw [e] at hξ
    obtain ⟨w, hw⟩ := hX.2 ξ hξ
    have hv := normVal K L v w ξ
    exact (win_pow_iff _ _ _ hv.2.2.1 hv.2.2.2 _ _ _ _ (norm_nonneg _) (hv.2.1 hξ.choose)).1 ((hW w).1.2 _ (hs' w) _ hw)
