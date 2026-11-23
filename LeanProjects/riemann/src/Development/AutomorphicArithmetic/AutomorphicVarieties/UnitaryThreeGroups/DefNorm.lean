import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne

open Matrix UpperTheory.V.U3

theorem UpperTheory.V.U3.isDeform_normalised_iff :
    ∀ {G C : Type} [Group G] [CommRing C] (r r' : G →* GG 3 C) (γ : G → Matrix (Fin 3) (Fin 3) C) (c g₁ : G),
      Normalised c g₁ r → IsDeform r γ r' → (Normalised c g₁ r' ↔ NormCoc c g₁ r γ) := by
  intro G C _ _ r r' γ c g₁ hn hd
  have hc : (r' c).mat = 1 + γ c := by rw [(hd c).2, hn.atc, Matrix.mul_one]
  have hz : zmat c g₁ r' = zmat c g₁ r + zvar c g₁ r γ := by
    simp only [zmat, zvar, (hd _).2, Matrix.add_mul, Matrix.one_mul]
    abel
  have h12 : zmat c g₁ r' 0 1 = zvar c g₁ r γ 0 1 := by
    rw [hz, Matrix.add_apply, hn.z12, zero_add]
  have h21 : zmat c g₁ r' 1 0 = zvar c g₁ r γ 1 0 := by
    rw [hz, Matrix.add_apply, hn.z21, zero_add]
  constructor
  · intro h
    refine ⟨?_, h12 ▸ h.z12, h21 ▸ h.z21⟩
    have := h.atc
    rw [hc] at this
    exact add_eq_left.mp this
  · intro h
    exact ⟨by rw [hc, h.atc, add_zero], h12.trans h.z12, h21.trans h.z21⟩
