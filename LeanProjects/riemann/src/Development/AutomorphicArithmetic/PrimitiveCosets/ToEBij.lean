import Development.AutomorphicArithmetic.PrimitiveCosets.RecH

open UpperTheory.Comparison₂ Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LHost

private theorem UpperTheory.Comparison₂.sign_character_bijective : Function.Bijective Formalism.LFunctionChainParameters.LHost.sgn2 := by
  constructor
  · intro a b h
    have h' := congrArg Multiplicative.toAdd h
    rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or b with rfl | rfl
    · rfl
    · exact absurd h' (by decide)
    · exact absurd h' (by decide)
    · rfl
  · intro y
    by_cases hy : Multiplicative.toAdd y = 0
    · refine ⟨1, Multiplicative.toAdd.injective ?_⟩
      rw [hy]
      decide
    · refine ⟨-1, Multiplicative.toAdd.injective ?_⟩
      have h1 : Multiplicative.toAdd y = 1 := by
        generalize Multiplicative.toAdd y = z at hy ⊢
        revert z
        decide
      rw [h1]
      decide

private theorem UpperTheory.Comparison₂.sign_character_one : Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 1) = 0 := by decide

private theorem UpperTheory.Comparison₂.sign_character_neg_one : Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 (-1)) = 1 := by decide

private theorem UpperTheory.Comparison₂.sign_character_zero_iff : ∀ u : ℤˣ, u = 1 ↔ Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 u) = 0 := by
  intro u
  rcases Int.units_eq_one_or u with rfl | rfl
  · exact iff_of_true rfl UpperTheory.Comparison₂.sign_character_one
  · exact iff_of_false (by decide) (by rw [UpperTheory.Comparison₂.sign_character_neg_one]; decide)

theorem UpperTheory.Comparison₂.toE_bij :
    ∀ φ : Frame, Function.Bijective (toE φ) ∧ toE φ φ.iod = Multiplicative.ofAdd sgc0 ∧ toE φ φ.cc = Multiplicative.ofAdd cconj ∧
      (∀ t, toE φ (φ.tau1 t) = Multiplicative.ofAdd ((0 : E0), t)) ∧ ∀ g : φ.GG, g ∈ φ.Psi ↔ InPhi (Multiplicative.toAdd (toE φ g)) := by
  intro φ
  have hs := UpperTheory.Comparison₂.sign_character_bijective
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rintro ⟨⟨a1, a2⟩, m⟩ ⟨⟨b1, b2⟩, n⟩ h
    have h' := congrArg Multiplicative.toAdd h
    change ((Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 a2), Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 a1)), φ.iotaInv m) =
      ((Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 b2), Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 b1)), φ.iotaInv n) at h'
    simp only [Prod.mk.injEq] at h'
    obtain ⟨⟨h2, h1⟩, h3⟩ := h'
    have e1 : a1 = b1 := hs.1 (Multiplicative.toAdd.injective h1)
    have e2 : a2 = b2 := hs.1 (Multiplicative.toAdd.injective h2)
    have e3 : m = n := by
      have h4 := congrArg φ.iota h3
      rwa [Frame.iota_iotaInv, Frame.iota_iotaInv] at h4
    subst e1
    subst e2
    subst e3
    rfl
  · intro y
    obtain ⟨u1, hu1⟩ := hs.2 (Multiplicative.ofAdd (Multiplicative.toAdd y).1.2)
    obtain ⟨u2, hu2⟩ := hs.2 (Multiplicative.ofAdd (Multiplicative.toAdd y).1.1)
    refine ⟨((u1, u2), φ.iota (Multiplicative.toAdd y).2), ?_⟩
    apply Multiplicative.toAdd.injective
    change ((Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 u2), Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 u1)),
      φ.iotaInv (φ.iota (Multiplicative.toAdd y).2)) = Multiplicative.toAdd y
    rw [hu1, hu2, Frame.iotaInv_iota]
    rfl
  · apply Multiplicative.toAdd.injective
    change ((Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 (-1)), Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 1)),
      φ.iotaInv 1) = ((1, 0), 0)
    rw [UpperTheory.Comparison₂.sign_character_neg_one, UpperTheory.Comparison₂.sign_character_one]
    rfl
  · apply Multiplicative.toAdd.injective
    change ((Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 (-1)), Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 (-1))),
      φ.iotaInv 1) = ((1, 1), 0)
    rw [UpperTheory.Comparison₂.sign_character_neg_one]
    rfl
  · intro t
    apply Multiplicative.toAdd.injective
    change ((Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 1), Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 1)),
      φ.iotaInv (φ.iota t)) = (((0 : ZMod 2), (0 : ZMod 2)), t)
    rw [UpperTheory.Comparison₂.sign_character_one, Frame.iotaInv_iota]
  · intro g
    show φ.chD g = 1 ↔ _
    exact UpperTheory.Comparison₂.sign_character_zero_iff g.1.2
