import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultCellsAmongOfIsPolyFanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionRemovesMaxMultiplicityCellsStatement

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

section Main

variable {O : Type} [CommRing O] {bar : O → O}

theorem maxMult_lt_of_among_zero {q M : ℕ} {φ : InvFun O} (hM : 1 ≤ M) (h : maxMult bar q φ ≤ M)
    (h0 : MultCellsAmong bar q φ M 0) : maxMult bar q φ < M := by
  obtain ⟨R, hR⟩ := h0
  have key : maxMult bar q φ ≤ ((M - 1 : ℕ) : ℕ∞) := by
    unfold maxMult
    refine iSup_le fun X => iSup_le fun i1 => iSup_le fun i2 => iSup_le fun i3 => iSup_le fun i4 => iSup_le fun hX =>
      iSup_le fun m => iSup_le fun δ => iSup_le fun hc => iSup_le fun hli => iSup_le fun hp => ?_
    have hle : ((cellMult bar fun i => (⟨δ i, hc.mem i⟩ : balForms bar X)) : ℕ∞) ≤ M := by
      refine le_trans ?_ h
      unfold maxMult
      exact le_iSup_of_le X <| le_iSup_of_le i1 <| le_iSup_of_le i2 <| le_iSup_of_le i3 <| le_iSup_of_le i4 <|
        le_iSup_of_le hX <| le_iSup_of_le m <| le_iSup_of_le δ <| le_iSup_of_le hc <| le_iSup_of_le hli <|
        le_iSup_of_le hp le_rfl
    have hne : cellMult bar (fun i => (⟨δ i, hc.mem i⟩ : balForms bar X)) ≠ M := fun he =>
      (hR X hX m δ ⟨hc, hli, hp, he⟩).elim fun k _ => k.elim0
    have hle' : cellMult bar (fun i => (⟨δ i, hc.mem i⟩ : balForms bar X)) ≤ M := by exact_mod_cast hle
    exact_mod_cast (show cellMult bar (fun i => (⟨δ i, hc.mem i⟩ : balForms bar X)) ≤ M - 1 by omega)
  exact key.trans_lt (by exact_mod_cast (show M - 1 < M by omega))

end Main

theorem exists_round_lt_maxMult : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (φ lab : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab → SimpLab H.bar q φ lab → maxMult H.bar q φ < ⊤ →
    2 ≤ maxMult H.bar q φ → ∃ φ' lab' : InvFun (𝓞 E), IsPolyFan H.bar q φ' ∧ IsTwInv H φ' ∧ IsTwInv H lab' ∧
      SimpLab H.bar q φ' lab' ∧ Subordinate H.bar q φ' φ ∧ maxMult H.bar q φ' < maxMult H.bar q φ := by
  intro E _ _ _ H q φ lab hD hP hT hL hS hfin h2
  set M := (maxMult H.bar q φ).toNat with hMdef
  have hMe : maxMult H.bar q φ = M := (ENat.coe_toNat hfin.ne).symm
  have hM2 : 2 ≤ M := by rw [hMe] at h2; exact_mod_cast h2
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_multCellsAmong_of_isPolyFan E H q φ hP M
  have key : ∀ (n : ℕ) (φ lab : InvFun (𝓞 E)), IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab →
      SimpLab H.bar q φ lab → maxMult H.bar q φ ≤ M → MultCellsAmong H.bar q φ M n →
      ∃ φ' lab' : InvFun (𝓞 E), IsPolyFan H.bar q φ' ∧ IsTwInv H φ' ∧ IsTwInv H lab' ∧ SimpLab H.bar q φ' lab' ∧
        Subordinate H.bar q φ' φ ∧ maxMult H.bar q φ' < M := by
    intro n
    induction n with
    | zero =>
      intro φ lab hP hT hL hS hle h0
      exact ⟨φ, lab, hP, hT, hL, hS, Subordinate.refl φ, maxMult_lt_of_among_zero (by omega) hle h0⟩
    | succ n ih =>
      intro φ lab hP hT hL hS hle h0
      obtain ⟨φ₁, lab₁, hP₁, hT₁, hL₁, hS₁, hs₁, hle₁, h₁⟩ := GlobalTheory.T.exists_starSubdivision_removes_maxMultiplicity_cells E H q φ lab hD hP hT hL hS M n hM2 hle h0
      obtain ⟨φ', lab', hP', hT', hL', hS', hs', hlt⟩ := ih φ₁ lab₁ hP₁ hT₁ hL₁ hS₁ hle₁ h₁
      exact ⟨φ', lab', hP', hT', hL', hS', hs'.trans hs₁, hlt⟩
  obtain ⟨φ', lab', hP', hT', hL', hS', hs', hlt⟩ := key n φ lab hP hT hL hS hMe.le hn
  exact ⟨φ', lab', hP', hT', hL', hS', hs', hMe ▸ hlt⟩

end GlobalTheory.PolFan
