import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHL2

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHLMZ

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.CutHL

variable {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem dmin_zero (z z' : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (h : 0 < r + 2) :
    Dmin k r z z' g ⟨0, h⟩ = 1 := by
  unfold Dmin
  exact Matrix.det_isEmpty

theorem qminorOp_zero (a b : Fin 0 → Fin (2 * r + k + 1)) (u : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    qminorOp (EabH (Hpk k r)) a b u f g = f g := by
  unfold qminorOp
  rw [Finset.sum_apply, Fintype.sum_unique]
  simp

theorem AAvop_zero (h : 0 ≤ r) (ell : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) : C3.AAvop k r 0 h ell f g = f g := by
  unfold C3.AAvop
  rw [Fintype.sum_unique, if_pos (Subsingleton.strictMono _), Matrix.det_isEmpty, one_smul, qminorOp_zero]

theorem qminorOp_one (a b : Fin 1 → Fin (2 * r + k + 1)) (u : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    qminorOp (EabH (Hpk k r)) a b u f g =
      (if a 0 = b 0 then u • f g else 0) + EabH (Hpk k r) (a 0) (b 0) f g := by
  unfold qminorOp
  rw [Finset.sum_apply, Fintype.sum_unique]
  simp [QuantumDeterminants.Top]

theorem AAvop_one (h : 1 ≤ r) (x : Q.Mx k r) (w : ℂ)
    (hnf : ∀ p : Fin (2 * r + k + 1), PBG.y0 x ⟨0, by omega⟩ p = if p.val = 2 * r + k then w else 0)
    (ell : ℂ) (f : Q.Mx k r → E) :
    C3.AAvop k r 1 h ell f x =
      w • (ell • f x + Q.EH k r (esI k r ⟨0, by omega⟩) (esI k r ⟨0, by omega⟩) f x) := by
  classical
  unfold C3.AAvop
  have hent : ∀ c : Fin 1 → Fin (2 * r + k + 1),
      (Matrix.of fun a l : Fin 1 => (x⁻¹ *ᵥ bvec (eI k r (Fin.castLE h a))) (c l)).det =
        if (c 0).val = 2 * r + k then w else 0 := by
    intro c
    rw [Matrix.det_unique]
    exact hnf (c 0)
  rw [Finset.sum_eq_single (fun _ => esI k r ⟨0, by omega⟩)]
  · rw [if_pos (Subsingleton.strictMono _), hent, if_pos (by simp [esI]),
      qminorOp_one, if_pos (by simp [C3.sR, esI])]
    simp only [C3.sR, Q.EH] at *
    rw [show ell + ((1 : ℕ) : ℂ) - 1 = ell by push_cast; ring]
    rfl
  · intro c _ hc
    split_ifs with hm
    · rw [hent, if_neg, zero_smul]
      intro h0
      apply hc
      funext l
      rw [Subsingleton.elim l 0]
      ext
      simpa [esI] using h0
    · rfl
  · intro hc; exact absurd (Finset.mem_univ _) hc

end Formalism.FourierDecayAlt.P.CutHLMZ

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.CutHL Formalism.FourierDecayAlt.P.CutHLMZ

theorem minus_zero_of_parts : CutHL.MinusZeroOfParts := by
  intro hNf hDm hT k r j hj z z' E _ _ Dm Φ Z γ τ hj0 hH Y
  subst hj0
  obtain ⟨_, _, hDo, _, hR, hZ, hτ, hγ, hx⟩ := hH
  have hnfy := (hNf k r 0 hj Z τ γ hZ hτ hγ).2
  have hT' := hT E k r 0 hj Dm Φ Z τ γ hDo hR.1 hZ hτ hγ hx
  have hD1 := (hDm k r 0 hj z z' Z τ γ hZ hτ hγ).2
  rw [Matrix.det_isEmpty, one_mul] at hD1
  have hτc : conj τ ≠ 0 := (map_ne_zero _).2 hτ
  have hv0 : ∀ g, D.vLet k r z z' 0 (by omega) (false, Y) 0 Φ g = Φ g := by
    intro g
    rw [PBG.letter_minus_component_zero, dmin_zero, map_one, inv_one, one_smul, AAvop_zero]
  have hv1 : ∀ g, D.vLet k r z z' 0 (by omega) (false, Y) 1 Φ g = 0 := by
    intro g
    unfold D.vLet
    simp
  have hA := AAvop_one (k := k) (r := r) (E := E) hj (x0 k r 0 hj Z τ γ) (conj τ) (fun p => by
      rw [hnfy ⟨0, by omega⟩ p (by simp)]
      have hp := p.isLt
      by_cases hq : p.val = 2 * r + k
      · rw [if_pos (by omega), if_pos hq, hq, Nat.sub_self]; simp [C3.Zb]
      · rw [if_neg (by omega), if_neg hq])
    ((Y : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) Φ
  have hu : ((Y : ℂ) - ((2 * r + k : ℕ) : ℂ) / 2) = (Y : ℂ) - levelZeroKernel k r 0 := by
    unfold levelZeroKernel; rw [Nat.sub_zero]; push_cast; ring
  rw [hu] at hA
  unfold Eq3
  simp only [hv0, hv1]
  rw [PBG.letter_minus_component_zero, hD1, hu, hA, smul_smul, inv_mul_cancel₀ hτc, one_smul, smul_zero, sub_zero, sub_eq_add_neg _ (conj τ • _),
    ← hT']

end Formalism.FourierDecayAlt.P
