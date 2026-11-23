import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHL2

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHLPZ

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

theorem AAop_zero (h : 0 ≤ r) (u : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) : C3.AAop k r 0 h u f g = f g := by
  unfold C3.AAop
  rw [Fintype.sum_unique, if_pos (Subsingleton.strictMono _), Matrix.det_isEmpty, one_smul, qminorOp_zero]

theorem qminorOp_one (a b : Fin 1 → Fin (2 * r + k + 1)) (u : ℂ) (f : Q.Mx k r → E) (g : Q.Mx k r) :
    qminorOp (EabH (Hpk k r)) a b u f g =
      (if a 0 = b 0 then u • f g else 0) + EabH (Hpk k r) (a 0) (b 0) f g := by
  unfold qminorOp
  rw [Finset.sum_apply, Fintype.sum_unique]
  simp [QuantumDeterminants.Top]

theorem AAop_one (h : 1 ≤ r) (x : Q.Mx k r) (τ : ℂ)
    (hnf : ∀ p : Fin (2 * r + k + 1), PBG.xi0 x ⟨0, by omega⟩ p = if p.val = 0 then τ else 0)
    (u : ℂ) (f : Q.Mx k r → E) :
    C3.AAop k r 1 h u f x = τ • (u • f x + Q.EH k r (eI k r ⟨0, by omega⟩) (eI k r ⟨0, by omega⟩) f x) := by
  classical
  unfold C3.AAop
  have hent : ∀ c : Fin 1 → Fin (2 * r + k + 1),
      (Matrix.of fun a l : Fin 1 =>
        herm (Hpk k r) (x *ᵥ bvec (c l)) (bvec (eI k r (Fin.castLE h a)))).det =
        if (c 0).val = 0 then τ else 0 := by
    intro c
    rw [Matrix.det_unique]
    exact hnf (c 0)
  rw [Finset.sum_eq_single (fun _ => eI k r ⟨0, by omega⟩)]
  · rw [if_pos (Subsingleton.strictMono _), hent, if_pos (by simp [eI]),
      qminorOp_one, if_pos (by simp [C3.xR, eI])]
    simp [C3.xR, eI, Q.EH]
  · intro c _ hc
    split_ifs with hm
    · rw [hent, if_neg, zero_smul]
      intro h0
      apply hc
      funext l
      rw [Subsingleton.elim l 0]
      ext
      simpa [eI] using h0
    · rfl
  · intro hc; exact absurd (Finset.mem_univ _) hc

end Formalism.FourierDecayAlt.P.CutHLPZ

namespace Formalism.FourierDecayAlt.P

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.CutHL Formalism.FourierDecayAlt.P.CutHLPZ

theorem plus_zero_of_parts : CutHL.PlusZeroOfParts := by
  intro hNf hDm hT k r j hj z z' E _ _ Dm Φ Z γ τ hj0 hH Y
  subst hj0
  obtain ⟨_, _, hDo, _, hR, hZ, hτ, hγ, hx⟩ := hH
  have hnf := (hNf k r 0 hj Z τ γ hZ hτ hγ).1
  have hT' := hT E k r 0 hj Dm Φ Z τ γ hDo hR.1 hZ hτ hγ hx
  have hD1 := (hDm k r 0 hj z z' Z τ γ hZ hτ hγ).2
  rw [Matrix.det_isEmpty, one_mul] at hD1
  have hv0 : ∀ g, D.vLet k r z z' 0 (by omega) (true, Y) 0 Φ g = Φ g := by
    intro g
    rw [PBG.letter_plus_component_zero, dmin_zero, inv_one, one_smul, AAop_zero]
  have hv1 : ∀ g, D.vLet k r z z' 0 (by omega) (true, Y) 1 Φ g = 0 := by
    intro g
    unfold D.vLet
    simp
  have hA := AAop_one (k := k) (r := r) (E := E) hj (x0 k r 0 hj Z τ γ) τ (fun p => by
      rw [hnf ⟨0, by omega⟩ p (by simp)]
      by_cases hp : p.val = 0
      · rw [if_pos (by omega), if_pos hp, hp]; simp [C3.Zb]
      · rw [if_neg (by omega), if_neg hp])
    ((Y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) Φ
  have hu : ((Y : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) = (Y : ℂ) + levelZeroKernel k r 0 := by
    unfold levelZeroKernel; rw [Nat.sub_zero]; push_cast; ring
  rw [hu] at hA
  unfold Eq1
  simp only [hv0, hv1]
  rw [PBG.letter_plus_component_zero, hD1, hu, hA, ← hT', smul_smul, inv_mul_cancel₀ hτ, one_smul, smul_zero, sub_zero]

end Formalism.FourierDecayAlt.P
