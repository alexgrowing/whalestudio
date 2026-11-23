import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHL2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RdVOfEq

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem zfull_zb {j : ℕ} (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (a b : Fin (j + 1)) :
    zfull Z τ a b = C3.Zb j 1 Z τ a.val b.val := by
  rw [zfull_apply]
  unfold C3.Zb
  have := a.isLt; have := b.isLt
  by_cases h1 : a.val < j ∧ b.val < j
  · rw [dif_pos h1, dif_pos h1.1, dif_pos h1.2]
  · rw [dif_neg h1]
    by_cases ha : a.val < j
    · have hb : ¬ b.val < j := fun hb => h1 ⟨ha, hb⟩
      rw [dif_pos ha, dif_neg hb, if_neg (fun h => by omega)]
    · rw [dif_neg ha]
      by_cases h2 : a.val = j ∧ b.val = j
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

theorem normal_form_x0 : NormalFormsAtBasePoint := by
  intro k r j hj Z τ γ hZ hτ hγ
  refine ⟨fun a p ha => ?_, fun a p ha => ?_⟩
  · rw [upper_minor_of_level_point hj Z τ γ a p ha]
    by_cases hp : p.val < j + 1
    · rw [dif_pos hp, if_pos hp]
      exact zfull_zb Z τ _ _
    · rw [dif_neg hp, if_neg hp]
  · rw [lower_minor_of_level_point hj hZ hτ hγ a p ha]
    by_cases hp : r + k < p.val ∧ 2 * r + k - p.val < j + 1
    · rw [dif_pos hp, if_pos hp]
      exact congrArg star (zfull_zb Z τ _ _)
    · rw [dif_neg hp, if_neg hp]

theorem leading_minors_at_base_point : LeadingMinorsAtBasePoint := by
  intro k r j hj z z' Z τ γ hZ hτ hγ
  have hnf := (normal_form_x0 k r j hj Z τ γ hZ hτ hγ).1
  have hd := Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb j 1 Z τ
  refine ⟨?_, ?_⟩
  · rw [PBG.dmin_nf z z' _ j 1 Z τ hj hnf j (by omega), hd.1]
  · rw [PBG.dmin_nf z z' _ j 1 Z τ hj hnf (j + 1) le_rfl, hd.2]
    simp [C3.sgnW]

theorem first_component_of_parts : Comp1OfParts := by
  intro hNf k r j hj z z' E _ _ Dm Φ Z γ τ hH Y
  obtain ⟨hz, hz', hD, hDs, hR, hZ, hτ, hγ, hx⟩ := hH
  obtain ⟨hnf, hnfy⟩ := hNf k r j hj Z τ γ hZ hτ hγ
  have hxG : x0 k r j hj Z τ γ ∈ B.GV k r := x0_GV hj hZ hτ hγ
  have hx1 : x0 k r j hj Z τ γ ∈ Q.Glev k r 0 ∩ Dm := ⟨⟨hxG, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hx⟩
  have hK : Q.SmoothLev k r 0 Dm Φ := hR.1
  have hRule : ∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ p q, C3.InNp k r p q → Q.EH k r p q Φ g = C3.dpsiP k r z' p q • Φ g :=
    fun g hg p q hpq => Formalism.FourierDecayAlt.P.rule_of_eq E k r z' Φ g hz' (fun n hn => (hR.2.1 g hg n hn).2) p q hpq
  refine ⟨?_, ?_⟩
  · have h := PBG.letter_plus_component_one_eq_smul_component_zero hD z z' j 1 le_rfl hj Z τ hZ hτ _ hx1 hnf Φ hK hRule Y
    rw [show ((-1 : ℂ) ^ (1 - 1) * τ⁻¹) = τ⁻¹ by simp] at h
    exact h
  · have h := PBG.letter_minus_component_one_eq_smul_component_zero hD z z' j 1 le_rfl hj Z τ hZ hτ _ hx1 hxG hnf hnfy Φ hK hRule Y
    rw [show ((-1 : ℂ) ^ (1 - 1) * (conj τ)⁻¹) = (conj τ)⁻¹ by simp] at h
    exact h

theorem headLetter_of_open (hL : LeftActionRuleAtBasePoint) (hT : TorusDirectionAtBasePoint) (hSL : ConjugateActionRuleAtBasePoint) (hST : ConjugateTorusDirectionAtBasePoint)
    (hFX : FrozenX) (hFV : FrozenV) (hPP : PlusPosOfParts) (hPZ : PlusZeroOfParts) (hMP : MinusPosOfParts)
    (hMZ : MinusZeroOfParts) : LevelPointCoordinates.HeadLetter :=
  headLetter_of_leaves normal_form_x0 leading_minors_at_base_point hL hT hSL hST hFX hFV first_component_of_parts hPP hPZ hMP hMZ

end Formalism.FourierDecayAlt.P.CutHL
