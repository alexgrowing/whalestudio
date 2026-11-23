import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevMulVecOutside

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

noncomputable section

namespace GlobalTheory.HCXi.LineStabiliser

open GlobalTheory.LevelUnitary GlobalTheory.LevelStabiliser

variable (k r' : ℕ)

def fst : Fin (2 * (1 + r') + k + 1) := ⟨0, by omega⟩

def lst : Fin (2 * (1 + r') + k + 1) := ⟨2 * (1 + r') + k, by omega⟩

theorem e0_eq : e0 k r' = Pi.single (fst k r') 1 := rfl

theorem gram_mulVec_e0 : Hpk k (1 + r') *ᵥ e0 k r' = Pi.single (lst k r') 1 := by
  ext i
  have hi := i.isLt
  rw [e0_eq, mulVec_single_one, Matrix.col_apply, Pi.single_apply]
  simp only [Hpk, fst, lst, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem star_e0_vecMul_hpk_eq_single_lst : star (e0 k r') ᵥ* Hpk k (1 + r') = Pi.single (lst k r') 1 := by
  ext i
  have hi := i.isLt
  have h : star (e0 k r') = Pi.single (fst k r') 1 := by
    rw [e0_eq, ← Pi.single_star, star_one]
  rw [h, single_one_vecMul, Matrix.row_apply, Pi.single_apply]
  simp only [Hpk, fst, lst, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem pair_e0_left (v : Fin (2 * (1 + r') + k + 1) → ℂ) :
    star (e0 k r') ⬝ᵥ (Hpk k (1 + r') *ᵥ v) = v (lst k r') := by
  rw [dotProduct_mulVec, star_e0_vecMul_hpk_eq_single_lst, single_one_dotProduct]

theorem lift_lst (w : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' w (lst k r') = 0 := by
  unfold liftVec
  rw [dif_neg]
  simp only [lst]
  omega

theorem e0_lst_eq_zero : e0 k r' (lst k r') = 0 := by
  rw [e0_eq, Pi.single_apply, if_neg]
  simp only [lst, fst, Fin.ext_iff]
  omega

theorem decomp (u : Fin (2 * (1 + r') + k + 1) → ℂ) (hu : u (lst k r') = 0) :
    u = liftVec k 1 r' ((incl k 1 r')ᴴ *ᵥ u) + u (fst k r') • e0 k r' := by
  have hc : ∀ j, ((incl k 1 r')ᴴ *ᵥ u) j = u (levPos k 1 r' j) := fun j =>
    inclH_mul k 1 r' (Matrix.of fun a _ => u a) j j
  ext i
  have hi := i.isLt
  rw [Pi.add_apply, Pi.smul_apply, e0_eq, Pi.single_apply, smul_eq_mul]
  unfold liftVec
  by_cases h : 1 ≤ i.val ∧ i.val < 2 * r' + k + 1 + 1
  · rw [dif_pos h, hc, if_neg (by simp only [fst, Fin.ext_iff]; omega), mul_zero, add_zero]
    congr 1
    simp only [levPos, Fin.ext_iff]
    omega
  · rw [dif_neg h, zero_add]
    by_cases h0 : i = fst k r'
    · rw [if_pos h0, mul_one, h0]
    · rw [if_neg h0, mul_zero, ← hu]
      congr 1
      simp only [fst, lst, Fin.ext_iff] at h0 ⊢
      omega

theorem pair_unitary {n : ℕ} (H p : Matrix (Fin n) (Fin n) ℂ) (hp : pᴴ * H * p = H) (v w : Fin n → ℂ) :
    star (p *ᵥ w) ⬝ᵥ (H *ᵥ (p *ᵥ v)) = star w ⬝ᵥ (H *ᵥ v) := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hp]

theorem pair_lift (v w : Fin (2 * r' + k + 1) → ℂ) :
    star (liftVec k 1 r' w) ⬝ᵥ (Hpk k (1 + r') *ᵥ liftVec k 1 r' v) = star w ⬝ᵥ (Hpk k r' *ᵥ v) := by
  rw [liftVec_eq, liftVec_eq, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, gram_inner]

theorem pair_shift (v w : Fin (2 * r' + k + 1) → ℂ) (c d : ℂ) :
    star (liftVec k 1 r' w + d • e0 k r') ⬝ᵥ (Hpk k (1 + r') *ᵥ (liftVec k 1 r' v + c • e0 k r')) =
      star w ⬝ᵥ (Hpk k r' *ᵥ v) := by
  rw [star_add, add_dotProduct, star_smul, smul_dotProduct, pair_e0_left, mulVec_add, dotProduct_add,
    pair_lift, mulVec_smul, gram_mulVec_e0, dotProduct_smul, dotProduct_single_one]
  simp [lift_lst, e0_lst_eq_zero]

theorem acts_through_level_one : ∀ (k r' : ℕ) (a : ℂ), ∀ p ∈ GV k (1 + r'), p *ᵥ e0 k r' = a • e0 k r' → a ≠ 0 ∧ ∃ g₁ ∈ GV k r', ∀ w : Fin (2 * r' + k + 1) → ℂ, ∃ c : ℂ, p *ᵥ liftVec k 1 r' w = liftVec k 1 r' (g₁ *ᵥ w) + c • e0 k r' := by
  intro k r' a p hp he
  have hp' : pᴴ * Hpk k (1 + r') * p = Hpk k (1 + r') := hp
  have ha : a ≠ 0 := by
    rintro rfl
    have h := pair_unitary _ p hp' (Pi.single (lst k r') 1) (e0 k r')
    rw [he, zero_smul, star_zero, zero_dotProduct, pair_e0_left] at h
    simp at h
  have hl : ∀ w, (p *ᵥ liftVec k 1 r' w) (lst k r') = 0 := by
    intro w
    have h := pair_unitary _ p hp' (liftVec k 1 r' w) (e0 k r')
    rw [he, star_smul, smul_dotProduct, pair_e0_left, pair_e0_left, lift_lst, smul_eq_mul] at h
    exact (mul_eq_zero.1 h).resolve_left (star_ne_zero.2 ha)
  have hd : ∀ w, p *ᵥ liftVec k 1 r' w =
      liftVec k 1 r' (((incl k 1 r')ᴴ * p * incl k 1 r') *ᵥ w) +
        (p *ᵥ liftVec k 1 r' w) (fst k r') • e0 k r' := by
    intro w
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← liftVec_eq k 1 r' w]
    exact decomp k r' _ (hl w)
  refine ⟨ha, (incl k 1 r')ᴴ * p * incl k 1 r', ?_, fun w => ⟨_, hd w⟩⟩
  generalize (incl k 1 r')ᴴ * p * incl k 1 r' = g at hd
  show gᴴ * Hpk k r' * g = Hpk k r'
  ext i j
  have h := pair_unitary _ p hp' (liftVec k 1 r' (Pi.single j 1)) (liftVec k 1 r' (Pi.single i 1))
  rw [hd (Pi.single j 1), hd (Pi.single i 1), pair_shift, pair_lift, star_mulVec, ← dotProduct_mulVec,
    mulVec_mulVec, mulVec_mulVec, ← Pi.single_star, star_one, single_one_dotProduct,
    single_one_dotProduct, mulVec_single_one, mulVec_single_one] at h
  exact h

end GlobalTheory.HCXi.LineStabiliser
