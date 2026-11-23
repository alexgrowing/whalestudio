import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameCompletion
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

namespace GlobalTheory.FrameExpansion

open Matrix in
private lemma herm_mulVec_invariant {k r : ℕ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hH : hᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * h = _root_.Formalism.QuantumDeterminants.Hpk k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ w) = _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) v w := by
  simp only [_root_.Formalism.QuantumDeterminants.herm]
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hH]

open Matrix in
private lemma inWb_of_coords_eq_zero {k r : ℕ} {v : Fin (2 * r + k + 1) → ℂ}
    (h1 : ∀ a, v (_root_.Formalism.QuantumDeterminants.eI k r a) = 0) (h2 : ∀ a, v (_root_.Formalism.QuantumDeterminants.esI k r a) = 0) : _root_.Formalism.QuantumDeterminants.inWb k r v := by
  intro i hi
  rcases hi with hi | hi
  · have e : _root_.Formalism.QuantumDeterminants.eI k r ⟨i, hi⟩ = i := Fin.ext rfl
    rw [← e]; exact h1 _
  · have e : _root_.Formalism.QuantumDeterminants.esI k r ⟨2 * r + k - i, by omega⟩ = i :=
      Fin.ext (show 2 * r + k - (2 * r + k - (i : ℕ)) = i by omega)
    rw [← e]; exact h2 _

open Matrix in
private lemma herm_bvec_esI_jet_harmonics {k r : ℕ} (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) v (_root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.esI k r a)) = v (_root_.Formalism.QuantumDeterminants.eI k r a) := by
  rw [_root_.Formalism.QuantumDeterminants.gn_herm_bvec_right, mulVec, dotProduct]
  simp only [_root_.Formalism.FourierDecayAlt.P.Qx3.hpk_row_es, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

open Matrix in
private lemma coord_eI_eq_zero_of_inWb {k r : ℕ} {v : Fin (2 * r + k + 1) → ℂ} (hv : _root_.Formalism.QuantumDeterminants.inWb k r v)
    (a : Fin r) : v (_root_.Formalism.QuantumDeterminants.eI k r a) = 0 :=
  hv _ (Or.inl (show (a : ℕ) < r from a.2))

open Matrix in
private lemma herm_bvec_eI_jet_harmonics {k r : ℕ} (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) v (_root_.Formalism.QuantumDeterminants.bvec (_root_.Formalism.QuantumDeterminants.eI k r a)) = v (_root_.Formalism.QuantumDeterminants.esI k r a) := by
  rw [_root_.Formalism.QuantumDeterminants.gn_herm_bvec_right, mulVec, dotProduct]
  simp only [_root_.Formalism.FourierDecayAlt.P.Qx3.hpk_row_e, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

open Matrix in
private lemma coord_esI_eq_zero_of_inWb {k r : ℕ} {v : Fin (2 * r + k + 1) → ℂ} (hv : _root_.Formalism.QuantumDeterminants.inWb k r v)
    (a : Fin r) : v (_root_.Formalism.QuantumDeterminants.esI k r a) = 0 :=
  hv _ (Or.inr (show r + k < 2 * r + k - (a : ℕ) by have := a.2; omega))

open Matrix in

theorem _root_.GlobalTheory.FrameExpansion.frame_expansion_uw_group :
    ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)), _root_.Formalism.QuantumDeterminants.inWb k r z → 0 < _root_.Formalism.QuantumDeterminants.Tz k r z → _root_.Formalism.FourierDecayAlt.Q.IsFrameOf k r [z] B → (∀ w, _root_.Formalism.QuantumDeterminants.inWb k r w → _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) w z = 0 → w = ∑ c, _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) w (B c) • B c) ∧ ∀ h ∈ _root_.Formalism.QuantumDeterminants.UWset k r z, (∀ w, _root_.Formalism.QuantumDeterminants.inWb k r w → _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) w z = 0 → _root_.Formalism.QuantumDeterminants.inWb k r (h *ᵥ w) ∧ _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ w) z = 0) ∧ (∀ v w, _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) (h *ᵥ v) (h *ᵥ w) = _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hpk k r) v w) ∧ h⁻¹ ∈ _root_.Formalism.QuantumDeterminants.UWset k r z ∧ h * h⁻¹ = 1 ∧ h⁻¹ * h = 1 ∧ ∀ h' ∈ _root_.Formalism.QuantumDeterminants.UWset k r z, h * h' ∈ _root_.Formalism.QuantumDeterminants.UWset k r z := by
  intro k r z B hz hT hB
  have hzz := _root_.Formalism.FourierDecayAlt.P.HermitianFormSums.hzz hT
  refine ⟨fun w hw hwz => _root_.Formalism.FourierDecayAlt.P.HermitianFormSums.complete0 hz hzz hB hw hwz, ?_⟩
  intro h hh
  have hH : hᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * h = _root_.Formalism.QuantumDeterminants.Hpk k r := hh.1
  have hinv := herm_mulVec_invariant hH
  have hfz : h *ᵥ z = z := hh.2.2
  have hdet : IsUnit h.det := _root_.Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hh.1
  refine ⟨fun w hw hwz => ⟨?_, ?_⟩, hinv, _root_.Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_inv hh, mul_nonsing_inv h hdet,
    nonsing_inv_mul h hdet, fun h' hh' => _root_.Formalism.FourierDecayAlt.P.LieBracketMultiplication.uw_mul hh hh'⟩
  · apply inWb_of_coords_eq_zero
    · intro a
      rw [← herm_bvec_esI_jet_harmonics (h *ᵥ w), ← (hh.2.1 a).2, hinv, herm_bvec_esI_jet_harmonics]
      exact coord_eI_eq_zero_of_inWb hw a
    · intro a
      rw [← herm_bvec_eI_jet_harmonics (h *ᵥ w), ← (hh.2.1 a).1, hinv, herm_bvec_eI_jet_harmonics]
      exact coord_esI_eq_zero_of_inWb hw a
  · rw [← hfz, hinv, hwz]

end GlobalTheory.FrameExpansion
