import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnfoldingAffineLinearMapAddEqAddFrM

noncomputable section

namespace GlobalTheory.PadicUnfold.Period

open Formalism.L2.Col GlobalTheory.IndefiniteRowSideFullHecke.UnfoldedLatticeData

def extZero {k : Type} [CommRing k] {n' n : ℕ} (c' c : ℕ) (y : (Fin n' → k) →ₗ[k] (Fin n → k)) :
    (Fin (n' + c') → k) →ₗ[k] (Fin (n + c) → k) :=
  Matrix.toLin' (Matrix.of fun (l : Fin (n + c)) (s : Fin (n' + c')) =>
    if hs : s.1 < n' then
      (if hl : l.1 < n then y (Pi.single ⟨s.1, hs⟩ 1) ⟨l.1, hl⟩ else 0) else 0)

theorem extZero_single {k : Type} [CommRing k] {n' n : ℕ} (c' c : ℕ)
    (y : (Fin n' → k) →ₗ[k] (Fin n → k)) (s : Fin (n' + c')) (l : Fin (n + c)) :
    extZero c' c y (Pi.single s 1) l = if hs : s.1 < n' then
      (if hl : l.1 < n then y (Pi.single ⟨s.1, hs⟩ 1) ⟨l.1, hl⟩ else 0) else 0 := by
  simp [extZero, Matrix.toLin'_apply]

theorem periodXX1_add_smul {k : Type} [CommRing k] {n' c' n c : ℕ} (a : k)
    (x y : (Fin n' → k) →ₗ[k] (Fin n → k)) (t : Loc.FC n' c' n c → k) :
    Loc.xx1 (x + a • y) t = Loc.xx1 x t + a • extZero c' c y := by
  refine hom_ext fun s l => ?_
  rw [LinearMap.add_apply, Pi.add_apply, LinearMap.smul_apply, Pi.smul_apply, linearMap_unfolding_apply_single, linearMap_unfolding_apply_single,
    extZero_single]
  by_cases hf : Loc.IsFree n' n c l.1 s.1
  · have hs : ¬ s.1 < n' := not_lt.2 hf.1
    simp [hf, hs]
  · by_cases hs : s.1 < n'
    · by_cases hl : l.1 < n <;> simp [hf, hs, hl]
    · simp [hf, hs]

theorem chArg_smul_extZero {k : Type} [CommRing k] {n' n c : ℕ} (a : k)
    (y : (Fin n' → k) →ₗ[k] (Fin n → k)) : Loc.chArg (a • extZero (c + 1) c y) = 0 := by
  rw [chArg_eq]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, extZero_single, dif_neg (by simp; omega), smul_zero]

variable {g : ℕ} [Fact g.Prime]

end GlobalTheory.PadicUnfold.Period
