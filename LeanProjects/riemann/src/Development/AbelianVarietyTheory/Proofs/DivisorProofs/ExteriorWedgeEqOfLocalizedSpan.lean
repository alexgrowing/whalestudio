import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingMapLinearCombination
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.WedgeDen

theorem alternatingMap_sum_smul_eq_det_smul' {L M N : Type} [Field L] [AddCommGroup M] [Module L M]
    [AddCommGroup N] [Module L N] {n : ℕ} (f : M [⋀^Fin n]→ₗ[L] N) (g : Fin n → M)
    (a : Fin n → Fin n → L) :
    f (fun i => ∑ l, a i l • g l) = (Matrix.of a).det • f g := by
  first
  | exact @_root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination
  | exact _root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination
  | (apply _root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination <;> assumption)
  | (intros; apply _root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AlternatingLinearCombination.alternating_map_linear_combination ..)

theorem exists_smul_ιMulti_eq_smul_ιMulti : ∀ (R L M : Type) [CommRing R] [Field L] [Algebra R L] [AddCommGroup M] [Module L M] (S : Submonoid R) (n : ℕ) (g w : Fin n → M), (∀ i, ∃ r ∈ S, ∃ c : Fin n → R, algebraMap R L r • w i = ∑ l, algebraMap R L (c l) • g l) → ∃ r ∈ S, ∃ c : R, algebraMap R L r • ExteriorAlgebra.ιMulti L n w = algebraMap R L c • ExteriorAlgebra.ιMulti L n g := by
  intro R L M _ _ _ _ _ S n g w h
  classical
  choose r hr c hc using h
  refine ⟨∏ i, r i, prod_mem fun i _ => hr i, (Matrix.of c).det, ?_⟩
  rw [map_prod, ← AlternatingMap.map_smul_univ]
  simp_rw [hc]
  rw [alternatingMap_sum_smul_eq_det_smul', RingHom.map_det]
  rfl

end GlobalTheory.WedgeDen
