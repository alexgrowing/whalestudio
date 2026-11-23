import Mathlib
import Formalism.PeriodIntegrals.RTTIndependence
import Formalism.YangianSpanCharacter.YangianRTTProofs.RttRelation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstEmbeddingOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EntrywiseSandwichCommute.BlockEmbeddingMulEntrySwap

namespace PI.QmSandwichWork

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P.W

private theorem rtt_commutator_sandwich_eq_of_relations {B : Type*} [Ring B] (R a b u u' e1 e2 : B)
    (hL : b * a * R = R * a * b) (hU : R * u' * u = u * u' * R) :
    b * a * (R * e1 * e2 - e2 * e1 * R) * (u' * u) =
      R * (a * b * e1 * e2 * u' * u) - b * a * e2 * e1 * u * u' * R := by
  rw [mul_sub, sub_mul]
  congr 1
  · calc b * a * (R * e1 * e2) * (u' * u) = b * a * R * (e1 * e2 * u' * u) := by
          simp only [mul_assoc]
      _ = R * a * b * (e1 * e2 * u' * u) := by rw [hL]
      _ = R * (a * b * e1 * e2 * u' * u) := by simp only [mul_assoc]
  · calc b * a * (e2 * e1 * R) * (u' * u) = b * a * e2 * e1 * (R * u' * u) := by
          simp only [mul_assoc]
      _ = b * a * e2 * e1 * (u * u' * R) := by rw [hU]
      _ = b * a * e2 * e1 * u * u' * R := by simp only [mul_assoc]

theorem main : PI.RTTSandwich := by
  intro A _ _ QQ p c ci p' c' ci' hW hW' hcomm hQ Y Y'
  dsimp only
  have qc : ∀ x ∈ ({p, c, ci, p', c', ci'} : Set A), ∀ (y : ℂ) (i j : Fin 2),
      Commute x (QQ y i j) := fun x hx y i j => hQ x hx y i j
  have PP : ∀ x ∈ ({p, c, ci} : Set A), ∀ y ∈ ({p', c', ci'} : Set A), Commute x y :=
    fun x hx y hy => hcomm x hx y hy
  have TQ : ∀ (y y' : ℂ) (i j k l : Fin 2),
      Commute (Formalism.YangianSpanCharacter.T.Tm y p c ci i j) (QQ y' k l) := fun y y' i j k l =>
    tm_entry_comm y (qc p (by simp) y' k l) (qc c (by simp) y' k l) (qc ci (by simp) y' k l) i j
  have TQ' : ∀ (y y' : ℂ) (i j k l : Fin 2),
      Commute (Formalism.YangianSpanCharacter.T.Tm y p' c' ci' i j) (QQ y' k l) := fun y y' i j k l =>
    tm_entry_comm y (qc p' (by simp) y' k l) (qc c' (by simp) y' k l)
      (qc ci' (by simp) y' k l) i j
  have TT : ∀ (y y' : ℂ) (i j k l : Fin 2),
      Commute (Formalism.YangianSpanCharacter.T.Tm y p c ci i j) (Formalism.YangianSpanCharacter.T.Tm y' p' c' ci' k l) := fun y y' i j k l =>
    tm_entry_comm y
      (tm_entry_comm y' (PP p (by simp) p' (by simp)).symm (PP p (by simp) c' (by simp)).symm
        (PP p (by simp) ci' (by simp)).symm k l).symm
      (tm_entry_comm y' (PP c (by simp) p' (by simp)).symm (PP c (by simp) c' (by simp)).symm
        (PP c (by simp) ci' (by simp)).symm k l).symm
      (tm_entry_comm y' (PP ci (by simp) p' (by simp)).symm (PP ci (by simp) c' (by simp)).symm
        (PP ci (by simp) ci' (by simp)).symm k l).symm i j
  have t1 : ∀ (y : ℂ) (a b d : A),
      Formalism.YangianSpanCharacter.T.T1 y a b d = Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm y a b d) := fun _ _ _ _ => rfl
  have t2 : ∀ (y : ℂ) (a b d : A),
      Formalism.YangianSpanCharacter.T.T2 y a b d = Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm y a b d) := fun _ _ _ _ => rfl
  have hR := Formalism.YangianSpanCharacter.P.rttRelation ℂ A p c ci Y Y' hW
  have hR' := Formalism.YangianSpanCharacter.P.rttRelation ℂ A p' c' ci' Y Y' hW'
  have key := rtt_commutator_sandwich_eq_of_relations ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) -
      Formalism.YangianSpanCharacter.T.Pf A) (Formalism.YangianSpanCharacter.T.T1 Y' p' c' ci') (Formalism.YangianSpanCharacter.T.T2 Y p' c' ci')
      (Formalism.YangianSpanCharacter.T.T2 Y p c ci) (Formalism.YangianSpanCharacter.T.T1 Y' p c ci)
      (Formalism.YangianSpanCharacter.T.E1 (QQ Y')) (Formalism.YangianSpanCharacter.T.E2 (QQ Y)) hR'.symm hR
  have s1 := (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute (QQ Y') (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci')
    (fun i j k l => (TQ' Y Y' k l i j).symm.eq)).symm
  have s2 := (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) (QQ Y)
    (fun i j k l => (TQ Y' Y i j k l).eq)).symm
  have s3 := (Formalism.FourierDecayAlt.P.W.first_second_embedding_commute (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci')
    (fun i j k l => (TT Y' Y i j k l).eq)).symm
  have r1 := Formalism.FourierDecayAlt.P.W.first_second_embedding_commute (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') (QQ Y)
    (fun i j k l => (TQ' Y' Y i j k l).eq)
  have r2 := Formalism.FourierDecayAlt.P.W.first_second_embedding_commute (QQ Y') (Formalism.YangianSpanCharacter.T.Tm Y p c ci)
    (fun i j k l => (TQ Y Y' k l i j).symm.eq)
  have r3 := Formalism.FourierDecayAlt.P.W.first_second_embedding_commute (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') (Formalism.YangianSpanCharacter.T.Tm Y p c ci)
    (fun i j k l => (TT Y Y' k l i j).symm.eq)
  have hK1 : Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') *
      Formalism.YangianSpanCharacter.T.E1 (QQ Y') * Formalism.YangianSpanCharacter.T.E2 (QQ Y) * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) *
      Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) =
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci' * QQ Y' * Formalism.YangianSpanCharacter.T.Tm Y' p c ci) *
      Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci' * QQ Y * Formalism.YangianSpanCharacter.T.Tm Y p c ci) := by
    rw [Formalism.FourierDecayAlt.P.W.first_embedding_mul, Formalism.FourierDecayAlt.P.W.first_embedding_mul, Formalism.FourierDecayAlt.P.W.entries_mem_mul, Formalism.FourierDecayAlt.P.W.entries_mem_mul]
    simp only [mul_assoc]
    rw [swap_l s1, swap_l s2, swap_l s3]
  have hK2 : Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci') * Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci') *
      Formalism.YangianSpanCharacter.T.E2 (QQ Y) * Formalism.YangianSpanCharacter.T.E1 (QQ Y') * Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p c ci) *
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p c ci) =
      Formalism.YangianSpanCharacter.T.E2 (Formalism.YangianSpanCharacter.T.Tm Y p' c' ci' * QQ Y * Formalism.YangianSpanCharacter.T.Tm Y p c ci) *
      Formalism.YangianSpanCharacter.T.E1 (Formalism.YangianSpanCharacter.T.Tm Y' p' c' ci' * QQ Y' * Formalism.YangianSpanCharacter.T.Tm Y' p c ci) := by
    rw [Formalism.FourierDecayAlt.P.W.first_embedding_mul, Formalism.FourierDecayAlt.P.W.first_embedding_mul, Formalism.FourierDecayAlt.P.W.entries_mem_mul, Formalism.FourierDecayAlt.P.W.entries_mem_mul]
    simp only [mul_assoc]
    rw [swap_l r1, swap_l r2, swap_l r3]
  rw [key, Matrix.sub_apply, flip_row, flip_col]
  simp only [t1, t2]
  rw [hK1, hK2, block_embedding_mul_entry, block_embedding_mul_entry_swap, mul_sub]

end PI.QmSandwichWork
