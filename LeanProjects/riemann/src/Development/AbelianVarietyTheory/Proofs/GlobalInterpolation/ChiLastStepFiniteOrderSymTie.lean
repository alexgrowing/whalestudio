import Mathlib
import Formalism.LocalToGlobal.HermitianForms.TiedSym
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GLevHChiPowEqOneAndMemRange
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CardResidueFieldTotallyRealTypePrimeStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LamJMemRangeAndPowEqOne
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem chi_last_step_finite_order_symTie : ∀ (D : D7) (u : D.what₂.Word) (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (Tf : FormsTiedSym D u Ch chOf), (∀ i, (∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i)) ∧ ∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i - 1)) → ∃ n : ℕ, 0 < n ∧ ∀ x : (Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.U, (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) ^ n = 1 ∧ ∃ r : D.what₂.LL, D.what₂.embLL r = (((Tf.cls D.R.m le_rfl (Or.inr rfl)).lev.chi x : ℂˣ) : ℂ) := by
  intro D u Ch chOf Tf hζ
  have hpos : ∀ i, 0 < D.host.g i * (D.host.g i - 1) := fun i =>
    Nat.mul_pos (D.host.g_prime i).pos (Nat.sub_pos_of_lt (D.host.g_prime i).one_lt)
  refine ⟨∏ i, D.host.g i * (D.host.g i - 1), Finset.prod_pos fun i _ => hpos i, ?_⟩
  refine GlobalTheory.gLevH_chi_pow_eq_one_and_mem_range _ _ _ _ _ _ _ _ _ _ _ _ _ Tf.glevM D.what₂.LL D.what₂.embLL _ D.host.g_prime ?_
  intro a v h M
  have key : (∃ r : D.what₂.LL, D.what₂.embLL r = ((Tf.lamM a v h M : ℂˣ) : ℂ)) ∧
      (((Tf.lamM a v h M : ℂˣ) : ℂ) ≠ 0 → ((Tf.lamM a v h M : ℂˣ) : ℂ) ^ (D.host.g a * (D.host.g a - 1)) = 1) := by
    rw [Tf.lamM_eq]
    unfold lamSym
    exact GlobalTheory.lamJ_mem_range_and_pow_eq_one _ D.what₂.LL D.what₂.embLL _ (D.host.g_prime a) (GlobalTheory.T.card_residue_field_totally_real_type_prime D a v h) (hζ a).1 (hζ a).2
      _ _ _ _ _ _ _ _
  refine ⟨?_, key.1⟩
  obtain ⟨c, hc⟩ : D.host.g a * (D.host.g a - 1) ∣ ∏ i, D.host.g i * (D.host.g i - 1) :=
    Finset.dvd_prod_of_mem (fun i => D.host.g i * (D.host.g i - 1)) (Finset.mem_univ a)
  rw [hc, pow_mul, key.2 (Units.ne_zero _), one_pow]

end GlobalTheory
