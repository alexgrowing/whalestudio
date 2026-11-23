import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InfiniteMeasureTransfer.MeasInfXferOf

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Matrix

namespace Formalism.L2.SG.Pf.MeasInfW

theorem continuous_uMat_at (I : AutInst) (v : InfinitePlace I.F) :
    Continuous fun s : I.Ginf => uMat (s v) := by
  first
  | exact Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply v))
  | fun_prop
  | continuity

theorem isClosed_mulVec_mem {n : ℕ} (x : Fin n → ℂ) (W : Submodule ℂ (Fin n → ℂ)) :
    IsClosed {M : Matrix (Fin n) (Fin n) ℂ | (M - 1) *ᵥ x ∈ W} := by
  have hW : IsClosed (W : Set (Fin n → ℂ)) := W.closed_of_finiteDimensional
  exact hW.preimage ((continuous_id.sub continuous_const).matrix_mulVec continuous_const)

theorem isClosed_InN {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    IsClosed {M : Matrix (Fin n) (Fin n) ℂ | InN ε e z M} := by
  have h1 : {M : Matrix (Fin n) (Fin n) ℂ | InN ε e z M} =
      ((⋂ a : Fin r, {M : Matrix (Fin n) (Fin n) ℂ | (M - 1) *ᵥ e a ∈ spanLt e a.1}) ∩
        {M : Matrix (Fin n) (Fin n) ℂ | (M - 1) *ᵥ z ∈ spanLt e r}) ∩
        ⋂ y : Fin n → ℂ, ⋂ (_ : ∀ a, hJ ε (e a) y = 0),
          {M : Matrix (Fin n) (Fin n) ℂ | (M - 1) *ᵥ y ∈ spanLt e r} := by
    ext M
    simp only [InN, InS, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [h1]
  exact ((isClosed_iInter fun a => isClosed_mulVec_mem _ _).inter (isClosed_mulVec_mem _ _)).inter
    (isClosed_iInter fun y => isClosed_iInter fun _ => isClosed_mulVec_mem _ _)

theorem nilpotent_measure_closed_form : NClosed := by
  intro I r e z
  have h1 : Ninf I e z = ⋂ v, (fun s : I.Ginf => uMat (s v)) ⁻¹'
      {M : Matrix (Fin I.n) (Fin I.n) ℂ | InN (I.ε v) (fun a => rv I v (e a)) (rv I v z) M} := by
    ext s
    simp only [Ninf, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h1]
  exact isClosed_iInter fun v => (isClosed_InN _ _ _).preimage (continuous_uMat_at I v)

theorem hermitian_measure_closed_form : HClosed := by
  intro I S
  have h1 : Hset I S = ⋂ v, ⋂ x ∈ S, (fun s : I.Ginf => uMat (s v)) ⁻¹'
      {M : Matrix (Fin I.n) (Fin I.n) ℂ | M *ᵥ rv I v x = rv I v x} := by
    ext s
    simp only [Hset, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [h1]
  refine isClosed_iInter fun v => isClosed_biInter fun x _ =>
    IsClosed.preimage (continuous_uMat_at I v) ?_
  exact isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const

end Formalism.L2.SG.Pf.MeasInfW
