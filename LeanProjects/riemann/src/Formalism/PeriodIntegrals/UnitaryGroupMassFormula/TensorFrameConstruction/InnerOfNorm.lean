import Mathlib
import Formalism.PeriodIntegrals.ScPiExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorFrameConstruction.LocalFramePreservesOrthogonal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorFrameConstruction.LocFrame
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorFrameConstruction.ContinuousOnTensOp

noncomputable section

open NumberField Matrix
open scoped InnerProductSpace

namespace PI.ScPiBuildW.Asm

open PI.ScPiExists Formalism.MainNotions.S

lemma inner_of_norm {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : H →L[ℂ] H)
    (hT : ∀ v, ‖T v‖ = ‖v‖) (u w : H) : ⟪T u, T w⟫_ℂ = ⟪u, w⟫_ℂ :=
  (⟨T.toLinearMap, hT⟩ : H →ₗᵢ[ℂ] H).inner_map_map u w

lemma uMat_one (I : AutInst) (v : InfinitePlace I.F) : uMat ((1 : I.Ginf) v) = 1 := rfl

lemma uMat_mul (I : AutInst) (s t : I.Ginf) (v : InfinitePlace I.F) :
    uMat ((s * t) v) = uMat (s v) * uMat (t v) := rfl

lemma inUJ_uMat (I : AutInst) (s : I.Ginf) (v : InfinitePlace I.F) : Formalism.REAL.inUJ (I.ε v) (uMat (s v)) :=
  (s v).2

lemma cont_uMat (I : AutInst) (v : InfinitePlace I.F) : Continuous fun s : I.Ginf => uMat (s v) :=
  Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply v))

theorem build : Build := by
  intro hW I r k e f z lam hn hF hz hlam hw
  classical
  choose w hw using hw
  choose H hHN hHI pl hπ using fun v => hW k (lam v) (hlam v)
  let _ := hHN
  let _ := hHI
  have hHF : ∀ v, FiniteDimensional ℂ (H v) := fun v => (hπ v).2.1
  let L : ∀ v, Loc.LocFrame I.n r k (I.ε v) := fun v => Rv.locFrame I e f z hn hF hz v (w v) (hw v)
  let A : I.Ginf → ∀ v, H v →L[ℂ] H v := fun s v => pl v ((L v).M (uMat (s v)))
  have hA1 : A 1 = fun _ => 1 := by
    funext v
    simp only [A]
    rw [uMat_one, Loc.LocFrame.M_one]
    exact (hπ v).2.2.1.1.1
  refine ⟨{
      Vpi := Tens.TV H
      piU := fun s => Tens.tensOp (A s)
      piU_rep := ?_
      Vloc := H
      piLoc := pl
      piLoc_type := hπ
      wfr := w
      wfr_on := fun v => (hw v).1
      wfr_perp := fun v => (hw v).2
      tensU := Tens.tensU
      tensU_inner := Tens.inner_tensU
      tensU_span := Tens.span_tensU
      tensU_equiv := fun s _ x => Tens.tensOp_tensU (A s) x }⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show Tens.tensOp (A 1) = 1
    rw [hA1]
    exact Tens.tensOp_one
  · intro s hs t ht
    show Tens.tensOp (A (s * t)) = Tens.tensOp (A s) * Tens.tensOp (A t)
    rw [← Tens.tensOp_mul]
    congr 1
    funext v
    simp only [A]
    rw [uMat_mul, (L v).M_mul (inUJ_uMat I s v) (hs v) (inUJ_uMat I t v) (ht v)]
    exact (hπ v).2.2.1.1.2 _ ((L v).M_inUJ (inUJ_uMat I s v) (hs v)) _
      ((L v).M_inUJ (inUJ_uMat I t v) (ht v))
  · intro s hs x y
    exact Tens.inner_tensOp (A s) (fun v u u' => inner_of_norm _
      (fun y => (hπ v).2.2.1.2.1 _ ((L v).M_inUJ (inUJ_uMat I s v) (hs v)) y) u u') x y
  · intro s hs
    show Tens.tensOp (A s) = 1
    have : A s = fun _ => 1 := by
      funext v
      simp only [A]
      rw [(L v).M_N (hs v)]
      exact (hπ v).2.2.1.1.1
    rw [this]
    exact Tens.tensOp_one
  · intro x
    refine Tens.continuousOn_tensOp A (Sinf I e z) (fun v y => ?_) x
    have hc : Continuous fun s : I.Ginf => (L v).M (uMat (s v)) := by
      apply continuous_pi
      intro a
      apply continuous_pi
      intro b
      simp only [Loc.LocFrame.M, hJ]
      exact continuous_const.dotProduct
        (continuous_const.matrix_mulVec ((cont_uMat I v).matrix_mulVec continuous_const))
    exact ((hπ v).2.2.1.2.2 y).comp hc.continuousOn
      (fun s hs => (L v).M_inUJ (inUJ_uMat I s v) (hs v))

end PI.ScPiBuildW.Asm
