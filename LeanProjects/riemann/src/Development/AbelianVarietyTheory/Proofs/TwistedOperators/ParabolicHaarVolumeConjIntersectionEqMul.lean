import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic

open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

noncomputable section
namespace GlobalTheory.CosetVolProd

open MeasureTheory ValuativeRel Matrix Topology in

theorem _root_.GlobalTheory.CosetVolProd.volR_Cgrp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (J : Subgroup (GL (n ⊕ Fin c) k)) (h : GL (n ⊕ Fin c) k), IsOpen (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp J h) : Set (GL n k)) → ∀ m : Measure (GL n k), _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.volR ν m (_root_.GlobalTheory.StepData.Cgrp J h) = _root_.GlobalTheory.RootEx.volN ν n c 1 ((_root_.GlobalTheory.StepData.Cgrp J h).subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1)) * m (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp J h)) := by
  intro k _ _ _ _ _ _ ν _ n _ _ c J h hopen m
  set C := _root_.GlobalTheory.StepData.Cgrp J h
  set N := _root_.GlobalTheory.RootEx.N k n c 1
  haveI := _root_.GlobalTheory.RootEx.VolN.isHaarMeasure_volN ν (n := n) (c := c) 1
  have key : ∀ g : GL n k, _root_.GlobalTheory.RootEx.volN ν n c 1
      {u : N | _root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) ∈ C}
      = (_root_.GlobalTheory.StepData.prX C : Set (GL n k)).indicator
          (fun _ => _root_.GlobalTheory.RootEx.volN ν n c 1 (C.subgroupOf N)) g := by
    intro g
    by_cases hg : g ∈ _root_.GlobalTheory.StepData.prX C
    · rw [Set.indicator_of_mem hg]
      obtain ⟨u₀, hu₀, hC⟩ := (_root_.GlobalTheory.StepData.mem_prX).1 hg
      have hv : (_root_.GlobalTheory.RootEx.embX c g)⁻¹ * u₀ * _root_.GlobalTheory.RootEx.embX c g ∈ N :=
        _root_.GlobalTheory.RootEx.Model.conj_mem hu₀ g
      set v : N := ⟨_, hv⟩
      have hset : {u : N | _root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) ∈ C}
          = (fun w => v⁻¹ * w) ⁻¹' (C.subgroupOf N : Set N) := by
        ext u
        show _ ∈ C ↔ ((v⁻¹ * u : N) : GL (n ⊕ Fin c) k) ∈ C
        have e : _root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k)
            = (u₀ * _root_.GlobalTheory.RootEx.embX c g) *
              (((_root_.GlobalTheory.RootEx.embX c g)⁻¹ * u₀ * _root_.GlobalTheory.RootEx.embX c g)⁻¹
                * u) := by group
        rw [e, C.mul_mem_cancel_left hC]
        rfl
      rw [hset, measure_preimage_mul]
    · rw [Set.indicator_of_notMem hg]
      have hset : {u : N | _root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) ∈ C} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.2 fun u hu => ?_
        apply hg
        refine (_root_.GlobalTheory.StepData.mem_prX).2 ⟨_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) * (_root_.GlobalTheory.RootEx.embX c g)⁻¹,
          _root_.GlobalTheory.RootEx.Radical.conj_mem g u.2, ?_⟩
        rwa [inv_mul_cancel_right]
      rw [hset, measure_empty]
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.volR
  refine (lintegral_congr key).trans ?_
  rw [lintegral_indicator_const hopen.measurableSet]

end GlobalTheory.CosetVolProd
