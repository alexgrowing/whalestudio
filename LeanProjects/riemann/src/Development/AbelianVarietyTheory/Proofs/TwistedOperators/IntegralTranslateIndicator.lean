import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QuotientIntegralParabolicUnfolding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

namespace GlobalTheory.StepAvg

open MeasureTheory ValuativeRel Matrix Topology in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} in
private lemma measurableSet_Cgrp_of_isCO {J : Subgroup (GL (n ⊕ Fin c) k)}
    (hJ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO J) (h : GL (n ⊕ Fin c) k) :
    MeasurableSet (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)) := by
  have hJ' : IsOpen (J : Set (GL (n ⊕ Fin c) k)) ∧ IsCompact (J : Set (GL (n ⊕ Fin c) k)) := hJ
  have hset : (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)) =
      (_root_.GlobalTheory.RootEx.R k n c 1 : Set (GL (n ⊕ Fin c) k)) ∩
        (fun x => h⁻¹ * x * h) ⁻¹' (J : Set (GL (n ⊕ Fin c) k)) := by
    ext x
    exact _root_.GlobalTheory.StepData.mem_Cgrp
  have hopen : IsOpen ((fun x : GL (n ⊕ Fin c) k => h⁻¹ * x * h) ⁻¹' (J : Set (GL (n ⊕ Fin c) k))) :=
    hJ'.1.preimage (by fun_prop)
  rw [hset]
  exact (_root_.GlobalTheory.RootEx.VolN.isClosed_R 1).measurableSet.inter hopen.measurableSet

open MeasureTheory ValuativeRel Matrix Topology in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} in
private lemma integral_indicator_embed_mul_unipotent_lemma (ν : Measure k) [ν.IsAddHaarMeasure]
    {J : Subgroup (GL (n ⊕ Fin c) k)} (hJ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO J) (h : GL (n ⊕ Fin c) k)
    (x : GL n k) :
    ∫ u : _root_.GlobalTheory.RootEx.N k n c 1,
        (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ))
          (_root_.GlobalTheory.RootEx.embX c x * (u : GL (n ⊕ Fin c) k))
        ∂(_root_.GlobalTheory.RootEx.volN ν n c 1) =
      (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp J h) : Set (GL n k)).indicator
        (fun _ => (((_root_.GlobalTheory.RootEx.volN ν n c 1)
          ((_root_.GlobalTheory.StepData.Cgrp J h).subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1))).toReal
            : ℂ)) x := by
  haveI := _root_.GlobalTheory.RootEx.VolN.isHaarMeasure_volN (c := c) (n := n) ν 1
  set C := _root_.GlobalTheory.StepData.Cgrp J h
  set E := _root_.GlobalTheory.RootEx.embX (k := k) (n := n) c
  by_cases hx : x ∈ _root_.GlobalTheory.StepData.prX C
  · obtain ⟨u₁, hu₁N, hu₁C⟩ := _root_.GlobalTheory.StepData.mem_prX.mp hx
    let w : _root_.GlobalTheory.RootEx.N k n c 1 :=
      ⟨E x⁻¹ * u₁⁻¹ * (E x⁻¹)⁻¹, _root_.GlobalTheory.RootEx.Radical.conj_mem x⁻¹
        (Subgroup.inv_mem _ hu₁N)⟩
    have key : ∀ u : _root_.GlobalTheory.RootEx.N k n c 1,
        (C : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ)) (E x * (u : GL (n ⊕ Fin c) k)) =
          ((C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1) :
            Set (_root_.GlobalTheory.RootEx.N k n c 1))).indicator (fun _ => (1 : ℂ)) (w * u) := by
      intro u
      have hwu : ((w * u : _root_.GlobalTheory.RootEx.N k n c 1) : GL (n ⊕ Fin c) k) =
          (u₁ * E x)⁻¹ * (E x * u) := by
        simp only [w, Subgroup.coe_mul, map_inv, inv_inv, _root_.mul_inv_rev, mul_assoc]
      have hiff : E x * (u : GL (n ⊕ Fin c) k) ∈ C ↔
          w * u ∈ C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1) := by
        rw [Subgroup.mem_subgroupOf, hwu, Subgroup.mul_mem_cancel_left _ (Subgroup.inv_mem _ hu₁C)]
      by_cases hu : E x * (u : GL (n ⊕ Fin c) k) ∈ C
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (show w * u ∈ _ from hiff.mp hu)]
      · rw [Set.indicator_of_notMem hu,
          Set.indicator_of_notMem (show w * u ∉ ((C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1) :
            Set (_root_.GlobalTheory.RootEx.N k n c 1))) from fun h' => hu (hiff.mpr h'))]
    have hmeas : MeasurableSet ((C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1) :
        Set (_root_.GlobalTheory.RootEx.N k n c 1))) :=
      measurable_subtype_coe (measurableSet_Cgrp_of_isCO hJ h)
    simp_rw [key]
    rw [integral_mul_left_eq_self (fun u => ((C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1) :
        Set (_root_.GlobalTheory.RootEx.N k n c 1))).indicator (fun _ => (1 : ℂ)) u) w,
      integral_indicator_const _ hmeas, Set.indicator_of_mem hx, measureReal_def, Complex.real_smul,
      mul_one]
  · rw [Set.indicator_of_notMem hx]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun u => ?_)
    refine Set.indicator_of_notMem (fun hu => hx ?_) _
    refine _root_.GlobalTheory.StepData.mem_prX.mpr ⟨E x * u * (E x)⁻¹,
      _root_.GlobalTheory.RootEx.Radical.conj_mem x u.2, ?_⟩
    convert hu using 1
    simp [E]

open MeasureTheory ValuativeRel Matrix Topology in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} in

theorem _root_.GlobalTheory.StepAvg.integral_translate_indicator : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ), 1 ≤ c → ∀ (J : Subgroup (GL (n ⊕ Fin c) k)), _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO J → ∀ (h : GL (n ⊕ Fin c) k), _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp J h)) → ∀ (m : Measure (GL n k)) [m.IsHaarMeasure], ∀ u₀ ∈ _root_.GlobalTheory.RootEx.N k n c 1, ∀ g₀ : GL n k, ∫ g, (∫ u : _root_.GlobalTheory.RootEx.N k n c 1, (_root_.GlobalTheory.StepData.Cgrp J h : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ)) (_root_.GlobalTheory.RootEx.embX c g * (u : GL (n ⊕ Fin c) k) * (u₀ * _root_.GlobalTheory.RootEx.embX c g₀)) ∂(_root_.GlobalTheory.RootEx.volN ν n c 1)) ∂m = ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.deltaR c g₀ * ((_root_.GlobalTheory.RootEx.volN ν n c 1 ((_root_.GlobalTheory.StepData.Cgrp J h).subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1))).toReal * (m (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp J h))).toReal) : ℝ) : ℂ) := by
  intro k _ _ _ _ _ _ ν _ n _ _ c hc J hJ h hpr m _ u₀ hu₀ g₀
  haveI := _root_.GlobalTheory.RootEx.VolN.isMulRightInvariant_volN (c := c) (n := n) ν 1
  haveI := _root_.GlobalTheory.SplitFlip.isMulRightInvariant_of_haar (k := k) m
  set C := _root_.GlobalTheory.StepData.Cgrp J h
  set E := _root_.GlobalTheory.RootEx.embX (k := k) (n := n) c
  set V : ℂ := (((_root_.GlobalTheory.RootEx.volN ν n c 1)
    (C.subgroupOf (_root_.GlobalTheory.RootEx.N k n c 1))).toReal : ℂ)
  have hinv : _root_.GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det g₀⁻¹) =
      (_root_.GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det g₀))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← _root_.GlobalTheory.SplitWeil.nabs_mul, ← map_mul, inv_mul_cancel, map_one,
      _root_.GlobalTheory.SplitWeil.nabs_one]
  have hpos := _root_.GlobalTheory.SplitWeil.nabs_pos k (Matrix.GeneralLinearGroup.det g₀)
  have ha0 : _root_.GlobalTheory.SplitWeil.nabs k (Matrix.GeneralLinearGroup.det g₀⁻¹) ^
      (-((c : ℝ) + 1 - 2 * ((1 : ℕ) : ℝ))) = _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.deltaR c g₀ := by
    rw [hinv, Real.inv_rpow hpos.le, Real.rpow_neg hpos.le, inv_inv,
      show ((c : ℝ) + 1 - 2 * ((1 : ℕ) : ℝ)) = (((c : ℤ) - 1 : ℤ) : ℝ) by push_cast; ring,
      Real.rpow_intCast]
    rfl
  have inner : ∀ g : GL n k,
      ∫ u : _root_.GlobalTheory.RootEx.N k n c 1,
          (C : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ))
            (E g * (u : GL (n ⊕ Fin c) k) * (u₀ * E g₀)) ∂(_root_.GlobalTheory.RootEx.volN ν n c 1) =
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.deltaR c g₀ •
          (_root_.GlobalTheory.StepData.prX C : Set (GL n k)).indicator (fun _ => V) (g * g₀) := by
    intro g
    have e1 : ∀ u : _root_.GlobalTheory.RootEx.N k n c 1,
        E g * (u : GL (n ⊕ Fin c) k) * (u₀ * E g₀) =
          E (g * g₀) * (E g₀⁻¹ * ((u * ⟨u₀, hu₀⟩ : _root_.GlobalTheory.RootEx.N k n c 1) :
            GL (n ⊕ Fin c) k) * (E g₀⁻¹)⁻¹) := by
      intro u
      simp only [map_mul, map_inv, inv_inv, Subgroup.coe_mul, mul_assoc, mul_inv_cancel_left]
    simp_rw [e1]
    rw [integral_mul_right_eq_self (fun u : _root_.GlobalTheory.RootEx.N k n c 1 =>
        (C : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ))
          (E (g * g₀) * (E g₀⁻¹ * (u : GL (n ⊕ Fin c) k) * (E g₀⁻¹)⁻¹))) ⟨u₀, hu₀⟩,
      _root_.GlobalTheory.RootEx.VolN.integral_conj_volN ν le_rfl hc g₀⁻¹
        (fun y => (C : Set (GL (n ⊕ Fin c) k)).indicator (fun _ => (1 : ℂ)) (E (g * g₀) * y)),
      integral_indicator_embed_mul_unipotent_lemma ν hJ h (g * g₀), ha0]
    all_goals simp only [C, V]
  have hpr' : IsOpen (_root_.GlobalTheory.StepData.prX C : Set (GL n k)) ∧
      IsCompact (_root_.GlobalTheory.StepData.prX C : Set (GL n k)) := hpr
  have hborel := (_root_.GlobalTheory.SplitWeil.volGL_haar k n ν).1
  have hmeas : MeasurableSet (_root_.GlobalTheory.StepData.prX C : Set (GL n k)) := hpr'.1.measurableSet

  simp_rw [inner]
  rw [integral_smul, integral_mul_right_eq_self (fun g : GL n k =>
      (_root_.GlobalTheory.StepData.prX C : Set (GL n k)).indicator (fun _ => V) g) g₀,
    integral_indicator_const _ hmeas, measureReal_def]
  simp only [V, Complex.real_smul]
  push_cast
  ring

end GlobalTheory.StepAvg
