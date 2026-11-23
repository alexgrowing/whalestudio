import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.MsetOfClosed
import Formalism.SharpRestriction.CuspSpanNormBounds.SpanMemOfImage

open MeasureTheory Matrix
open scoped ENNReal

noncomputable section

namespace Formalism.MainNotions.S.Pv.AmpDDPf.CC

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

theorem sfin_muN (L : LocBessel k r) : SFinite L.μN := by
  exact Formalism.MainNotions.FrameBoundFromBesselTorus.sFinite_haarLie _ _

theorem pairMeas_bad (L : LocBessel k r) : pairMeas L {x | ¬ Good L x} = 0 := by
  haveI : SFinite L.μN := sfin_muN L
  haveI : SigmaFinite L.μW := L.hμW.1.1
  haveI : SigmaFinite L.μW' := L.hμW'.1.1
  have hN : L.μN {x | Matrix.of x ∉ Nset k r} = 0 := by
    obtain ⟨c, -, hform⟩ := Formalism.MainNotions.BridgeCSB.haarLie_N_eq (k := k) (r := r)
    have h1 := (Formalism.MainNotions.BridgeCSB.haarLieN k r 1 one_ne_zero ENNReal.one_ne_top).2.2.1
    rw [hform, one_smul] at h1
    rw [LocBessel.μN, hform, Measure.smul_apply, h1, smul_zero]
  have hW : L.μW {x | Matrix.of x ∉ UWset k r L.z} = 0 := L.hμW.1.2.2.1
  have hW' : L.μW' {x | Matrix.of x ∉ UWset k r L.z'} = 0 := L.hμW'.1.2.2.1
  have hsub : {x : PairSp k r | ¬ Good L x} ⊆
      ((Set.univ ×ˢ {x | Matrix.of x ∉ Nset k r}) ×ˢ Set.univ ∪
        Set.univ ×ˢ (Set.univ ×ˢ {x | Matrix.of x ∉ Nset k r})) ∪
      (({x | Matrix.of x ∉ UWset k r L.z} ×ˢ Set.univ) ×ˢ Set.univ ∪
        Set.univ ×ˢ ({x | Matrix.of x ∉ UWset k r L.z'} ×ˢ Set.univ)) := by
    intro x hx
    simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, Set.mem_setOf_eq, true_and, and_true]
    by_contra hc
    push_neg at hc
    exact hx (by unfold Good; exact ⟨hc.1.1, hc.1.2, hc.2.1, hc.2.2⟩)
  refine measure_mono_null hsub ?_
  unfold pairMeas
  refine measure_union_null (measure_union_null ?_ ?_) (measure_union_null ?_ ?_) <;>
    simp only [Measure.prod_prod, hN, hW, hW', mul_zero, zero_mul]

theorem nu_bad (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {μR : Measure (Mt k r)} (hR0 : μR ≠ 0) (hRc : μR {x | Matrix.of x ∉ RStab k r γ} = 0)
    {ν : Measure (PairSp k r)} (hQ : IsOrbQuot L γ μR ν) : ν {x | ¬ Good L x} = 0 := by
  have hm : MeasurableSet {x : PairSp k r | ¬ Good L x} := (good_mset L).compl
  have h := hQ ({x : PairSp k r | ¬ Good L x}.indicator 1) (measurable_one.indicator hm)
  rw [lintegral_indicator_one hm, pairMeas_bad] at h
  have hin : ∀ x, ∫⁻ a, {x : PairSp k r | ¬ Good L x}.indicator 1 (stabAct γ (Matrix.of a) x) ∂μR =
      μR Set.univ * {x : PairSp k r | ¬ Good L x}.indicator 1 x := by
    intro x
    have hst : ∀ᵐ a ∂μR, Matrix.of a ∈ RStab k r γ := by
      rw [ae_iff]
      exact hRc
    have hae : ∀ᵐ a ∂μR, {x : PairSp k r | ¬ Good L x}.indicator (1 : PairSp k r → ℝ≥0∞)
        (stabAct γ (Matrix.of a) x) = {x : PairSp k r | ¬ Good L x}.indicator 1 x := by
      filter_upwards [hst] with a ha
      classical
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply, good_stabAct L ha x]
    rw [lintegral_congr_ae hae, lintegral_const, mul_comm]
  simp_rw [hin] at h
  rw [lintegral_const_mul _ (measurable_one.indicator hm), lintegral_indicator_one hm] at h
  have hR : μR Set.univ ≠ 0 := by rwa [Ne, Measure.measure_univ_eq_zero]
  exact (mul_eq_zero.1 h.symm).resolve_left hR

end Formalism.MainNotions.S.Pv.AmpDDPf.CC
