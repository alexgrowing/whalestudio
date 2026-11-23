import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOfMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankCoinvariantInducedIso
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil
open scoped Matrix

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.FullRankCoinv.LeftScale

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem indicator_one_mem_fullRk {n d : ℕ} {U : Set (Matrix (Fin n) (Fin d) k)} (hU : IsClopen U) (hc : IsCompact U)
    (hr : ∀ Y ∈ U, Y.rank = n) : U.indicator (fun _ => (1 : ℂ)) ∈ fullRk k n d := by
  refine ⟨⟨?_, ?_⟩, fun Y hY => Set.indicator_of_notMem (fun h => hY (hr Y h)) _⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ U
    · filter_upwards [hU.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    · filter_upwards [hU.compl.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · exact HasCompactSupport.intro' hc hU.isClosed fun x hx => Set.indicator_of_notMem hx _

theorem matInt_indicator_ne_zero [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] {n d : ℕ}
    {U : Set (Matrix (Fin n) (Fin d) k)} (hU : IsOpen U) (hc : IsCompact U) (hne : U.Nonempty) :
    matInt ν (U.indicator (fun _ => (1 : ℂ))) ≠ 0 := by
  haveI := SplitWeil.secondCountable k
  haveI := SplitWeil.t2Space k
  let e : (Fin n × Fin d → k) ≃ₜ Matrix (Fin n) (Fin d) k :=
    { toEquiv := Equiv.curry _ _ _
      continuous_toFun := continuous_pi fun i => continuous_pi fun j => continuous_apply (i, j)
      continuous_invFun := continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1) }
  have ho : IsOpen (e ⁻¹' U) := hU.preimage e.continuous
  have hcp : IsCompact (e ⁻¹' U) := e.isCompact_preimage.2 hc
  have hn : (e ⁻¹' U).Nonempty := hne.preimage e.surjective
  have h1 : matInt ν (U.indicator (fun _ => (1 : ℂ))) =
      ∫ v, (e ⁻¹' U).indicator (fun _ => (1 : ℂ)) v ∂(Measure.pi fun _ => ν) := rfl
  rw [h1, integral_indicator_const _ ho.measurableSet]
  have hpos := ho.measure_pos (Measure.pi fun _ : Fin n × Fin d => ν) hn
  have hlt := hcp.measure_lt_top (μ := Measure.pi fun _ : Fin n × Fin d => ν)
  simp [Measure.real, ENNReal.toReal_eq_zero_iff, hpos.ne', hlt.ne]

theorem matInt_smul [MeasurableSpace k] (ν : Measure k) {n d : ℕ} (c : ℂ) (φ : Matrix (Fin n) (Fin d) k → ℂ) :
    matInt ν (c • φ) = c * matInt ν φ := by
  unfold matInt
  simp only [Pi.smul_apply, smul_eq_mul]
  exact integral_const_mul _ _

def stabKO {n d : ℕ} (φ : Matrix (Fin n) (Fin d) k → ℂ) : Subgroup (KO k (Fin d)) where
  carrier := {κ | ∀ Y : Matrix (Fin n) (Fin d) k, φ (Y * κ.val.val) = φ Y}
  one_mem' := fun Y => by simp
  mul_mem' := fun {a b} ha hb Y => by
    rw [Subgroup.coe_mul, Units.val_mul, ← Matrix.mul_assoc, hb, ha]
  inv_mem' := fun {a} ha Y => by
    have := ha (Y * (a⁻¹).val.val)
    rw [Matrix.mul_assoc, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel] at this
    simpa using this.symm

theorem finiteIndex_stabKO {n d : ℕ} {φ : Matrix (Fin n) (Fin d) k → ℂ}
    (hφ : φ ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin d) k)) : (stabKO φ).FiniteIndex := by
  obtain ⟨U, hU, hinv⟩ := sb_right_invariant k n d φ hφ
  haveI : CompactSpace (KO k (Fin d)) := isCompact_iff_compactSpace.mp (isCompact_KO (k := k) (n := Fin d))
  have ho : IsOpen (stabKO φ : Set (KO k (Fin d))) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    exact Filter.mem_of_superset (continuous_subtype_val.continuousAt.preimage_mem_nhds (by simpa using hU))
      fun u hu => hinv _ hu
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  exact Subgroup.finiteIndex_of_finite_quotient

end GlobalTheory.FullRankCoinv.LeftScale
