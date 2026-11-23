import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelIndexMulMeasure
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

namespace GlobalTheory.OpenVolIndex

theorem measure_toReal_inv_eq_relIndex : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (H L : Subgroup G), H ≤ L → IsOpen (H : Set G) → IsCompact (L : Set G) → μ (L : Set G) = 1 → (μ (H : Set G)).toReal⁻¹ = (H.relIndex L : ℝ) := by
  intro G _ _ _ _ _ μ _ H L hHL hH hL hμL
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hHo : IsOpen ((H.subgroupOf L : Subgroup L) : Set L) :=
    hH.preimage continuous_subtype_val
  haveI : Finite (L ⧸ H.subgroupOf L) := Subgroup.quotient_finite_of_isOpen _ hHo
  haveI : (H.subgroupOf L).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have key := GlobalTheory.BaseModule.relIndex_mul_measure' H L hHL hH.measurableSet μ
  rw [hμL] at key
  have htop : μ (H : Set G) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hμL]; exact ENNReal.one_ne_top) (measure_mono hHL)
  have hr : (H.relIndex L : ℝ) * (μ (H : Set G)).toReal = 1 := by
    have := congrArg ENNReal.toReal key
    simpa [ENNReal.toReal_mul] using this
  exact (eq_inv_of_mul_eq_one_left hr).symm

end GlobalTheory.OpenVolIndex
