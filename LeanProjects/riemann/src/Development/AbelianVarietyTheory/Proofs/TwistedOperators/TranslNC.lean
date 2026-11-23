import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace GlobalTheory.HaarCoords

theorem transl_nC : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (UX D ρ)) (lB : Measure (Mx D ρ S₀.rank)) (lC : Measure (skewA D ρ)), μ.IsHaarMeasure → lB.IsAddHaarMeasure → lC.IsAddHaarMeasure → SFinite μ → SFinite lB → SFinite lC → ∀ c' : skewA D ρ, ∃ T : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) → UX D ρ × (Mx D ρ S₀.rank × skewA D ρ), MeasurePreserving T (μ.prod (lB.prod lC)) (μ.prod (lB.prod lC)) ∧ ∀ p, d.levi (T p).1.1 * (d.nB (T p).2.1 * d.nC (T p).2.2) = d.nC c' * (d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) := by
  intro D S S₀ ρ d μ lB lC _ _ hC _ _ _ c'
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ S₀.rank) := ⟨rfl⟩
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  obtain ⟨i1, -, i3, -⟩ := lattice_Mx D ρ ρ
  haveI : SecondCountableTopology (Mx D ρ ρ) := i3
  haveI : BorelSpace (skewA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (skewA D ρ) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : MeasurableAdd₂ (skewA D ρ) := inferInstance
  haveI : MeasurableAdd (skewA D ρ) := inferInstance
  let s : UX D ρ → skewA D ρ := fun u => skewConj (u⁻¹).1.1 c'
  have hinv : Continuous fun u : UX D ρ => (u⁻¹).1.1 := Units.continuous_coe_inv.comp continuous_subtype_val
  have hs : Continuous s := by
    refine Continuous.subtype_mk ?_ _
    exact (hinv.matrix_mul continuous_const).matrix_mul (continuous_adj.comp hinv)
  refine ⟨fun p => (p.1, (p.2.1, s p.1 + p.2.2)), ?_, ?_⟩
  · have hg : Measurable (Function.uncurry fun (u : UX D ρ) (q : Mx D ρ S₀.rank × skewA D ρ) => (q.1, s u + q.2)) :=
      measurable_snd.fst.prodMk ((hs.measurable.comp measurable_fst).add measurable_snd.snd)
    exact (MeasurePreserving.id μ).skew_product hg
      (Filter.Eventually.of_forall fun u => ((MeasurePreserving.id lB).prod (measurePreserving_add_left lC (s u))).map_eq)
  · rintro ⟨u, b, c⟩
    have h := d.levi_mul_nC c' (u⁻¹).1
    have hL : d.levi (u⁻¹).1 = (d.levi u.1)⁻¹ := by rw [Subgroup.coe_inv, map_inv]
    rw [hL] at h
    have h2 : d.nC c' * d.levi u.1 = d.levi u.1 * d.nC (s u) := by
      calc d.nC c' * d.levi u.1 = d.levi u.1 * ((d.levi u.1)⁻¹ * d.nC c') * d.levi u.1 := by rw [mul_inv_cancel_left]
        _ = d.levi u.1 * (d.nC (s u) * (d.levi u.1)⁻¹) * d.levi u.1 := by rw [h]
        _ = d.levi u.1 * d.nC (s u) := by rw [← mul_assoc (d.levi u.1), inv_mul_cancel_right]
    show d.levi u.1 * (d.nB b * d.nC (s u + c)) = d.nC c' * (d.levi u.1 * (d.nB b * d.nC c))
    rw [d.nC_add, ← mul_assoc (d.nC c'), h2, mul_assoc, ← mul_assoc (d.nC (s u)), d.nC_mul_nB, mul_assoc]

end GlobalTheory.HaarCoords
