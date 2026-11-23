import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagRatioFieldEq
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PBirationalRatioClosure
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFnFieldTrdeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem HodgeFlagRatioTrdeg.proof (h₂ : HodgeFlagRatioFieldEq.Statement) (h₃ : HodgeFlagMinorTrdeg.Statement) :
    HodgeFlagRatioTrdeg.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B c hc
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  let cX : ∀ k, ι k := fun k => c (Sum.inl k)
  have hyX : ∀ p : Σ k, ι k, Pl.flagGenericPoint B ⟨Sum.inl p.1, p.2⟩ = algebraMap Ω Pl.ΩY (D.y p) :=
    fun p => PlueckerData.ofΩ_eq Pl _
  have hcX : ∀ k, D.y ⟨k, cX k⟩ ≠ 0 := fun k h => hc (Sum.inl k) (by
    rw [hyX ⟨k, cX k⟩, h, map_zero])

  have hbase : Set.range (algebraMap Ω Pl.ΩY) ⊆ Subfield.closure (coneRatios (Pl.flagGenericPoint B) c) := by
    have hle : Subfield.map (algebraMap Ω Pl.ΩY) (Subfield.closure (coneRatios D.y cX)) ≤
        Subfield.closure (coneRatios (Pl.flagGenericPoint B) c) := by
      rw [Subfield.map_le_iff_le_comap, Subfield.closure_le]
      rintro _ ⟨p, rfl⟩
      refine Subfield.subset_closure ⟨⟨Sum.inl p.1, p.2⟩, ?_⟩
      show Pl.flagGenericPoint B ⟨Sum.inl p.1, p.2⟩ / Pl.flagGenericPoint B ⟨Sum.inl p.1, cX p.1⟩ =
        algebraMap Ω Pl.ΩY (D.y p / D.y ⟨p.1, cX p.1⟩)
      rw [map_div₀, hyX p, hyX ⟨p.1, cX p.1⟩]
    rintro _ ⟨x, rfl⟩
    refine hle ⟨x, ?_, rfl⟩
    rw [BirationalRatioClosure.full K ι Ω D.y cX D.birational hcX]
    trivial
  set Ef := IntermediateField.adjoin Ω (coneRatios (Pl.flagGenericPoint B) c)
  have hsub : Ef.toSubfield = Subfield.closure (coneRatios (Pl.flagGenericPoint B) c) := by
    rw [IntermediateField.adjoin_toSubfield]
    exact le_antisymm (Subfield.closure_le.2 (Set.union_subset hbase Subfield.subset_closure))
      (Subfield.closure_mono Set.subset_union_right)
  have e : Subfield.closure (coneRatios (Pl.flagGenericPoint B) c) ≃+* Ef :=
    (RingEquiv.subfieldCongr hsub).symm.trans (RingEquiv.refl Ef)
  have hE : Algebra.trdeg ℤ (Subfield.closure (coneRatios (Pl.flagGenericPoint B) c)) = Algebra.trdeg ℤ Ef :=
    (AlgEquiv.ofRingEquiv (f := e) fun x => by rw [eq_intCast, eq_intCast, map_intCast]).trdeg_eq
  rw [hE]
  have : FaithfulSMul ℤ Ω := (faithfulSMul_iff_algebraMap_injective ℤ Ω).mpr Int.cast_injective
  have : FaithfulSMul Ω Ef := (faithfulSMul_iff_algebraMap_injective Ω Ef).mpr (algebraMap Ω Ef).injective
  rw [← trdeg_add_eq ℤ Ω (A := Ef), FnFieldTrdeg.full K ι Ω D.y D.n D.birational D.arith,
    ← (IntermediateField.equivOfEq (h₂ II Ψ K ι Ω E D Pl H B c hc)).symm.trdeg_eq,
    h₃ Ω Ψ D.N D.j D.j_le_N]
  rw [← Nat.cast_add]
  rfl

end GroundTheory.Heights₂.Heights.LowerBoundFree
