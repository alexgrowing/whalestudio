import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsBirationalRatioClosure
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPlueckerRatioFieldEq
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagRatioTrdeg
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFnFieldTrdeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem PlueckerRatioTrdeg.proof (h₁ : BirationalRatioClosure.Statement) (h₂ : PlueckerRatioFieldEq.Statement)
    (h₃ : FlagRatioTrdeg.Statement) : PlueckerRatioTrdeg.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl c hc
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  let cX : ∀ k, ι k := fun k => c (Sum.inl k)
  have hyX : ∀ p : Σ k, ι k, Pl.yY ⟨Sum.inl p.1, p.2⟩ = algebraMap Ω Pl.ΩY (D.y p) :=
    fun p => (PlueckerData.yY_inl Pl p.1 p.2).trans (PlueckerData.ofΩ_eq Pl _)
  have hcX : ∀ k, D.y ⟨k, cX k⟩ ≠ 0 := fun k h => hc (Sum.inl k) (by
    rw [hyX ⟨k, cX k⟩, h, map_zero])

  have hbase : Set.range (algebraMap Ω Pl.ΩY) ⊆ Subfield.closure (coneRatios Pl.yY c) := by
    have hle : Subfield.map (algebraMap Ω Pl.ΩY) (Subfield.closure (coneRatios D.y cX)) ≤
        Subfield.closure (coneRatios Pl.yY c) := by
      rw [Subfield.map_le_iff_le_comap, Subfield.closure_le]
      rintro _ ⟨p, rfl⟩
      refine Subfield.subset_closure ⟨⟨Sum.inl p.1, p.2⟩, ?_⟩
      show Pl.yY ⟨Sum.inl p.1, p.2⟩ / Pl.yY ⟨Sum.inl p.1, cX p.1⟩ = algebraMap Ω Pl.ΩY (D.y p / D.y ⟨p.1, cX p.1⟩)
      rw [map_div₀, hyX p, hyX ⟨p.1, cX p.1⟩]
    rintro _ ⟨x, rfl⟩
    refine hle ⟨x, ?_, rfl⟩
    rw [h₁ K ι Ω D.y cX D.birational hcX]
    trivial
  set Ef := IntermediateField.adjoin Ω (coneRatios Pl.yY c)
  have hsub : Ef.toSubfield = Subfield.closure (coneRatios Pl.yY c) := by
    rw [IntermediateField.adjoin_toSubfield]
    exact le_antisymm (Subfield.closure_le.2 (Set.union_subset hbase Subfield.subset_closure))
      (Subfield.closure_mono Set.subset_union_right)
  have e : Subfield.closure (coneRatios Pl.yY c) ≃+* Ef :=
    (RingEquiv.subfieldCongr hsub).symm.trans (RingEquiv.refl Ef)
  have hE : Algebra.trdeg ℤ (Subfield.closure (coneRatios Pl.yY c)) = Algebra.trdeg ℤ Ef :=
    (AlgEquiv.ofRingEquiv (f := e) fun x => by rw [eq_intCast, eq_intCast, map_intCast]).trdeg_eq
  rw [hE]
  have : FaithfulSMul ℤ Ω := (faithfulSMul_iff_algebraMap_injective ℤ Ω).mpr Int.cast_injective
  have : FaithfulSMul Ω Ef := (faithfulSMul_iff_algebraMap_injective Ω Ef).mpr (algebraMap Ω Ef).injective
  rw [← trdeg_add_eq ℤ Ω (A := Ef), FnFieldTrdeg.full K ι Ω D.y D.n D.birational D.arith,
    ← (IntermediateField.equivOfEq (h₂ II Ψ K ι Ω E D Pl c hc)).symm.trdeg_eq, h₃ Ω Ψ D.N]
  rw [← Nat.cast_add]
  rfl

end GroundTheory.Heights₂.Heights.LowerBoundFree
