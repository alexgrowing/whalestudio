import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailRest
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailSide
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSideRest
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailFurther
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailExtra
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherExtra
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPtZeroNeZero
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver mIdealOver)

theorem SegreRealise.proof (hB : SegreBase.Statement) (hT : SegreTwist.Statement) (hD : SegreDim.Statement)
    (hNf : SegreNef.Statement) (hNm : SegreNum.Statement) (hBd : BundleOfDeg.Statement)
    (hMD : ModelDimEq.Statement) (hMN : ModelNefEq.Statement) (hMNum : ModelNumEq.Statement) :
    SegreRealise.Statement := by
  classical
  intro F _ K _ _ ι _ Ω _ _ y d μs hy hd
  have : ∀ a, Nonempty (ι a) := fun a => ⟨(hy a).choose⟩
  have hcard : 0 < Fintype.card (∀ a, ι a) := Fintype.card_pos
  let N := Fintype.card (∀ a, ι a) - 1
  let eqv : (∀ a, ι a) ≃ Fin (N + 1) := Fintype.equivFinOfCardEq (by omega)
  have hbase : IndefiniteRowSideFullHecke.Kleiman2.IsModelWithBase F (segreJoin y) (Sum.inl ()) := (hB F K ι Ω y hy).1
  choose Ms hMs using fun j =>
    hBd F (Unit ⊕ K) _ Ω (segreJoin y) (Sum.inl ()) N eqv hbase (IndefiniteRowSideFullHecke.Kleiman2.pullDeg (μs j))
  have hsub : Kleiman.IsSubvar (IndefiniteRowSideFullHecke.Kleiman2.blockVec (segreJoin y) (Sum.inl ()) ∘ eqv.symm)
      (Kleiman.primeOf (S := F) (IndefiniteRowSideFullHecke.Kleiman2.blockVec (segreJoin y) (Sum.inl ()) ∘ eqv.symm)) d :=
    (hMD F _ _ Ω (segreJoin y) (Sum.inl ()) N eqv hbase d).2 (by rw [hD F K ι Ω y hy]; exact hd)
  refine ⟨N, eqv, IndefiniteRowSideFullHecke.Kleiman2.blockVec (segreJoin y) (Sum.inl ()) ∘ eqv.symm, Ms, fun i => ?_, hsub,
    fun j c => ?_, fun j => ?_, ?_⟩
  · show ∏ a, y ⟨a, eqv.symm (eqv i) a⟩ = ∏ a, y ⟨a, i a⟩
    rw [Equiv.symm_apply_apply]
  · exact (hMs j c).trans (hT F K ι Ω y hy (μs j) c)
  · exact (hMN F _ _ Ω (segreJoin y) (Sum.inl ()) N eqv hbase _ (Ms j) (hMs j)).trans (hNf F K ι Ω y hy (μs j))
  · exact (hMNum F _ _ Ω (segreJoin y) (Sum.inl ()) N eqv hbase d (fun j => IndefiniteRowSideFullHecke.Kleiman2.pullDeg (μs j)) Ms
      hMs hsub).trans (hNm F K ι Ω y hy d μs)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
