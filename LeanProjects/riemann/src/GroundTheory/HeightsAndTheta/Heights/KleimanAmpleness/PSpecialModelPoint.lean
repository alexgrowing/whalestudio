import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLastBis
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisSide
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsBisTail
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsFurtherLast
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver mConeMapOver chartRingOver)

theorem SpecialModelPoint.proof (hgen : BlockGenOfModel.Statement) (htr : BlockGenTransfer.Statement)
    (hmod : ModelOfBlockGen.Statement) : SpecialModelPoint.Statement := by
  intro O _ _ _ Ω _ _ _ _ K _ _ ι _ y k₀ hy Ω' _ _ y' hy' hle
  let _ : Algebra O Ω' :=
    ((algebraMap (IsLocalRing.ResidueField O) Ω').comp (IsLocalRing.residue O)).toAlgebra
  have : IsScalarTower O (IsLocalRing.ResidueField O) Ω' :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hle' : mIdealOver O y ≤ mIdealOver O y' := by
    intro f hf
    have h1 := hle (Ideal.mem_map_of_mem (MvPolynomial.map (IsLocalRing.residue O)) hf)
    rw [mIdealOver, RingHom.mem_ker] at h1 ⊢
    rw [← h1, mConeMapOver, mConeMapOver]
    exact (MvPolynomial.aeval_map_algebraMap (IsLocalRing.ResidueField O) _ f).symm
  have hb : BlockGen O y' k₀ := htr O K ι Ω y k₀ (hgen O K ι Ω y k₀ hy) Ω' y' hy' hle'
  refine hmod _ K ι Ω' y' k₀ hy' ?_
  intro j hj k
  obtain ⟨w, hw, hsum⟩ := hb j hj k
  refine ⟨w, fun a b => ?_, hsum⟩
  have hsub : chartRingOver O (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀)) (fun _ => j) ≤
      (chartRingOver (IsLocalRing.ResidueField O) (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y' k₀))
        (fun _ => j)).restrictScalars O :=
    Algebra.adjoin_le Algebra.subset_adjoin
  exact hsub (hw a b)

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
