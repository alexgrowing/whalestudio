import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKleimanNefF
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PModelGenericPoint
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTailRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

theorem KleimanNefF.kleimanNef_field_of_alt (hT : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.NefProductNonneg.Statement) :
    KH.KleimanNefFStatement := by
  classical
  intro F _ K _ ι _ I V n a hI hV hnef
  have : V.IsPrime := hV.1.1
  have hVd := HilbertSamuel.KleimanNefF.isMultiProjPrime_dvr hV.1
  set y := GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelGenericPoint.genPt (O := F) V
  have hy : KH.mIdealOver F y = V :=
    GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelGenericPoint.mIdealOver_genPt V hVd.multiHomog
  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hV.1.2.2 k
    exact ⟨i, (GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.ModelGenericPoint.genPt_ne_zero V _).2 hi⟩
  have hrel : FieldNumbers.relDim (KH.mIdealOver F y) = ((n : ℕ) : WithBot (WithTop ℤ)) := by
    rw [hy]
    exact (FieldNumbers.CutRegular.relDim_eq_natCast_iff V n).2 hV.2
  have hnef' : ∀ j, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.IsNef F y (a j) := by
    intro j W hW hle hW1
    rw [hy] at hle
    have hWF : IsProjVarF W 1 :=
      ⟨⟨hW.isPrime, (NumbersDVR.VocabMultiHomogIdeal.proof NumbersDVR.VocabMultiHomog.proof F K ι W).2
        hW.multiHomog, hW.relevant⟩, (FieldNumbers.CutRegular.relDim_eq_natCast_iff W 1).1 hW1⟩
    have h := hnef j W hWF hle
    rwa [HilbertSamuel.KleimanNefF.eq_intNum hI 1 W _ hWF] at h
  have h := hT F K ι _ y n a hnz hrel hnef'
  rw [hy] at h
  rw [HilbertSamuel.KleimanNefF.eq_intNum hI n V a hV]
  exact h

theorem NefProductNonneg.unfolding_matrix_of_form (hS : GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization.SegreRealise.Statement)
    (hA : GroundTheory.Heights₂.Heights.Kleiman.NefProductNonneg.Statement.{0, 0}) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2.NefProductNonneg.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y d μs hy hd hnef
  obtain ⟨N, _, x, Ms, _, hsub, _, hiff, hnum⟩ := hS F K ι Ω y d μs hy hd
  rw [← hnum]
  exact hA F Ω N x d _ Ms hsub fun j => (hiff j).2 (hnef j)

end

end GroundTheory.Heights₂.Heights.ForSecondHalf
