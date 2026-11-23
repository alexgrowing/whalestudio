import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.ZsCovMeas
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.UnfoldingVolume
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.VolumeClassRepresentatives.IwasawaCovolume
import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
import Formalism.SharpRestriction.CuspSpanNormBounds.SGauge

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
  Formalism.MainNotions.LeviCoordinates
open scoped ENNReal Pointwise

namespace Formalism.L2.S.S7.ZsCovSum

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem muA_FD (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (ys : Finset I.Gf)
    (hys : Formalism.MainNotions.FundamentalDomainUnfolding.ClassReps I ys) (Dy : I.Gf → Set I.Ginf)
    (hD : ∀ y ∈ ys, Formalism.MainNotions.FundamentalDomainUnfolding.IsFundInf I y (Formalism.MainNotions.FundamentalDomainUnfolding.muInf I) (Dy y)) :
    I.muA μf (UnfoldingVolume.FD I ys Dy) = μf I.Kset * ∑ y ∈ ys, Formalism.MainNotions.FundamentalDomainUnfolding.muInf I (Dy y) := by
  rw [UnfoldingVolume.FD, measure_biUnion_finset]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [UnfoldingVolume.muA_eq, Measure.prod_prod, UnfoldingVolume.Ky_measure, mul_comm]
  · intro y hy y' hy' hne
    refine Set.disjoint_left.2 fun p hp hp' => hne ?_
    have hk : y⁻¹ * p.2 ∈ I.Kset := hp.2
    have hk' : y'⁻¹ * p.2 ∈ I.Kset := hp'.2
    refine hys.2 y hy y' hy' ⟨1, rrg_one_mem I, (y⁻¹ * p.2) * (y'⁻¹ * p.2)⁻¹,
      UnfoldingVolume.kmul I hk (UnfoldingVolume.kinv I hk'), ?_⟩
    show y' = 1 * y * ((y⁻¹ * p.2) * (y'⁻¹ * p.2)⁻¹)
    group
  · intro y hy
    exact (hD y hy).1.prod (UnfoldingVolume.Ky_meas I y)

theorem FD_meas (I : AutInst) (ys : Finset I.Gf) (Dy : I.Gf → Set I.Ginf)
    (hD : ∀ y ∈ ys, Formalism.MainNotions.FundamentalDomainUnfolding.IsFundInf I y (Formalism.MainNotions.FundamentalDomainUnfolding.muInf I) (Dy y)) :
    MeasurableSet (UnfoldingVolume.FD I ys Dy) :=
  Finset.measurableSet_biUnion ys fun y hy => (hD y hy).1.prod (UnfoldingVolume.Ky_meas I y)

theorem blockEquiv {n P Q : ℕ} (ε : Fin n → Bool) (hP : (Finset.univ.filter fun i => ε i = true).card = P)
    (hn : P + Q = n) :
    ∃ e : Fin P ⊕ Fin Q ≃ Fin n, (∀ i, ε (e (Sum.inl i)) = true) ∧ ∀ j, ε (e (Sum.inr j)) = false := by
  have hT : Fintype.card {i // ε i = true} = P := by rw [Fintype.card_subtype]; exact hP
  have hF : Fintype.card {i // ¬ ε i = true} = Q := by
    rw [Fintype.card_subtype_compl, hT, Fintype.card_fin]; omega
  let eT : Fin P ≃ {i // ε i = true} := (Fintype.equivFinOfCardEq hT).symm
  let eF : Fin Q ≃ {i // ¬ ε i = true} := (Fintype.equivFinOfCardEq hF).symm
  refine ⟨(Equiv.sumCongr eT eF).trans (Equiv.sumCompl fun i => ε i = true), fun i => ?_, fun j => ?_⟩
  · simpa using (eT i).2
  · simpa using (eF j).2

theorem volgU_eq_Icc (n : ℕ) :
    IwasawaCovolume.volgU n = ∏ i ∈ Finset.Icc 1 n, (2 * Real.pi) ^ i / ((i - 1).factorial : ℝ) := by
  induction n with
  | zero => simp [IwasawaCovolume.volgU]
  | succ k ih =>
    rw [IwasawaCovolume.volgU, Finset.prod_range_succ, ← IwasawaCovolume.volgU, ih, Finset.prod_Icc_succ_top (by omega)]
    simp

end Formalism.L2.S.S7.ZsCovSum
