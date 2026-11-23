import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootOfUnityThetaTwist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlaceStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsFinOf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPointPrescribedLocalMatricesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.RowBase

theorem exists_isBase : Big fun ch => ∀ t, ∃ b, IsBase t ch.S.B b := by
  refine GlobalTheory.RowReal.big_mono ?_ (Big.and GlobalTheory.T.representation_at_every_place GlobalTheory.T.exists_unitaryPoint_prescribed_localMatrices)
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch ⟨hrep, hloc⟩ t
  classical
  let β0 : CosFam ch.G t := fun _ _ => DoubleCoset.mk _ _ 1
  obtain ⟨b', hb'⟩ := (hrep 1 t).1 β0
  have H : ∀ j, ∃ x : GA D (ch.G.V (.grid D.R.m j)),
      (j ∈ idx D → ∃ δ, IsTilt ch.G j δ ∧ IsFinOf δ x) ∧ (j ∉ idx D → x = 1) := by
    intro j
    by_cases hj : j ∈ idx D
    · have hle : j ≤ D.R.m := by have := GlobalTheory.RowRep.idx_le hj; omega
      obtain ⟨δ, -, hδ, -⟩ := hb'.2 j hj hle
      obtain ⟨x, hx⟩ := GlobalTheory.RowRep.exists_isFinOf _ δ
      exact ⟨x, fun _ => ⟨δ, hδ, hx⟩, fun h => absurd hj h⟩
    · exact ⟨1, fun h => absurd h hj, fun _ => rfl⟩
  choose f hf using H
  obtain ⟨r, hr⟩ := hloc t 0 (Nat.zero_le _) (fun w => (stair (locGrid ch.G t w.1) (unifAt w.1) (cosExp ch.G w.1) 0)⁻¹)
  refine ⟨Function.update f 0 r, ?_, ?_, ?_⟩
  · rw [Function.update_self]; exact hr
  · intro j hj
    have h0 : j ≠ 0 := by have := GlobalTheory.RowRep.idx_le hj; omega
    rw [Function.update_of_ne h0]
    exact (hf j).1 hj
  · intro j h0 hj
    rw [Function.update_of_ne h0]
    exact (hf j).2 hj

end GlobalTheory.RowBase
