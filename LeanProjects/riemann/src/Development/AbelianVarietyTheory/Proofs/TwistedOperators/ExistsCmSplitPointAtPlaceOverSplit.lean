import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltSc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneHomothetyCarriesSelfDualOfSplitComponentStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsFrameFinitePartMulOfCarriesLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardDivisionPointsHalfSplitPlaceNormPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGood
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitLocalPlaceDataAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegerIffOfEquiv
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateIntoK1
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitPtAtPlace

set_option maxHeartbeats 1000000 in

theorem exists_splitPt_cpt : ∀ (D : D7) (w : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e w → D.host.F = maximalRealSubfield D.host.E → ∃ p : GlobalTheory.FinPl.SplitPt D (Kw w), p.e = e ∧ p.v = w.under (𝓞 D.host.F) ∧ ∀ a : AE D, p.pr a = cpt w (Lev.swapAE D (finPart D a)) := by
  intro D w e he hF
  obtain ⟨s, hsw⟩ := GlobalTheory.OffBad.splitPlace_of_isSplitPl D w
    (GlobalTheory.OffBad.isSplitPl_of_isSplit D w (GlobalTheory.DivPtLocal.isSplit_of_isIdemAt D w e he))
  subst hsw
  obtain ⟨p, c, hpl, hc, hci, hπ⟩ := GlobalTheory.T.exists_splitLocalPlaceData_at_splitPlace D s hF
  obtain ⟨q, hq⟩ := GlobalTheory.PlaceSplitPt.exists_splitPt p
  have hqe : q.e = p.e := by rw [← hq]; rfl
  have hqpr : ∀ a, q.pr a = p.π a := fun a => by rw [← hq]; rfl
  have hpe : Formalism.L2.NTheta.IsIdemAt p.e s.w := ⟨p.split, hpl.2.2⟩
  have hee : p.e = e := GlobalTheory.LocMod.PinInhab.idem_unique hpe he
  refine ⟨q, hqe.trans hee, GlobalTheory.LocMod.PinInhab.v_eq_under q (hqe ▸ hpe), fun a => ?_⟩
  rw [hqpr, hπ]
  have key := GlobalTheory.SplitFrameW.cpt_swap D.host.F hF ((GlobalTheory.StdFrames.toAd D).comp (Lev.swapAE D))
    (fun a x => GlobalTheory.StdFrames.toAd_spec D x a) s c hc hci (GlobalTheory.NJoin.tensCast hF (finPart D a))
  rw [← key]
  have hcast : GlobalTheory.NJoin.tensCast hF = GlobalTheory.Mem.R3.swapCast hF := rfl
  rw [hcast, RingEquiv.symm_apply_apply]
  rfl

end GlobalTheory.SplitPtAtPlace
