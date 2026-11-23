import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSubgroupOfLocalComponentsSplitPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemBesselGroupOfLocalMatrixGridNodeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumBasePointUniqueAllTuples
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCmSplitPointAtPlaceOverSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLocalGroupsNormalFramesSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNormalFramesAndBasePointSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowLiftBes
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem exists_suppAt_locAt {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (B : Frames G) (t : T)
    {w : Pl D.host.E} (ew : AE D) (hew : Formalism.L2.NTheta.IsIdemAt ew w) {j : ℕ} (hj : j ≤ D.R.m)
    (x : GL (Fin ((locGrid G t w).rank (D.R.m, j))) (Kw w)) :
    ∃ h : GA D (G.V (.grid D.R.m j)), SuppAt ew _ h ∧ GlobalTheory.RowRep.locAt B t w j hj h = x := by
  have he : IsIdemSum ew {w} := ⟨⟨fun _ => ew, fun PP hPP => by rw [Finset.mem_singleton.1 hPP]; exact hew,
    (Finset.sum_singleton (fun _ => ew) w).symm⟩, hew.1.2.1⟩
  obtain ⟨g', hg'⟩ := GlobalTheory.RowRep.exists_inBasis_eq (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj⟩) (B.β D.R.m j) w x
  obtain ⟨h, hh, hl⟩ := GlobalTheory.RowRep.exists_suppAt_loc_eq (G.V (.grid D.R.m j)) {w} ew he fun w' => (Finset.mem_singleton.1 w'.2).symm ▸ g'
  exact ⟨h, hh, hg' _ (hl ⟨w, Finset.mem_singleton_self w⟩)⟩

end GlobalTheory.RowLiftBes

namespace GlobalTheory.RowLiftBes
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem mem_besGrp_of_hasLoc : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t j σ, j ∈ idx D → ∀ (hj : j ≤ D.R.m) (hj' : j < D.R.m) (h' : j + 2 * σ + 2 = D.R.m)
    (r : GA D (ch.G.V (.grid D.R.m j))) (g : ∀ w : locPl ch.G t, GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, j))) (Kw w.1)),
    HasLoc t ch.S.B hj r g → (∀ w, g w ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := j) hj') →
    r ∈ besGrp (besDecAt ch.G j σ h') (GlobalTheory.OrthSumExists.orthDecHsum D _ _) := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ => ?_⟩⟩
  intro t j σ hi hj hj' h' r g ⟨e, he, hsupp, hloc⟩ hg
  refine GlobalTheory.T.mem_subgroup_of_localComponents_splitPlaces _ (locPl ch.G t) e he _ r hsupp fun w hw ew hew => ?_
  obtain ⟨h, hs, hl⟩ := exists_suppAt_locAt ch.S.B t ew hew hj (g ⟨w, hw⟩)
  refine ⟨h, GlobalTheory.T.mem_besselGroup_of_localMatrix_gridNode ch.S.toGridChoice (Set.mem_univ t) hw ew hew hj hj' h' h hs (hl ▸ hg ⟨w, hw⟩), hs, ?_⟩
  exact GlobalTheory.RowBaseUniq.loc_eq_of_inBasis _ _ _ (hl.trans (hloc ⟨w, hw⟩).symm)

end GlobalTheory.RowLiftBes
