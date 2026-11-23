import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GeneralDiagonalMatrix
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Formalism.LocalToGlobal.ProjectiveLattices.CompFin
import Formalism.LocalToGlobal.ProjectiveLattices.ModelAt
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.DefCore

theorem defCase_core : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), RowsT p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → DefCase (p.T.U ((i : ℕ) + 1)) (xiR D) ∧ Finite (Comp (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c) ∧ Nonempty (Comp (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c) ∧ (∀ σ, GoodEmb p.T.Q.c σ → ∀ g, (p.T.dict ((i : ℕ) + 1) σ g).2 ∈ ((p.T.U ((i : ℕ) + 1) σ).X (p.T.dict ((i : ℕ) + 1) σ g).1).dom) := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M _ hm _ hW _ hF
  have hJ : LawsJ p.T := p.fw.laws
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.succ_pos _, hm.le⟩
  obtain ⟨hp, hq, hr⟩ := hW.sig
  have hk := D.R.m_add_three_le_k
  have hq0 : (p.T.Q.Dw ((i : ℕ) + 1)).q = 0 := by
    have : (dat p i).q = D.R.m - ((i : ℕ) + 1) := by rw [hq]; rfl
    simpa [dat, hm] using this
  have hp1 : 1 ≤ (p.T.Q.Dw ((i : ℕ) + 1)).p := by
    have : (dat p i).p = D.R.k + ((i : ℕ) + 1) - 1 := by rw [hp]; rfl
    simp only [dat] at this
    omega
  refine ⟨⟨hq0, hp1, ?_, hJ.pins.2.1.2, hF, hJ.unf _ hj, ?_⟩, CompFin.finite_comp _ _, ?_, ?_⟩
  · exact goodAt_of_two_primes hJ.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  · exact (GlobalTheory.LevGeo.laws_core D p.T _ hJ hj).xiAbs
  · exact (GlobalTheory.GeomIrr.compNe_and_exists_fnAlgClosed _ _ _ _ _ _ (by omega)).1
  · intro σ hσ g
    exact GlobalTheory.IndefiniteRowSideFullHecke.GeneralDiagonalMatrix.dict_mem_dom p.T hJ _ hj σ hσ g

end GlobalTheory.DefCore
