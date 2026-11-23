import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentPointLastIndex
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefCaseCoreStatement

set_option synthInstance.maxHeartbeats 200000

section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FlatCore
namespace GlobalTheory.DefCoreLie
end GlobalTheory.DefCoreLie
namespace GlobalTheory.DefCoreLie
theorem degLie_core_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), _root_.GlobalTheory.CovTop.RowsTAlt p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → ∀ (Z : Comp (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c) (P : PtData Z) (τ : Psi p.T.Q.H), P.degLie τ.1 = -flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm := by
  intro D L hT Gi Gl Kc Y0 cX ex Csz p i PP A M hR hm hG hW hN hF Z P τ
  obtain ⟨hDC, -, -, -⟩ := _root_.GlobalTheory.T.finite_nonempty_components_and_dict_mem_dom p i PP A M hR hm hG hW hN hF
  have hJ : LawsJ p.T := p.fw.laws
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.succ_pos _, hm.le⟩
  have hL : Laws (p.T.U ((i : ℕ) + 1)) (xiR D) := GlobalTheory.LawsCore.laws_core D p.T hJ _ hj hF
  obtain ⟨_, χ, hχ, hOm, -, hH⟩ := GlobalTheory.T.logPeriod_eq_kroneckerCharacter_logPeriod_of_host D L p.T.Q hJ.pins.1 p.Del p.h0
  have hFr := frameDeg_def GlobalTheory.T.cmObject_definite_lieEigenLattice_degree_difference D.host.E p.T.Q.H hH χ hχ _ _ _ _ _ _ _ hL hDC.q
  obtain ⟨s⟩ := GlobalTheory.FlatLine.Definite.nonempty_flatSec (p.T.U ((i : ℕ) + 1)) (xiR D) hDC.q hDC.p hDC.good hDC.unf hDC.geo Z τ
  have h := (hFr Z τ (ArchSec.ofConst s.toFrame) s.toFrame.rho_vw fun w v hv => by
      have h1 := s.toFrame.val_eq hv
      rw [Pi.zero_apply, zero_add] at h1
      exact h1).2
  rw [(GlobalTheory.T.degree_dualDetLie_eq_neg_flatSection_degree _ _ _ _ _ _ _ _ _ hDC Z P).1 τ s, s.deg_eq_toFrame, flatDegVal, ← hOm, ← h]
  rfl
end GlobalTheory.DefCoreLie
end
