import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticesDifferentiableOperator
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MovedVacuumVectorCorrespondence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticesDifferentiableOperatorStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
noncomputable section
namespace GlobalTheory.MovedDict
theorem jets_moved_by_translation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (p : Pair _), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ∃ (Ls : Submodule (𝓞 D.host.E) (Fin (ch.G.pS p).rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin (ch.G.pT p).rank → D.host.E)) (κ : ℂ), SD D Ls ∧ SD D Lt ∧ Mod1All κ ∧ Differentiable ℂ (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p)) ∧ (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → EqAt D q Ls (stdL D _) ∧ EqAt D q Lt (stdL D _) ∧ ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ‖ = 1) ∧ ∀ (k : ℕ), 0 < k → ∀ w : WO (ch.G.pS p) (ch.G.pT p), k • w ∈ latO (ch.G.pS p) (ch.G.pT p) (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True) → ∃ (ζ : Qbar) (s : VC D (ch.G.pS p).rank (ch.G.pT p).rank), (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ k • s ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt ∧ ∀ mon, jetTab ch.W ch.S.N.frC p (heisO ch.W.ψ (ch.G.pS p) (ch.G.pT p) w (ch.S.Z.vac p)) (x * ch.S.N.u _) (y * ch.S.N.u _) mon = ch.S.Z.c0 p * opp p (((mon.mapDomain (fvar ch.G p)).prod fun v e => period ch.S.Z.δ v.1 ^ e) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial (mon.mapDomain (fvar ch.G p)) 1) fun z => κ * ((ζ : ℂ) * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK ch.S.Z.δ) s (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p)) z)) := by
  intro hPr hInp
  obtain ⟨CF0, h2⟩ := _root_.GlobalTheory.T.twist_moved_vacuum_correspondence hPr hInp
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := h2 ε CF hCF
  refine ⟨x₀, fun D large₂ hε hx₀ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt => ?_⟩
  intro p hp x y
  obtain ⟨Ls, Lt, κ, hSs, hSt, hκ, hd, hq, hvac, hmov, hjet⟩ := hx D large₂ hε hx₀ Γ Pl0 T A Ks R F hS ch hIs hAt p hp x y
  refine ⟨Ls, Lt, κ, hSs, hSt, hκ, hd, hq, fun n hn w hw => ?_⟩
  obtain ⟨ζ, s, hζ, hs, hj⟩ := GlobalTheory.T.finiteHeisenbergTranslate_selfDualVacuum_fockJets ch.S.toGridChoice p hp Ls Lt κ _ hSs hSt hd hvac hjet n hn _
    (by rw [← actO_nsmul]; exact hmov _ hw)
  refine ⟨ζ, s, hζ, hs, fun mon => ?_⟩
  rw [jetTab_heisO ch.W ch.S.N.frC p hp _ (ch.S.Z.vac_is p hp).2.theta w _ _ mon]
  exact hj _
end GlobalTheory.MovedDict
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translated_jets_dictionary : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (p : Pair _), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ∃ (Ls : Submodule (𝓞 D.host.E) (Fin (ch.G.pS p).rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin (ch.G.pT p).rank → D.host.E)) (κ : ℂ), SD D Ls ∧ SD D Lt ∧ Mod1All κ ∧ Differentiable ℂ (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p)) ∧ (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → EqAt D q Ls (stdL D _) ∧ EqAt D q Lt (stdL D _) ∧ ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ‖ = 1) ∧ ∀ (k : ℕ), 0 < k → ∀ w : WO (ch.G.pS p) (ch.G.pT p), k • w ∈ latO (ch.G.pS p) (ch.G.pT p) (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True) → ∃ (ζ : Qbar) (s : VC D (ch.G.pS p).rank (ch.G.pT p).rank), (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ k • s ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt ∧ ∀ mon, jetTab ch.W ch.S.N.frC p (heisO ch.W.ψ (ch.G.pS p) (ch.G.pT p) w (ch.S.Z.vac p)) (x * ch.S.N.u _) (y * ch.S.N.u _) mon = ch.S.Z.c0 p * opp p (((mon.mapDomain (fvar ch.G p)).prod fun v e => period ch.S.Z.δ v.1 ^ e) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial (mon.mapDomain (fvar ch.G p)) 1) fun z => κ * ((ζ : ℂ) * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK ch.S.Z.δ) s (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p)) z)) := by
  first | exact @_root_.GlobalTheory.MovedDict.jets_moved_by_translation | exact _root_.GlobalTheory.MovedDict.jets_moved_by_translation | (intros; apply _root_.GlobalTheory.MovedDict.jets_moved_by_translation <;> assumption)
end
