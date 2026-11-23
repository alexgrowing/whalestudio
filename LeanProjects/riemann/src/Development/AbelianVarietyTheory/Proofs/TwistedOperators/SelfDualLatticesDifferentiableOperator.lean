import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrT
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticesEntireIntertwiningStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteHeisenbergTranslateSelfDualVacuumFockJetsStatement
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

theorem negGA_mem_GfC' {D : D7} (V : HSp D) {g : Formalism.L2.Theta.GA D V} (hg : g ∈ GfC V) : negGA V g ∈ GfC (negSp V) := by
  have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
  simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
  rw [e]
  exact hg

theorem jetTab_heisO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc}
    (W : G.Weil) (B : VertexFrames G) (p : GlobalTheory.ChiGrid.Pair T), DefPair D.R.m p → ∀ f : WO (G.pS p) (G.pT p) → ℂ,
    IsThetaFunO W.ψ _ _ f → ∀ w : WO (G.pS p) (G.pT p), ∀ (x : FinPt G p.small) (y : FinPt G p.big)
    (mon : DVar D.what₂.Tau (G.V p.small).rank (G.V p.big).rank →₀ ℕ),
    jetTab W B p (heisO W.ψ _ _ w f) x y mon = fockIn W B p (heisO W.ψ _ _ (actO _ _ (G.toPair p x y).1 (G.toPair p x y).2 w)
      (W.om p (G.toPair p x y) f)) (MvPolynomial.monomial (mon.mapDomain (fvar G p)) 1) 0 := by
  intro D T L sc G W B p hp f hf w x y mon
  have hn := DefPair.nodes hp
  have hom := W.om_is p (by cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega)
  have mem : (G.toPair p x y).1 ∈ GfC (G.pS p) ∧ (G.toPair p x y).2 ∈ GfC (G.pT p) := by
    cases p with
    | chi i j => exact ⟨negGA_mem_GfC' _ y.2, x.2⟩
    | mu t i j => exact ⟨x.2, y.2⟩
    | core i => exact ⟨negGA_mem_GfC' _ y.2, x.2⟩
    | top t j => exact ⟨x.2, y.2⟩
  have hth := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all W.ψ_std hf w
  have e := GlobalTheory.OrientedHeis.om_fin_pureTensorO W.ψ _ _ _ _ (W.om p) hom W.θ W.θ_is _ mem.1 _ mem.2
    (G.cartS W.cart p) (G.onT W.cart p) (G.onS B p) (G.onT B p) _ (MvPolynomial.monomial (mon.mapDomain (fvar G p)) 1) hth
  rw [hom.om_heis _ _ w f hf] at e
  simp only [jetTab, GlobalTheory.FunObj.kerFin, GridData.Weil.ker, thetaKO, fockIn]
  rw [e]

theorem actO_nsmul {D : D7} (S T : HSp D) (g : Formalism.L2.Theta.GA D S) (h : Formalism.L2.Theta.GA D T) (n : ℕ) (w : WO S T) :
    actO S T g h (n • w) = n • actO S T g h w := by
  unfold actO
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, succ_nsmul, Matrix.mul_add, Matrix.add_mul, ih]

theorem jets_moved : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (p : Pair _), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ∃ (Ls : Submodule (𝓞 D.host.E) (Fin (ch.G.pS p).rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin (ch.G.pT p).rank → D.host.E)) (κ : ℂ), SD D Ls ∧ SD D Lt ∧ Mod1All κ ∧ Differentiable ℂ (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p)) ∧ (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → EqAt D q Ls (stdL D _) ∧ EqAt D q Lt (stdL D _) ∧ ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ‖ = 1) ∧ ∀ (k : ℕ), 0 < k → ∀ w : WO (ch.G.pS p) (ch.G.pT p), k • w ∈ latO (ch.G.pS p) (ch.G.pT p) (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True) → ∃ (ζ : Qbar) (s : VC D (ch.G.pS p).rank (ch.G.pT p).rank), (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ k • s ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt ∧ ∀ mon, jetTab ch.W ch.S.N.frC p (heisO ch.W.ψ (ch.G.pS p) (ch.G.pT p) w (ch.S.Z.vac p)) (x * ch.S.N.u _) (y * ch.S.N.u _) mon = ch.S.Z.c0 p * opp p (((mon.mapDomain (fvar ch.G p)).prod fun v e => period ch.S.Z.δ v.1 ^ e) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial (mon.mapDomain (fvar ch.G p)) 1) fun z => κ * ((ζ : ℂ) * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK ch.S.Z.δ) s (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p)) z)) := by
  intro hPr hInp
  obtain ⟨CF0, h2⟩ := GlobalTheory.T.exists_lattices_entire_intertwining hPr hInp
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
