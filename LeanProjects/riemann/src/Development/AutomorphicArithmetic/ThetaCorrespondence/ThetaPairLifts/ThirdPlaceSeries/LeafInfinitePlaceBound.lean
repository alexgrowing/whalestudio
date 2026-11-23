import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
namespace GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
section Fit
open GlobalTheory.ChiGrid Formalism.L2.Host
variable {T : Type} {Lc : LevCh D T} {sc : Consts}
end Fit
def LeafConditions (Comparison₂ : TieT) (Q : PropT) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm CH => DIVinN Fm →
  ∃ C0 : ℝ, ∀ C, C0 ≤ C → _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p => ∀ d : FunIn p CF, Comparison₂ p CF d → Q p CF d C CH
def ExistsFunctionIn (Fld : FldT) (Comparison₂ : TieT) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm _ => DIVinN Fm →
  _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p => ∀ (G : Grid p CF) (W : G.Weil), W.Over p.R.toRealDat → GridFit p G → Fld p CF G W →
    ∃ d : FunIn p CF, d.G = G ∧ Comparison₂ p CF d
def LeafMinimalMass (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun _ _ d C _ => LeafMM d.O C
def LeafUniqueMap (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d _ _ =>
  ∃ ze : Tup p → _, ze p.P.A3.fam3.base3.μ0 = 1 ∧ (∀ t, ∃ n : ℕ, 0 < n ∧ ze t ^ n = 1) ∧
    LeafC (p.S false) (d.data ze ∅ fun _ => 0)
def LeafKernel (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun _ _ d _ _ => LeafKer d.O
def LeafFixedPoint (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => ∃ Tf dF, LeafFP (d.data (fun _ => 1) Tf dF) (p.S false).μ C p.Z.b
def LeafHeightMapBound (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ =>
  ∀ vb : Matrix (Fin d.n) (Fin ((Df p).dQ p.P.A3.fam3.base3.μ0)) _,
    vb * (Df p).Pq p.P.A3.fam3.base3.μ0 = d.V p.P.A3.fam3.base3.μ0 →
      Formalism.HN.htMap (Pi.basisFun _ (Fin ((Df p).dQ p.P.A3.fam3.base3.μ0))) ((Df p).XQ p.P.A3.fam3.base3.μ0)
        (Pi.basisFun _ (Fin d.n)) d.X' (Matrix.mulVecLin vb) ≤ d.O.bIPa C p.Z.b
def LeafInfinitePlaceBound : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition fun p _ d C _ =>
  ∃ g : InfinitePlace _ → ℝ, (∀ v q, (Df p).Qp p.P.A3.fam3.base3.μ0 q ≠ ⊥ →
      g v ≤ ∑ j, Real.log ((p.S false).lam j p.P.A3.fam3.base3.μ0 q v)) ∧
    -(3 * C * d.O.f * d.O.m * (d.O.N : ℝ) ^ 2 * Real.log p.Z.b) ≤ Formalism.PairingDivisionLocalBalance.meanInf _ g
def LeafUniqueSquareRoot (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => LeafOneSquare d.O (p.S false).μ C p.Z.b
def LeafDensity (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => PrimeCountingSumBound d.O C p.Z.x p.Z.b
def LeafIntegrality (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => LeafINT d.O C p.Z.b
def ArchimedeanCondition (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => LeafARCH d.O C p.Z.b
def LeafThetaBound (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => LeafTHB d.O C p.Z.x p.Z.b
def LeafWeightBound (Comparison₂ : TieT) : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions (Fitted Comparison₂) fun p _ d C _ => LeafWt d.O C p.Z.b
def DescentHeightCondition : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition fun p _ d _ _ => leafHypothesesConst d.O ∧ LatticeConstantBound d.O p.Z.b
def RankGapBound' : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition fun p _ d C _ => DegreeAndSizeBounds d.O C p.Z.b
def RamifiedSumBound' : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition fun p _ d C _ => PrimePowerModuliSumBound d.O C p.Z.b ∧ LeafCS d.O p.Z.b
def DescentPolynomialCondition : Prop := _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition fun p _ d C CH => LeafPol d.O C p.Z.x CH p.Z.b
def ScaleCondition : Prop := Closed FamHyp fun Fm _ => _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p =>
  1 ≤ p.Z.x ∧ 1 ≤ Real.log p.Z.b ∧ Real.log p.Z.b + Real.log p.Z.x ≤ 3 * Real.log p.Z.b
def BundleCondition : Prop := ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.PointConditions' →
  (Df p).WF ∧ ∃ R0 : IndefRows (Df p), R0.toIndefData = p.S false
def ConstantFunctionFits (Fld : FldT) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm CH => DIVinN Fm →
  _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun _ _ _ p => HasGrid Fld p CF → ∀ C, (p.S false).FUN (p.N C CH)
theorem evPt_and' {eps : ℝ} {Fm : FamP eps} {P Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (hP : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm P) (hQ : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm Q) : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm fun x hx i p => P x hx i p ∧ Q x hx i p :=
  let ⟨a, ha⟩ := hP
  let ⟨b, hb⟩ := hQ
  ⟨max a b, fun x hx h i p hp => ⟨ha x hx (le_of_max_le_left h) i p hp, hb x hx (le_of_max_le_right h) i p hp⟩⟩
theorem evPt_mono {eps : ℝ} {Fm : FamP eps} {P Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (hP : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm P) (h : ∀ x hx i p, p.PointConditions' → P x hx i p → Q x hx i p) : _root_.GlobalTheory.BigTop.EventuallyAtPoints Fm Q :=
  let ⟨a, ha⟩ := hP
  ⟨a, fun x hx h' i p hp => h x hx i p hp (ha x hx h' i p hp)⟩
theorem LeafConditions.mono {Comparison₂ Tie' : TieT} {Q Q' : PropT} (h : _root_.GlobalTheory.BigTop.Fun.LeafConditions Comparison₂ Q)
    (h' : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF) (C CH : ℝ), p.PointConditions' → Tie' p CF d →
      Comparison₂ p CF d ∧ (Q p CF d C CH → Q' p CF d C CH)) : _root_.GlobalTheory.BigTop.Fun.LeafConditions Tie' Q' := by
  obtain ⟨CF0, h⟩ := h
  refine ⟨CF0, fun CF hCF => (h CF hCF).imp fun Fm CH _ a hN => ?_⟩
  obtain ⟨C0, a⟩ := a hN
  exact ⟨C0, fun C hC => _root_.GlobalTheory.BigTop.Fun.evPt_mono (a C hC) fun _ _ _ p hp b d hd =>
    (h' p CF d C CH hp hd).2 (b d (h' p CF d C CH hp hd).1)⟩
theorem LeafConditions.and {Comparison₂ : TieT} {Q Q' : PropT} (h : _root_.GlobalTheory.BigTop.Fun.LeafConditions Comparison₂ Q) (h' : _root_.GlobalTheory.BigTop.Fun.LeafConditions Comparison₂ Q') :
    _root_.GlobalTheory.BigTop.Fun.LeafConditions Comparison₂ fun p CF d C CH => Q p CF d C CH ∧ Q' p CF d C CH := by
  obtain ⟨a, h⟩ := h
  obtain ⟨b, h'⟩ := h'
  refine ⟨max a b, fun CF hCF => ((h CF (le_of_max_le_left hCF)).and (h' CF (le_of_max_le_right hCF))).imp
    fun Fm CH _ c hN => ?_⟩
  obtain ⟨C0, c1⟩ := c.1 hN
  obtain ⟨C1, c2⟩ := c.2 hN
  exact ⟨max C0 C1, fun C hC => _root_.GlobalTheory.BigTop.Fun.evPt_mono (_root_.GlobalTheory.BigTop.Fun.evPt_and' (c1 C (le_of_max_le_left hC)) (c2 C (le_of_max_le_right hC)))
    fun _ _ _ _ _ e d hd => ⟨e.1 d hd, e.2 d hd⟩⟩
theorem LeafConditions.of_noTie {Q : PropT} (h : _root_.GlobalTheory.BigTop.Fun.LeafConditions trivialTieCondition Q) (Comparison₂ : TieT) : _root_.GlobalTheory.BigTop.Fun.LeafConditions Comparison₂ Q :=
  h.mono fun _ _ _ _ _ _ _ => ⟨trivial, id⟩
theorem fun0Fit_of_leaves_alt (Fld : FldT) (Comparison₂ : TieT) (hB : _root_.GlobalTheory.BigTop.Fun.BundleCondition) (hS : _root_.GlobalTheory.BigTop.Fun.ScaleCondition) (hE : _root_.GlobalTheory.BigTop.Fun.ExistsFunctionIn Fld Comparison₂) (h1 : _root_.GlobalTheory.BigTop.Fun.LeafMinimalMass Comparison₂) (h2 : _root_.GlobalTheory.BigTop.Fun.LeafUniqueMap Comparison₂)
    (h3 : _root_.GlobalTheory.BigTop.Fun.LeafKernel Comparison₂) (h4 : _root_.GlobalTheory.BigTop.Fun.LeafFixedPoint Comparison₂) (h5 : _root_.GlobalTheory.BigTop.Fun.LeafHeightMapBound Comparison₂) (h6 : _root_.GlobalTheory.BigTop.Fun.LeafInfinitePlaceBound) (h7 : _root_.GlobalTheory.BigTop.Fun.LeafUniqueSquareRoot Comparison₂) (h8 : _root_.GlobalTheory.BigTop.Fun.LeafDensity Comparison₂) (h9 : _root_.GlobalTheory.BigTop.Fun.LeafIntegrality Comparison₂) (h10 : _root_.GlobalTheory.BigTop.Fun.ArchimedeanCondition Comparison₂)
    (h11 : _root_.GlobalTheory.BigTop.Fun.LeafThetaBound Comparison₂) (h12 : _root_.GlobalTheory.BigTop.Fun.LeafWeightBound Comparison₂) (h13 : _root_.GlobalTheory.BigTop.Fun.DescentHeightCondition) (h14 : _root_.GlobalTheory.BigTop.Fun.RankGapBound') (h15 : _root_.GlobalTheory.BigTop.Fun.RamifiedSumBound') (h16 : _root_.GlobalTheory.BigTop.Fun.DescentPolynomialCondition) : _root_.GlobalTheory.BigTop.Fun.ConstantFunctionFits Fld := by
  obtain ⟨a, hA⟩ := _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h1 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h2 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h3 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h4 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h5 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and (_root_.GlobalTheory.BigTop.Fun.LeafConditions.of_noTie h6 _) <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h7 <|
    _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h8 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h9 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h10 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h11 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and h12 <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and (_root_.GlobalTheory.BigTop.Fun.LeafConditions.of_noTie h13 _) <|
    _root_.GlobalTheory.BigTop.Fun.LeafConditions.and (_root_.GlobalTheory.BigTop.Fun.LeafConditions.of_noTie h14 _) <| _root_.GlobalTheory.BigTop.Fun.LeafConditions.and (_root_.GlobalTheory.BigTop.Fun.LeafConditions.of_noTie h15 _) (_root_.GlobalTheory.BigTop.Fun.LeafConditions.of_noTie h16 _)
  obtain ⟨b, hE⟩ := hE
  refine ⟨max a b, fun CF hCF => (((hA CF (le_of_max_le_left hCF)).and (hE CF (le_of_max_le_right hCF))).and hS).imp
    fun Fm CH _ c hN => ?_⟩
  obtain ⟨C0, c1⟩ := c.1.1 hN
  refine _root_.GlobalTheory.BigTop.Fun.evPt_mono (_root_.GlobalTheory.BigTop.Fun.evPt_and' (_root_.GlobalTheory.BigTop.Fun.evPt_and' (c1 (max C0 1) (le_max_left _ _)) (c.1.2 hN)) c.2) fun x hx i p hp e hG C => ?_
  obtain ⟨⟨e1, e2⟩, s1, s2, s3⟩ := e
  obtain ⟨G, W, g1, g2, g3⟩ := hG
  obtain ⟨d, rfl, hd⟩ := e2 G W g1 g2 g3
  obtain ⟨l1, ⟨ze, z1, z2, l2⟩, l3, ⟨Tf, dF, l4⟩, l5, l6, l7, l8, l9, l10, l11, l12, l13, l14, l15, l16⟩ := e1 d ⟨g2, hd⟩
  obtain ⟨wf, R0, hR⟩ := hB p hp
  have v0 : (d.data ze Tf dF).vmu p.P.A3.fam3.base3.μ0 = d.V p.P.A3.fam3.base3.μ0 := by
    show (ze _)⁻¹ • _ = _
    rw [z1, inv_one]
    exact one_smul _ _
  have v1 : ∀ Tf dF t, (d.data (fun _ => 1) Tf dF).vmu t = d.V t := fun _ _ _ => by
    show (1 : _)⁻¹ • _ = _
    rw [inv_one]
    exact one_smul _ _
  have hRR := R0.RR_spec Formalism.DivisionValues.lattice_gluing wf
  refine functional_lower_bound_of_conditions_numeric wf (p.S false) p.Z C CH (d.data ze Tf dF) (max C0 1) (hR ▸ R0.D_pos) (hR ▸ R0.h0) (hR ▸ R0.l1a)
    (hR ▸ R0.l1c) (hR ▸ R0.frames.1) (hR ▸ hRR.1) (hR ▸ hRR.2) (le_max_right _ _) s1 s2 s3 l1 l2 ?_ ?_ ⟨?_, l6⟩ l7 l8 l9 l10
    l11 l13.1 l13.2 l14 l15.1 l15.2 l12 l16
  · have : LinearMap.ker (d.O.vmu _).mulVecLin = _ := l3
    rw [v1] at this
    show LinearMap.ker ((d.data ze Tf dF).vmu _).mulVecLin = _
    rw [v0]
    exact this
  · have := GlobalTheory.finitePlaceBound_inv_rootOfUnity_smul _ ze _ _ _ z2 l4
    simp only [v1] at this
    exact this
  · intro vb hvb
    exact l5 vb (hvb.trans v0)
end GlobalTheory.BigTop.Fun
end
end
