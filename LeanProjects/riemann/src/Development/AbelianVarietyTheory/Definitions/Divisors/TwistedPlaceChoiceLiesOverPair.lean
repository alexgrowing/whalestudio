import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharGal
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.FunctionalLowerBoundOfConditionsNumeric
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyGridDataIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilOver
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotTeichTrivOfIsDelta
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointConductorPlacesExcludedSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatLatSmulLeOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisGe

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

namespace GlobalTheory.BigTop.Fun

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

abbrev Df (p : PtAt ex Csz) : DefSide p.P.A3.fam3.base3 := lv (p.F.fc (p.R.toCx3 p.F).zs) false

abbrev Tup (p : PtAt ex Csz) : Type := p.P.A3.fam3.base3.Tup

abbrev PlL (D : D7) : Type := HeightOneSpectrum (𝓞 D.what₂.LL)

abbrev Sq (D : D7) : Type := Fin D.R.m × Fin D.R.m

abbrev Grid (p : PtAt ex Csz) (CF : ℝ) : Type 1 := GlobalTheory.ChiGrid.GridData p.R.toRealDat.toLevCh ⟨1, CF, p.Z.b⟩

set_option genInjectivity false in
set_option genSizeOfSpec false in

structure FunIn (p : PtAt ex Csz) (CF : ℝ) where

  G : GlobalTheory.ChiGrid.GridData p.R.toRealDat.toLevCh ⟨1, CF, p.Z.b⟩

  W : G.Weil

  ext : W.Over p.R.toRealDat

  n : ℕ

  X' : InfinitePlace D.what₂.LL → Matrix (Fin n) (Fin n) ℂ

  M : Submodule (𝓞 D.what₂.LL) (Fin n → D.what₂.LL)

  V : ∀ t : Tup p, Matrix (Fin n) (Fin ((Df p).nV t)) D.what₂.LL

  rq : Tup p → Sq D → D.what₂.LL

  dl : PlL D → ℝ

  Sd : Finset ℕ

  Se : Finset ℕ

  N0 : Sq D → ℤ → ℕ → ℝ

  zA : Sq D → D.what₂.LL

  zA' : Sq D → D.what₂.LL

  zT : Sq D → ℤ → D.what₂.LL

  zTd : Sq D → Bool → ℤ → D.what₂.LL

  gT : Sq D → ℤ → PlL D → ℤ

  ch : PlL D → Bool

  Bw : ℝ

open Classical in

def cloud (D : D7) (τ i : ℕ) : ℤ :=
  if h : τ < Fintype.card D.what₂.Tau then
    (GlobalTheory.SignedHC.GridData.ofHCParam (D.hc ((Fintype.equivFin D.what₂.Tau).symm ⟨τ, h⟩)) 0 0 0).v i else 0

def sqRank (D : D7) (ij : Sq D) : ℕ :=
  GlobalTheory.ChiGrid.rankV D ij.1 ((ij.2 : ℕ) + 1) + GlobalTheory.ChiGrid.rankV D ((ij.1 : ℕ) + 1) ij.2

open Classical in

def FunIn.data {p : PtAt ex Csz} {CF : ℝ} (d : FunIn p CF) (ze : Tup p → D.what₂.LL) (Tf : Finset (PlL D)) (dF : PlL D → ℤ) :
    FunData D.what₂.LL (Df p) where
  n := d.n
  X' := d.X'
  M := d.M
  vmu t := (ze t)⁻¹ • d.V t
  Tf := Tf
  dF := dF
  m := D.R.m
  rq := d.rq
  dl := d.dl
  Sd := d.Sd
  Se := d.Se
  N0 := d.N0
  zA := d.zA
  zA' := d.zA'
  zT := d.zT
  zTd := d.zTd
  gT := d.gT
  ch := d.ch
  dd := sqRank D
  hd ij := sqRank D ij / 2
  yy ij := D.R.m - 1 - ij.2
  Sq := HeightOneSpectrum (𝓞 D.host.F)
  S0 := d.G.pl.S0
  sv0 := d.G.pl.v0
  cc v := if v = d.G.pl.v0 then 1 else 2
  qq v := Ideal.absNorm v.asIdeal
  f := D.R.f
  k := D.R.k
  tt := D.R.t
  cl := cloud D
  g1 := D.host.g 0
  g2 := D.host.g 1
  pd := D.host.pde
  pd' := D.host.pde'
  dE := discr D.host.E
  Bw := d.Bw

abbrev FunIn.O {p : PtAt ex Csz} {CF : ℝ} (d : FunIn p CF) : FunData D.what₂.LL (Df p) := d.data (fun _ => 1) ∅ fun _ => 0

abbrev TieT := ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ), FunIn p CF → Prop

abbrev PropT := ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ), FunIn p CF → ℝ → ℝ → Prop

def trivialTieCondition : TieT := fun _ _ _ => True

section Fit

open GlobalTheory.ChiGrid Formalism.L2.Host

variable {T : Type} {Lc : LevCh D T} {sc : Consts}

def lamOf (G : GridData Lc sc) : GlobalTheory.LamTie.LamDat D where
  C := Lc.C
  q0 := q0 D
  w0 := G.pl.w G.pl.v0
  c a g := cen D sc.cGap (D.eTau.symm g) (a.1 + 1)
  chi a := G.ch.chiH (a.1 + 1)

structure FieldHas (G : GridData Lc sc) {K : Type} [Field K] (e : K →+* ℂ) : Prop where

  values : ∀ i, 1 ≤ i → i ≤ D.R.m → (G.ch.chiH i).ValuesIn 0 e

  roots : ∀ v ∈ G.pl.S0, ∃ z : K, IsPrimitiveRoot z (Ideal.absNorm v.asIdeal ^ G.pl.depth sc v)

theorem lambdaGrid_apply (G : GridData Lc sc) (l : ℕ) (j a : Fin D.R.m) :
    (lamOf G).lam0 l j a = Lc.C.mu0 j * Lc.C.delAt l / G.ch.chiH (a.1 + 1) := (div_eq_mul_inv _ _).symm

theorem lamOf_hasInfQ (G : GridData Lc sc) (a : Fin D.R.m) :
    ((lamOf G).chi a).HasInfQ (embPsi D.host) fun g => ((lamOf G).c a g : ℚ) := by
  refine ⟨fun g => 2 * cen D sc.cGap (D.eTau.symm g) (a.1 + 1), fun g => by simp [lamOf], fun k => ?_⟩
  refine (G.ch.inf (a.1 + 1) (by omega) a.2 k).trans (Fintype.prod_equiv D.eTau _ _ fun τ => ?_)
  simp only [Equiv.symm_apply_apply]
  rfl

theorem lamOf_teich (G : GridData Lc sc) : (lamOf G).Teich := fun a w hw x hx =>
  G.ch.wild (a.1 + 1) (by omega) a.2 w hw x (by rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hx)

theorem FieldHas.map {G : GridData Lc sc} {K K' : Type} [Field K] [Field K'] {e' : K' →+* ℂ} (j : K →+* K')
    (h : FieldHas G (e'.comp j)) : FieldHas G e' :=
  ⟨fun i h1 h2 v hv => (h.values i h1 h2 v hv).elim fun y hy => ⟨j y, hy⟩,
    fun v hv => (h.roots v hv).elim fun z hz => ⟨j z, hz.map_of_injective j.injective⟩⟩

theorem exists_fieldHas (G : GridData Lc sc) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ FieldHas G M.val.toRingHom := by
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  have hpos : ∀ v : HeightOneSpectrum (𝓞 D.host.F), 0 < Ideal.absNorm v.asIdeal ^ G.pl.depth sc v := fun v =>
    pow_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 v.ne_bot)) _
  have h1 : ∀ a : Fin D.R.m, ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
      (G.ch.chiH (a.1 + 1)).ValuesIn 0 M.val.toRingHom := fun a => by
    obtain ⟨n, hn, hi⟩ := lamOf_hasInfQ G a
    have := GlobalTheory.T.algebraicHeckeChar_values_in_numberField D.host.F D.host.E c (D.R.Psi) (embPsi D.host) hcm _ n 0 hi fun g => by
      have h3 : (n g : ℚ) = 2 * ((lamOf G).c a g : ℚ) := hn g
      have h2 : n g = 2 * (lamOf G).c a g := by exact_mod_cast h3
      exact ⟨(lamOf G).c a g, by rw [h2]; ring⟩
    rw [Int.cast_zero, zero_div] at this
    exact this
  choose Mc hMc hMc' using h1
  choose Mr hMr hMr' using fun v : G.pl.S0 => GlobalTheory.Mem.FrameVal.exists_roots _ (hpos v)
  refine ⟨(⨆ a, Mc a) ⊔ ⨆ v, Mr v, inferInstance, fun i a b => ?_, fun v hv => ?_⟩
  · obtain ⟨i, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    exact GlobalTheory.Mem.FrameVal.valuesIn_mono (hMc' ⟨i, b⟩) ((le_iSup Mc _).trans le_sup_left)
  · have hz := Complex.isPrimitiveRoot_exp _ (hpos v).ne'
    exact ⟨⟨_, ((le_iSup Mr ⟨v, hv⟩).trans le_sup_right) (hMr' ⟨v, hv⟩ _ hz.pow_eq_one)⟩,
      IsPrimitiveRoot.of_map_of_injective (f := IntermediateField.val _) hz Subtype.val_injective⟩

def TwistedPlaceChoiceLiesOverPair (D : D7) (c : NChoice D) : Prop :=
  (∀ w, GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → D.ntw.l (c.twI w) = D.what₂.places.resChar w ∧
    (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (c.twI w) w ∨ GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.LiesUnder D (c.twI w) (D.what₂.places.conj w))) ∧
  ∀ w w', GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w' → GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.SamePair D w w' → c.Q w ≠ ∅ → c.twI w = c.twI w'

theorem TwistedPlaceChoiceLiesOverPair.inW1 {D : D7} {c : NChoice D} (h : TwistedPlaceChoiceLiesOverPair D c) {w : D.what₂.places.Pl} (hw : GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.Twisted D w) :
    D.ntw.NonzeroIndexPlace (c.twI w) :=
  (h.1 w hw).2.elim (fun h1 => ⟨w, hw, h1⟩) fun h1 => ⟨_, (GlobalTheory.IndefiniteRowSideFullHecke.GoodPairSystems.twisted_conj w).2 hw, h1⟩

structure GridFit (p : PtAt ex Csz) {CF : ℝ} (G : Grid p CF) : Prop where

  frame : ValLL0 D p.R.C

  field : FieldHas G (embLL0 D)

  setting : TwistedPlaceChoiceLiesOverPair D ex.nch

  cond : ∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (ex.nch.twI w) (ex.nch.Q w)

  powers : ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (ex.nch.twI w) : ℤ) →
    BlochKatoReduction.Gen.partC N0 (ex.nch.twI w) (ex.nch.Q w) (ex.nch.k' w) (ex.nch.psi' w ^ a) (twEps D (ex.nch.twI w))

  psi : Formalism.L2.Host.PsiChoiceCompatible D p.R.C ex.nch p.Tp

  list : GlobalTheory.LamTie.IsLamTieFull D.ntw (lamOf G)

theorem GridFit.fieldLL {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF} (h : GridFit p G) : FieldHas G D.what₂.embLL :=
  h.field.map D.LL0.val.toRingHom

theorem GridFit.of_twistAt {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF} {xd v0 rep} (h : GlobalTheory.EX.TwistAt L ex.nch xd v0 rep)
    (h1 : ValLL0 D p.R.C) (h2 : FieldHas G (embLL0 D)) (h3 : Formalism.L2.Host.PsiChoiceCompatible D p.R.C ex.nch p.Tp)
    (h4 : GlobalTheory.LamTie.IsLamTieFull D.ntw (lamOf G)) : GridFit p G := by
  classical
  obtain ⟨⟨N0, hN⟩, hall⟩ := h.2.1
  have hg := (hall N0 hN).1
  refine ⟨h1, h2, ⟨hg.1.1, fun w w' a b c _ => hg.1.2 w w' a b c⟩, fun w hw => ?_, ⟨N0, fun w hw a ha => ?_⟩, h3, h4⟩
  · obtain ⟨c, -, -, -, S, -, hS⟩ := hg.2.1 w hw
    have e := (hS 1 isCoprime_one_left).1
    exact ⟨fun P hP => (e.1 P hP).1, (Finset.disjoint_union_right.1 e.2.1).1, c⟩
  · obtain ⟨-, -, -, -, S, -, hS⟩ := hg.2.1 w hw
    have e : ∃ b : ℤ, IsCoprime b (D.ntw.l (ex.nch.twI w) : ℤ) ∧
        BlochKatoReduction.Gen.psiAt (ex.nch.sd w) (ex.nch.psi' w) ^ b = ex.nch.psi' w ^ a := by
      cases ex.nch.sd w
      · exact ⟨-a, ha.neg_left, by simp [BlochKatoReduction.Gen.psiAt]⟩
      · exact ⟨a, ha, by simp [BlochKatoReduction.Gen.psiAt]⟩
    obtain ⟨b, hb, e⟩ := e
    exact e ▸ (hS b hb).2.2.2.2.1

end Fit

abbrev FldT := ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (G : Grid p CF), G.Weil → Prop

def HasGrid (Fld : FldT) (p : PtAt ex Csz) (CF : ℝ) : Prop :=
  ∃ (G : Grid p CF) (W : G.Weil), W.Over p.R.toRealDat ∧ GridFit p G ∧ Fld p CF G W

def Fitted (Comparison₂ : TieT) : TieT := fun p CF d => GridFit p d.G ∧ Comparison₂ p CF d

def Lf (Comparison₂ : TieT) (Q : PropT) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm CH => DIVinN Fm →
  ∃ C0 : ℝ, ∀ C, C0 ≤ C → EvPt Fm fun _ _ _ p => ∀ d : FunIn p CF, Comparison₂ p CF d → Q p CF d C CH

def Ex (Fld : FldT) (Comparison₂ : TieT) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm _ => DIVinN Fm →
  EvPt Fm fun _ _ _ p => ∀ (G : Grid p CF) (W : G.Weil), W.Over p.R.toRealDat → GridFit p G → Fld p CF G W →
    ∃ d : FunIn p CF, d.G = G ∧ Comparison₂ p CF d

def MM (Comparison₂ : TieT) : Prop := Lf (Fitted Comparison₂) fun _ _ d C _ => LeafMM d.O C

def OneMap (Comparison₂ : TieT) : Prop := Lf (Fitted Comparison₂) fun p _ d _ _ =>
  ∃ ze : Tup p → _, ze p.P.A3.fam3.base3.μ0 = 1 ∧ (∀ t, ∃ n : ℕ, 0 < n ∧ ze t ^ n = 1) ∧
    LeafC (p.S false) (d.data ze ∅ fun _ => 0)

def Ker (Comparison₂ : TieT) : Prop := Lf (Fitted Comparison₂) fun _ _ d _ _ => LeafKer d.O

def FP (Comparison₂ : TieT) : Prop := Lf (Fitted Comparison₂) fun p _ d C _ => ∃ Tf dF, LeafFP (d.data (fun _ => 1) Tf dF) (p.S false).μ C p.Z.b

def IPa (Comparison₂ : TieT) : Prop := Lf (Fitted Comparison₂) fun p _ d C _ =>
  ∀ vb : Matrix (Fin d.n) (Fin ((Df p).dQ p.P.A3.fam3.base3.μ0)) _,
    vb * (Df p).Pq p.P.A3.fam3.base3.μ0 = d.V p.P.A3.fam3.base3.μ0 →
      Formalism.HN.htMap (Pi.basisFun _ (Fin ((Df p).dQ p.P.A3.fam3.base3.μ0))) ((Df p).XQ p.P.A3.fam3.base3.μ0)
        (Pi.basisFun _ (Fin d.n)) d.X' (Matrix.mulVecLin vb) ≤ d.O.bIPa C p.Z.b

def IPb : Prop := Lf trivialTieCondition fun p _ d C _ =>
  ∃ g : InfinitePlace _ → ℝ, (∀ v q, (Df p).Qp p.P.A3.fam3.base3.μ0 q ≠ ⊥ →
      g v ≤ ∑ j, Real.log ((p.S false).lam j p.P.A3.fam3.base3.μ0 q v)) ∧
    -(3 * C * d.O.f * d.O.m * (d.O.N : ℝ) ^ 2 * Real.log p.Z.b) ≤ Formalism.PairingDivisionLocalBalance.meanInf _ g

def OneSq (Comparison₂ : TieT) : Prop := Lf (Fitted Comparison₂) fun p _ d C _ => LeafOneSquare d.O (p.S false).μ C p.Z.b

def Den (Comparison₂ : TieT) : Prop := Lf (Fitted Comparison₂) fun p _ d C _ => PrimeCountingSumBound d.O C p.Z.x p.Z.b

def Int (Comparison₂ : TieT) : Prop := Lf (Fitted Comparison₂) fun p _ d C _ => LeafINT d.O C p.Z.b

def Arch (Comparison₂ : TieT) : Prop := Lf (Fitted Comparison₂) fun p _ d C _ => LeafARCH d.O C p.Z.b

def Thb (Comparison₂ : TieT) : Prop := Lf (Fitted Comparison₂) fun p _ d C _ => LeafTHB d.O C p.Z.x p.Z.b

def Wt (Comparison₂ : TieT) : Prop := Lf (Fitted Comparison₂) fun p _ d C _ => LeafWt d.O C p.Z.b

def DesH : Prop := Lf trivialTieCondition fun p _ d _ _ => leafHypothesesConst d.O ∧ LatticeConstantBound d.O p.Z.b

def RankGapBound : Prop := Lf trivialTieCondition fun p _ d C _ => DegreeAndSizeBounds d.O C p.Z.b

def RamifiedSumBound : Prop := Lf trivialTieCondition fun p _ d C _ => PrimePowerModuliSumBound d.O C p.Z.b ∧ LeafCS d.O p.Z.b

def DesPol : Prop := Lf trivialTieCondition fun p _ d C CH => LeafPol d.O C p.Z.x CH p.Z.b

def Scale : Prop := Closed FamHyp fun Fm _ => EvPt Fm fun _ _ _ p =>
  1 ≤ p.Z.x ∧ 1 ≤ Real.log p.Z.b ∧ Real.log p.Z.b + Real.log p.Z.x ≤ 3 * Real.log p.Z.b

def Bundle : Prop := ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), p.Rows →
  (Df p).WF ∧ ∃ R0 : IndefRows (Df p), R0.toIndefData = p.S false

def Fun0Fit (Fld : FldT) : Prop := ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → Closed FamHyp fun Fm CH => DIVinN Fm →
  EvPt Fm fun _ _ _ p => HasGrid Fld p CF → ∀ C, (p.S false).FUN (p.N C CH)

def FamGrid (Fld : FldT) (CF : ℝ) : FamClass := fun Fm => FamHyp Fm ∧ EvPt Fm fun _ _ _ p => HasGrid Fld p CF

theorem evPt_and {eps : ℝ} {Fm : FamP eps} {P Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (hP : EvPt Fm P) (hQ : EvPt Fm Q) : EvPt Fm fun x hx i p => P x hx i p ∧ Q x hx i p :=
  let ⟨a, ha⟩ := hP
  let ⟨b, hb⟩ := hQ
  ⟨max a b, fun x hx h i p hp => ⟨ha x hx (le_of_max_le_left h) i p hp, hb x hx (le_of_max_le_right h) i p hp⟩⟩

theorem evPt_imp {eps : ℝ} {Fm : FamP eps} {P Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Pt Fm x hx i → Prop}
    (hP : EvPt Fm P) (h : ∀ x hx i p, p.Rows → P x hx i p → Q x hx i p) : EvPt Fm Q :=
  let ⟨a, ha⟩ := hP
  ⟨a, fun x hx h' i p hp => h x hx i p hp (ha x hx h' i p hp)⟩

theorem Lf.mono {Comparison₂ Tie' : TieT} {Q Q' : PropT} (h : Lf Comparison₂ Q)
    (h' : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF) (C CH : ℝ), p.Rows → Tie' p CF d →
      Comparison₂ p CF d ∧ (Q p CF d C CH → Q' p CF d C CH)) : Lf Tie' Q' := by
  obtain ⟨CF0, h⟩ := h
  refine ⟨CF0, fun CF hCF => (h CF hCF).imp fun Fm CH _ a hN => ?_⟩
  obtain ⟨C0, a⟩ := a hN
  exact ⟨C0, fun C hC => evPt_imp (a C hC) fun _ _ _ p hp b d hd =>
    (h' p CF d C CH hp hd).2 (b d (h' p CF d C CH hp hd).1)⟩

theorem Lf.and {Comparison₂ : TieT} {Q Q' : PropT} (h : Lf Comparison₂ Q) (h' : Lf Comparison₂ Q') :
    Lf Comparison₂ fun p CF d C CH => Q p CF d C CH ∧ Q' p CF d C CH := by
  obtain ⟨a, h⟩ := h
  obtain ⟨b, h'⟩ := h'
  refine ⟨max a b, fun CF hCF => ((h CF (le_of_max_le_left hCF)).and (h' CF (le_of_max_le_right hCF))).imp
    fun Fm CH _ c hN => ?_⟩
  obtain ⟨C0, c1⟩ := c.1 hN
  obtain ⟨C1, c2⟩ := c.2 hN
  exact ⟨max C0 C1, fun C hC => evPt_imp (evPt_and (c1 C (le_of_max_le_left hC)) (c2 C (le_of_max_le_right hC)))
    fun _ _ _ _ _ e d hd => ⟨e.1 d hd, e.2 d hd⟩⟩

theorem Lf.of_noTie {Q : PropT} (h : Lf trivialTieCondition Q) (Comparison₂ : TieT) : Lf Comparison₂ Q :=
  h.mono fun _ _ _ _ _ _ _ => ⟨trivial, id⟩

theorem fun0Fit_of_leaves (Fld : FldT) (Comparison₂ : TieT) (hB : Bundle) (hS : Scale) (hE : Ex Fld Comparison₂) (h1 : MM Comparison₂) (h2 : OneMap Comparison₂)
    (h3 : Ker Comparison₂) (h4 : FP Comparison₂) (h5 : IPa Comparison₂) (h6 : IPb) (h7 : OneSq Comparison₂) (h8 : Den Comparison₂) (h9 : Int Comparison₂) (h10 : Arch Comparison₂)
    (h11 : Thb Comparison₂) (h12 : Wt Comparison₂) (h13 : DesH) (h14 : RankGapBound) (h15 : RamifiedSumBound) (h16 : DesPol) : Fun0Fit Fld := by
  obtain ⟨a, hA⟩ := Lf.and h1 <| Lf.and h2 <| Lf.and h3 <| Lf.and h4 <| Lf.and h5 <| Lf.and (Lf.of_noTie h6 _) <| Lf.and h7 <|
    Lf.and h8 <| Lf.and h9 <| Lf.and h10 <| Lf.and h11 <| Lf.and h12 <| Lf.and (Lf.of_noTie h13 _) <|
    Lf.and (Lf.of_noTie h14 _) <| Lf.and (Lf.of_noTie h15 _) (Lf.of_noTie h16 _)
  obtain ⟨b, hE⟩ := hE
  refine ⟨max a b, fun CF hCF => (((hA CF (le_of_max_le_left hCF)).and (hE CF (le_of_max_le_right hCF))).and hS).imp
    fun Fm CH _ c hN => ?_⟩
  obtain ⟨C0, c1⟩ := c.1.1 hN
  refine evPt_imp (evPt_and (evPt_and (c1 (max C0 1) (le_max_left _ _)) (c.1.2 hN)) c.2) fun x hx i p hp e hG C => ?_
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

def FunIn.ofGrid {p : PtAt ex Csz} {CF : ℝ} (G : Grid p CF) (W : G.Weil) (h : W.Over p.R.toRealDat) (n : ℕ)
    (V : ∀ t : Tup p, Matrix (Fin n) (Fin ((Df p).nV t)) D.what₂.LL) : FunIn p CF :=
  ⟨G, W, h, n, fun _ => 1, Submodule.span _ (Set.range (Pi.basisFun D.what₂.LL (Fin n))), V, fun _ _ => 1, fun _ => 0, ∅, ∅,
    fun _ _ _ => 0, fun _ => 1, fun _ => 1, fun _ _ => 1, fun _ _ _ => 1, fun _ _ _ => 0, fun _ => true, 1⟩

example (p : PtAt ex Csz) : p.Z.b = L.sc.b ∧ p.Z.x = L.sc.x := ⟨rfl, rfl⟩

example (p : PtAt ex Csz) (CF : ℝ) (G : Grid p CF) (h : GridFit p G) : ∃ z : D.what₂.LL,
    IsPrimitiveRoot z (Ideal.absNorm G.pl.v0.asIdeal ^ GlobalTheory.ChiGrid.depth0 D CF p.Z.b) := by
  simpa [GlobalTheory.ChiGrid.Places.depth] using h.fieldLL.roots _ (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))

example (p : PtAt ex Csz) (CF : ℝ) (G : Grid p CF) (h : GridFit p G) (w) (hw : TwistedAt D w) :
    Nonempty (D.ntw.abelian₂ (ex.nch.twI w)) := h.list.nonempty (h.setting.inW1 hw)

example (Fld : FldT) (h : Fun0) : Fun0Fit Fld :=
  ⟨0, fun _ _ => h.imp fun _ _ _ a hN => evPt_imp (a hN) fun _ _ _ _ _ b _ => b⟩

end GlobalTheory.BigTop.Fun

end
