import Formalism.LocalToGlobal.ClassOfRecordOfChoice
import Formalism.LocalToGlobal.IndefiniteReal.TrISepWith
import Formalism.LocalToGlobal.IndefiniteReal.RealTP
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NMjT
import Formalism.LocalToGlobal.SelSide
import Formalism.LocalToGlobal.SelSideN
import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt
import Formalism.LocalToGlobal.KernelLattices.KerPins
import Formalism.LocalToGlobal.KernelLattices.KerPinsU
import Formalism.LocalToGlobal.KernelLattices.KerMtPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Formalism.LocalToGlobal.GroupLattices.JointServices.Cut
import Formalism.LocalToGlobal.Divisibility.RecBridgeSel
import Formalism.SharpRestriction.Divisibility.HookProducts.Compl3Record

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT

namespace Formalism.L2.Top4

open Formalism.L2.Top3

abbrev BaseLevelCompatibleSelection (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    {P : Formalism.L2.Rows.RowSideFamily (Fm.ex x hx i) // Formalism.L2.Rows.RowSideDetermined ((sel Fm hc).2 x hx h i).T P}

section SelTieS

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

structure SelTie (R : Formalism.L2.RecT ex) where
  Pq : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers (NumberField.maximalRealSubfield D.host.E)) →
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.E)
  side : Formalism.L2.SelSidePq R Pq
  pqN : Formalism.L2.PqN R Pq
  gside : Formalism.L2.GSide R
  ker : Formalism.L2.KerTupTie R
  mu0 : Formalism.L2.KerMu0Tie R

  pins : Formalism.L2.Ker.KerPinsU R

  mtTw : R.T.ker.MtTwTie

  beOn : ∀ u, Formalism.L2.Ker.BeOnTie D u

end SelTieS

abbrev SelT (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x), SelTie ((sel Fm hc).2 x hx h i)

abbrev ColumnCompatibleSelection (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) (selP : BaseLevelCompatibleSelection 𝒜 sel) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    Formalism.L2.DIV.SquareIntegrableColumnsCompatible ((sel Fm hc).2 x hx h i).T (selP Fm hc x hx h i).1

abbrev SelS (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    Formalism.L2.SG.SpectralTiesReal.STiesR ((sel Fm hc).2 x hx h i)

def ZscAt {𝒜 : FamClass} (sel : Formalism.L2.TSel 𝒜) (selP : BaseLevelCompatibleSelection 𝒜 sel) (selDH : SelDH 𝒜 sel) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm)
    (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x) :
    Formalism.L2.Indef.DefSub (selP Fm hc x hx h i).1.A3.fam3.amb3 → Formalism.L2.Indef.IndefScale (selP Fm hc x hx h i).1.A3.fam3.base3 :=
  fun Zs =>
    let z := Formalism.L2.DIV.ZscOfNum3 (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0
      (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) (selDH Fm hc x hx h i).1.1 (selDH Fm hc x hx h i).1.2) (Equiv.refl _) (Fm.L x i).Nc Zs
    { z with l6m := fun j => z.l6m j - Fm.Csz * z.l6u, l6u := 0 }

structure KsChoice (D : D7) where
  Ks : Type
  [f : Field Ks]
  [n : NumberField Ks]
  [a : Algebra Ks D.what₂.LL]

attribute [instance] KsChoice.f KsChoice.n KsChoice.a

abbrev SelK (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x), KsChoice (Fm.D x i)

abbrev IndefiniteRealisationChoice (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) (selS : SelS 𝒜 sel) (selP : BaseLevelCompatibleSelection 𝒜 sel) (selDH : SelDH 𝒜 sel)
    (selC : ColumnCompatibleSelection 𝒜 sel selP) (selK : SelK 𝒜 sel) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    Formalism.IndefR.RealT ((sel Fm hc).2 x hx h i) (selP Fm hc x hx h i).1 (selC Fm hc x hx h i).c.face (selC Fm hc x hx h i).Sp
      (ZscAt sel selP selDH Fm hc x hx h i) (selS Fm hc x hx h i) (selK Fm hc x hx h i).Ks

def PrimAll {𝒜 : FamClass} (sel : Formalism.L2.TSel 𝒜) {selS : SelS 𝒜 sel} {selP : BaseLevelCompatibleSelection 𝒜 sel} {selDH : SelDH 𝒜 sel}
    {selC : ColumnCompatibleSelection 𝒜 sel selP} {selK : SelK 𝒜 sel} (selI : IndefiniteRealisationChoice 𝒜 sel selS selP selDH selC selK) : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    Formalism.IndefR.Links.PrimRows3 (selI Fm hc x hx h i).Rl (selI Fm hc x hx h i).F ∧ (selP Fm hc x hx h i).1.A3.fam3.TypesSep3

theorem rowsHold0_of {𝒜 : FamClass} {sel : Formalism.L2.TSel 𝒜} {selS : SelS 𝒜 sel} {selP : BaseLevelCompatibleSelection 𝒜 sel} {selDH : SelDH 𝒜 sel}
    {selC : ColumnCompatibleSelection 𝒜 sel selP} {selK : SelK 𝒜 sel} {selI : IndefiniteRealisationChoice 𝒜 sel selS selP selDH selC selK} (hPA : PrimAll sel selI)
    {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x) :
    Formalism.L2.Rows.RowsHold0_3 (selP Fm hc x hx h i).1 := by
  obtain ⟨hP, hsep⟩ := hPA Fm hc x hx h i
  exact (selI Fm hc x hx h i).rowsHold0 (selC Fm hc x hx h i).ok1 hsep hP

def RkOf {𝒜 : FamClass} (sel : Formalism.L2.TSel 𝒜) (selS : SelS 𝒜 sel) (selP : BaseLevelCompatibleSelection 𝒜 sel) (selDH : SelDH 𝒜 sel) (selC : ColumnCompatibleSelection 𝒜 sel selP)
    (selK : SelK 𝒜 sel) (selI : IndefiniteRealisationChoice 𝒜 sel selS selP selDH selC selK) (hPA : PrimAll sel selI) :
    ∀ {eps : ℝ} (Fm : FamP eps), D3 3 𝒜 Fm →
      Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, Formalism.L2.DIV.DivisionRowsKernel (Fm.ex x hx i) :=
  fun Fm hc => ⟨(sel Fm (d3_a hc)).1, fun x hx h i =>
    (selC Fm (d3_a hc) x hx h i).toK (rowsHold0_of hPA Fm (d3_a hc) x hx h i) (ZscAt sel selP selDH Fm (d3_a hc) x hx h i)⟩

def EvSel {𝒜 : FamClass} (sel : Formalism.L2.TSel 𝒜) {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm)
    (Q : ∀ (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x), Prop) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x), x0 ≤ x → ∀ i : Fm.Ix x, Q x hx h i

section At

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX} {Rc : Formalism.L2.RecT ex} {P : Formalism.L2.Rows.RowSideFamily ex}
  {Dcf : ∀ Zs : Formalism.L2.Indef.DefSub P.A3.fam3.amb3, Formalism.L2.Indef.DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs, Formalism.L2.Indef.SPer (Dcf Zs)} {Zscf : Formalism.L2.Indef.DefSub P.A3.fam3.amb3 → Formalism.L2.Indef.IndefScale P.A3.fam3.base3}
  {S : Formalism.L2.SG.SpectralTiesReal.STiesR Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure RowsAt4 (Q : Formalism.IndefR.RealT Rc P Dcf Spf Zscf S Ks) (C CH : ℝ) (hN hO : Prop) : Prop where

  w1 : ∀ w, (Q.Rl.toCx3 Q.F).W1 Q.F.cr (Q.Rl.num Q.F C CH) w → w ∈ Q.Rl.twPl

  covol : ((Q.Rl.toCx3 Q.F).data Q.F.cr false).L3 (Q.Rl.num Q.F C CH)

  onto : hN → ((Q.Rl.toCx3 Q.F).data Q.F.cr false).ON (Q.Rl.num Q.F C CH)

  lamLow : hO → ((Q.Rl.toCx3 Q.F).data Q.F.cr true).L6 (Q.Rl.num Q.F C CH)
  seeIso : (Q.Rl.toCx3 Q.F).SEEIso Q.sEE
  miStar : (Q.Rl.toCx3 Q.F).MIstar2 (Q.F.eV (Q.Rl.toCx3 Q.F).zs) Q.sEE

  fun0 : hN → ((Q.Rl.toCx3 Q.F).data Q.F.cr false).FUN (Q.Rl.num Q.F C CH)

  pass : Formalism.IndefR.Links.PassIn3 Q.Rl Q.F C CH

  kap : Formalism.L2.Rows.RowsHoldKap3 P

end At

def RowsAtSel {𝒜 : FamClass} (sel : Formalism.L2.TSel 𝒜) {selS : SelS 𝒜 sel} {selP : BaseLevelCompatibleSelection 𝒜 sel} {selDH : SelDH 𝒜 sel}
    {selC : ColumnCompatibleSelection 𝒜 sel selP} {selK : SelK 𝒜 sel} (selI : IndefiniteRealisationChoice 𝒜 sel selS selP selDH selC selK)
    (DefRows4 : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x) (C CH : ℝ), Prop)
    (OneMapRow : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x), Prop)
    {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (CH : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ EvSel sel Fm hc fun x hx h i =>
    RowsAt4 (selI Fm hc x hx h i) C CH (DIVinN Fm) (OneMapRow Fm hc x hx h i) ∧ DefRows4 Fm hc x hx h i C CH

def Wire4 {𝒜 : FamClass} (sel : Formalism.L2.TSel 𝒜) (selS : SelS 𝒜 sel) (selP : BaseLevelCompatibleSelection 𝒜 sel) (selDH : SelDH 𝒜 sel) (selC : ColumnCompatibleSelection 𝒜 sel selP) (selK : SelK 𝒜 sel)
    (selI : IndefiniteRealisationChoice 𝒜 sel selS selP selDH selC selK) (hPA : PrimAll sel selI)
    (DefRows4 : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x) (C CH : ℝ), Prop)
    (OneMapRow : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x), Prop)
    (Cabs : ℝ) : Prop :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : D3 3 𝒜 Fm) (CH : ℝ), 0 ≤ Fm.Csz → DGamSize Fm →
    RowsAtSel sel selI DefRows4 OneMapRow Fm (d3_a hc) CH → EvSel sel Fm (d3_a hc) (OneMapRow Fm (d3_a hc)) →
    (∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).BuRational) → DIVinN Fm →
    ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (h : (RkOf sel selS selP selDH selC selK selI hPA Fm hc).1 ≤ x) (i : Fm.Ix x),
      Nonempty (Formalism.L2.DIV.DivisionPackageKernel ((RkOf sel selS selP selDH selC selK selI hPA Fm hc).2 x hx h i) C Cabs)

open Formalism.L2.DIV in

structure RemainingDivisionBounds {eps : ℝ} (Fm : FamP eps) (Cabs CH : ℝ) : Prop where

  hh : Formalism.MainNotions.LocalQuadraticParts.ComplementTwoFamily Fm → DIVinN Fm → Formalism.MainNotions.LocalQuadraticParts.FrameNumberBoundFamily Fm Fm.Csz CH
  bu : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).BuRational
  rr : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).RRFull
  la : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, 0 ≤ (Fm.L x i).La

theorem cut_of_stable {eps : ℝ} {Fm : FamP eps}
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (μ : (Fm.D x i).what₂.Tup) (a : NumberField.RingOfIntegers (Fm.D x i).what₂.LL),
      ∀ y ∈ ((Fm.D x i).what₂.Mtilde μ).carrier, (Fm.D x i).what₂.embLL (a : (Fm.D x i).what₂.LL) • y ∈ ((Fm.D x i).what₂.Mtilde μ).carrier) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∀ μ, Formalism.BasicNotions.DV.Used (Fm.D x i) μ → Formalism.L2.G.ServJoint.CutUp (Fm.D x i) μ := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx i μ _ => Formalism.L2.G.ServJoint.cutUp_of_stable _ μ fun a y hy => h x hx i μ a y hy⟩

theorem cut_of_otie {eps : ℝ} {Fm : FamP eps} (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Formalism.L2.G.ServJoint.OTie (Fm.D x i)) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∀ μ, Formalism.BasicNotions.DV.Used (Fm.D x i) μ → Formalism.L2.G.ServJoint.CutUp (Fm.D x i) μ := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx i μ hμ => Formalism.L2.G.ServJoint.cutUpOfOTie _ (h x hx i) μ hμ⟩

open Formalism.L2.DIV in
theorem RemainingDivisionBounds.toRows {eps : ℝ} {Fm : FamP eps} {Rt : Σ' x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, DivisionRowsKernel (Fm.ex x hx i)}
    {Cabs CH : ℝ} (r : RemainingDivisionBounds Fm Cabs CH)
    (pkg : DIVinN Fm → ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (h : Rt.1 ≤ x) (i : Fm.Ix x), Nonempty (DivisionPackageKernel (Rt.2 x hx h i) C Cabs))
    (cut : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∀ μ, Formalism.BasicNotions.DV.Used (Fm.D x i) μ → Formalism.L2.G.ServJoint.CutUp (Fm.D x i) μ)
    (a : ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.LocalQuadraticParts.adm2 (Fm.D x i) (Fm.L x i))
    (c2 : Formalism.MainNotions.LocalQuadraticParts.ComplementTwoFamily Fm) (c5 : Formalism.MainNotions.LocalQuadraticParts.ComplementCountFamily Fm) :
    BridgeRowsK Fm Rt Cabs CH where
  pkg := pkg
  adm2 := by
    obtain ⟨x0, a⟩ := a
    refine ⟨max x0 (Fm.x1 + 1), fun x hx i => a x (le_trans (le_max_left _ _) hx) ?_ i⟩
    have := le_trans (le_max_right _ _) hx
    linarith
  cut := cut
  c3 := Formalism.MainNotions.DIV.HookProducts.RBCompl3.rbCompl3 Fm
  hh := r.hh c2
  c2 := c2
  c5 := c5
  bu := r.bu
  rr := r.rr
  la := r.la

end Formalism.L2.Top4

end
