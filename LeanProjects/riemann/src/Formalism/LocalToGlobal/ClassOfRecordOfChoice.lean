import Formalism.LocalToGlobal.ClassRec
import Formalism.LocalToGlobal.ThresholdSelection
import Formalism.SharpRestriction.LevelLetterCocycles.TwAllF
import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
import Formalism.SharpRestriction.PageFix
import Formalism.SharpRestriction.Divisibility.SmallFirstModulusBelowScale
import Formalism.LocalToGlobal.GroupLattices.LinkGConcreteNoKer
import Formalism.SharpRestriction.DesignExistsOfChoices
import Formalism.SharpRestriction.SmoothDesignExistence.DesignExistsDes
import Formalism.SharpRestriction.SmoothDesignExistence.AdmissibleTopsMertens
import Formalism.SharpRestriction.GlobalSchurBounds.WeightVectorSmallSharesEight
import Formalism.LocalToGlobal.Divisibility.RecBridge
import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
import Formalism.SharpRestriction.GlobalSchurBounds.LemmaBSecondBranchOfLength
import Formalism.LocalToGlobal.GlobalTheory.ConcNP
import Formalism.LocalToGlobal.HilbertRowConditions.AllJoinP
import Formalism.LocalToGlobal.GroupLattices.AdmissibleOfInclusion
import Formalism.LocalToGlobal.GroupLattices.ServiceOfTiedSelection
import Formalism.LocalToGlobal.Divisibility.RowsOfTiedSubspacesEq
import Formalism.LocalToGlobal.Divisibility.NumericScaleExponentEqExtended
import Formalism.LocalToGlobal.Divisibility.RecBridgeTied
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.MinkowskiQ
import Formalism.SharpRestriction.AdmissibleParameterJoins.DGamMink
import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT

namespace Formalism.L2.Top3

abbrev WithChN (𝒞 : FamClass) : FamClass :=
  fun Fm => 𝒞 Fm ∧ DGamDvdF Fm ∧ TameDistinctF Fm ∧ BoxesF Fm ∧ QDRowsF Fm ∧ Fm.CYL ≤ 9

theorem withSm_of_withChN {𝒞 : FamClass} {eps : ℝ} (Fm : FamP eps) (h : WithChN 𝒞 Fm) : WithSm (WithChN 𝒞) Fm :=
  ⟨h, J.dGamSmooth_of_dvd Fm h.2.1⟩

theorem designChoices_upN {𝒞 : FamClass} {C0 : ℝ} {cT : ℝ → ℝ → ℝ} (h : DesignChoices (WithTw 𝒞) C0 cT) :
    DesignChoices (WithTw (WithSm (WithChN 𝒞))) C0 cT := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps he hle K => ?_⟩
  obtain ⟨Fm, CH, C5, Cb, hc, hCH, hL, h5, hb, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := h eps he hle K
  exact ⟨Fm, CH, C5, Cb, ⟨withSm_of_withChN Fm ⟨hc.1, a8, a10, a6, a7, a13⟩, hc.2⟩, hCH, hL, h5, hb, a1, a2, a3,
    a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩

abbrev D3 (C0 : ℝ) (𝒜 : FamClass) : FamClass := Des (WithChN 𝒜) C0

theorem d3_a {C0 : ℝ} {𝒜 : FamClass} {eps : ℝ} {Fm : FamP eps} (h : D3 C0 𝒜 Fm) : 𝒜 Fm := h.1.1.1.1

theorem closed_eps_le_one (𝒞 : FamClass) : Closed 𝒞 fun {eps} _ _ => eps ≤ 1 := by
  have K : TransportedAlt := by constructor <;> exact 0
  exact ⟨1, one_pos, fun _ _ hle => ⟨K, fun _ _ _ _ => hle⟩⟩

theorem closed_of_mem {𝒞 : FamClass} {P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (h : Closed 𝒞 fun Fm CH => 𝒞 Fm → P Fm CH) :
    Closed 𝒞 P := by
  obtain ⟨a, ha, h⟩ := h
  exact ⟨a, ha, fun e he hle => let ⟨K, hK⟩ := h e he hle; ⟨K, fun Fm CH hc hL => hK Fm CH hc hL hc⟩⟩

theorem tied_families_of_choice {eps : ℝ} {Fm : FamP eps} (s : Formalism.L2.TSelF Fm) : Formalism.L2.LinkedFamiliesLevelClass Fm :=
  ⟨s.1, fun x hx h i => ⟨(s.2 x hx h i).T.toTiedDataS⟩⟩

def TupUsedF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x (_ : Fm.x1 < x), x0 ≤ x → ∀ (i : Fm.Ix x), ∀ μ : (Fm.D x i).what₂.Tup, Formalism.BasicNotions.DV.Used (Fm.D x i) μ

def EmbF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x (_ : Fm.x1 < x), x0 ≤ x → ∀ (i : Fm.Ix x),
    (NumberField.InfinitePlace.mk (Fm.D x i).what₂.embLL).embedding = (Fm.D x i).what₂.embLL

def TwAllF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    Formalism.MainNotions.TwConjAt (Fm.D x i) (Fm.ex x hx i).nch ∧
      ∃ (N0 : (Fm.D x i).ntw.Tw → ℕ) (S : ∀ (i' : (Fm.D x i).ntw.Tw) (j : ℕ) (b : Bool), Finset ((Fm.D x i).nexp.Dat i' j b)),
        Formalism.MainNotions.TwGoodAtAll (Fm.D x i) (Fm.ex x hx i).nch ⟨Formalism.MainNotions.twE Fm x hx i, N0, S⟩

def Duty {eps : ℝ} (Fm : FamP eps) : Prop :=
  PageFix Fm ∧ PageWin Fm ∧ Formalism.MainNotions.DIV.Align.SmallFirstModulusBelowScale Fm ∧ TameDistinctF Fm ∧ ChosenWall Fm ∧ TupUsedF Fm ∧ TwAllF Fm

theorem class_duties_of_choice {eps : ℝ} {Fm : FamP eps} (s : Formalism.L2.TSelF Fm) (h : Duty Fm) : Formalism.L2.LinkedFamiliesAligned Fm :=
  ⟨⟨tied_families_of_choice s, h.1⟩, h.2.2.1, h.2.2.2.1⟩

theorem class_of_record_of_choice {eps : ℝ} {Fm : FamP eps} (s : Formalism.L2.TSelF Fm) (h : Formalism.L2.LinkedFamiliesAligned Fm) : Formalism.L2.LayerTwoFamilyClass Fm :=
  ⟨s.tiedRec, h⟩

theorem real_place_second_layer_conditions_of_choice {eps : ℝ} {Fm : FamP eps} (s : Formalism.L2.TSelF Fm)
    (hχ : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x) (h : s.1 ≤ x), x0 ≤ x → ∀ (i : Fm.Ix x) u, ChiFin0 ((s.2 x hx h i).T.cols.forms u)) :
    RealPlaceSecondLayerConditions Fm := by
  obtain ⟨x0, hχ⟩ := hχ
  refine ⟨max (max x0 s.1) (Fm.x1 + 1), fun x hx i => ?_⟩
  have h1 : Fm.x1 < x := by have := le_trans (le_max_right _ _) hx; linarith
  have hs : s.1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have h0 : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  exact ⟨(s.2 x h1 hs i).T.theta.real, (s.2 x h1 hs i).T.cols, fun u => hχ x h1 hs h0 i u⟩

open Formalism.L2.DIV in

structure BridgeRest {eps : ℝ} (Fm : FamP eps) (Rw : Σ' x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ i : Fm.Ix x, DivisionRowsFace (Fm.L x i))
    (Cabs CH : ℝ) : Prop where
  pkg : DIVinN Fm → ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (h : Rw.1 ≤ x) (i : Fm.Ix x), Nonempty (DivisionPackageFace (Rw.2 x hx h i) C Cabs)
  cut : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∀ μ, Formalism.BasicNotions.DV.Used (Fm.D x i) μ → Formalism.L2.G.ServJoint.CutUp (Fm.D x i) μ
  c3 : ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Compl3 (Fm.L x i) (Fm.X x i) Fm.Csz C
  hh : DIVinN Fm → Formalism.MainNotions.LocalQuadraticParts.FrameNumberBoundFamily Fm Fm.Csz CH
  c5 : Formalism.MainNotions.LocalQuadraticParts.ComplementCountFamily Fm
  bu : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).BuRational
  rr : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).RRFull
  la : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, 0 ≤ (Fm.L x i).La

open Formalism.L2.DIV in

theorem BridgeRest.toRows {eps : ℝ} {Fm : FamP eps} {Rw : Σ' x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ i : Fm.Ix x, DivisionRowsFace (Fm.L x i)}
    {Cabs CH : ℝ} (r : BridgeRest Fm Rw Cabs CH)
    (a : ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.LocalQuadraticParts.adm2 (Fm.D x i) (Fm.L x i))
    (c2 : Formalism.MainNotions.LocalQuadraticParts.ComplementTwoFamily Fm) :
    BridgeRowsF Fm Rw Cabs CH where
  pkg := r.pkg
  adm2 := by
    obtain ⟨x0, a⟩ := a
    refine ⟨max x0 (Fm.x1 + 1), fun x hx i => a x (le_trans (le_max_left _ _) hx) ?_ i⟩
    have := le_trans (le_max_right _ _) hx
    linarith
  cut := r.cut
  c3 := r.c3
  hh := r.hh
  c2 := c2
  c5 := r.c5
  bu := r.bu
  rr := r.rr
  la := r.la

abbrev SelP (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    {P : Formalism.L2.Rows.RowSideFamily (Fm.ex x hx i) // Formalism.L2.Rows.RowSideDetermined ((sel Fm hc).2 x hx h i).T P ∧ Formalism.L2.Rows.RowsHold0_3 P}

abbrev SelDH (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    {p : ℕ × ℕ // (Fm.D x i).s.Del = (p.1 : ℚ) ∧ (Fm.L x i).etaSz = ((Fm.D x i).R.m : ℝ) * (p.2 : ℝ)}

def RwOf {𝒜 : FamClass} {C0 : ℝ} (sel : Formalism.L2.TSel 𝒜) (selP : SelP 𝒜 sel) (selDH : SelDH 𝒜 sel) :
    ∀ {eps : ℝ} (Fm : FamP eps), D3 C0 𝒜 Fm → Σ' x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ i : Fm.Ix x, Formalism.L2.DIV.DivisionRowsFace (Fm.L x i) :=
  fun Fm hc => ⟨(sel Fm (d3_a hc)).1, fun x hx h i =>
    let P := selP Fm (d3_a hc) x hx h i
    let p := selDH Fm (d3_a hc) x hx h i
    Formalism.L2.DIV.DivisionRowsFace.ofCompatibleData ((sel Fm (d3_a hc)).2 x hx h i).T P.1 P.2.1 P.2.2
      (Formalism.L2.DIV.ZscOfNum3 P.1.A3 P.1.P0 P.1.ψ0 (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) p.1.1 p.1.2) (Equiv.refl _)
        (Fm.L x i).Nc)⟩

theorem complement_two_of_items {eps : ℝ} {Fm : FamP eps} (h : Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm) : Formalism.MainNotions.LocalQuadraticParts.ComplementTwoFamily Fm := by
  obtain ⟨C, x0, h⟩ := Formalism.MainNotions.WeightDegreeSizes.secondComplement_family_of_inputs Fm h
  refine ⟨C, max x0 (Fm.x1 + 1), fun x hx i => h x (le_trans (le_max_left _ _) hx) ?_ i⟩
  have := le_trans (le_max_right _ _) hx
  linarith

section ColChoice

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {Kc : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX}

structure ColChoice (P : Formalism.L2.Rows.RowSideFamily ex) where
  X : Formalism.L2.Col.Fields
  e : X.Tau → (X.E →+* D.what₂.LL)
  c : Formalism.L2.DIV.ColRec3 (Formalism.L2.DIV.fieldsLL D X e) P.A3 P.Ps P.ψs
  Sp : ∀ Zs : Formalism.L2.Indef.DefSub P.A3.fam3.amb3, Formalism.L2.Indef.SPer (c.face Zs)
  tie : Formalism.L2.DIV.ColTie3 P X e c Sp

end ColChoice

abbrev SelC (𝒜 : FamClass) (sel : Formalism.L2.TSel 𝒜) (selP : SelP 𝒜 sel) :=
  ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
    ColChoice (selP Fm hc x hx h i).1

def RtOf {𝒜 : FamClass} {C0 : ℝ} (sel : Formalism.L2.TSel 𝒜) (selP : SelP 𝒜 sel) (selDH : SelDH 𝒜 sel) (selC : SelC 𝒜 sel selP) :
    ∀ {eps : ℝ} (Fm : FamP eps), D3 C0 𝒜 Fm → Σ' x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ i : Fm.Ix x, Formalism.L2.DIV.DivisionRowsColumns (Fm.L x i) :=
  fun Fm hc => ⟨(sel Fm (d3_a hc)).1, fun x hx h i =>
    let P := selP Fm (d3_a hc) x hx h i
    let p := selDH Fm (d3_a hc) x hx h i
    let c := selC Fm (d3_a hc) x hx h i
    Formalism.L2.DIV.DivisionRowsColumns.split_model_to_place_model P.1 P.2.2 c.X c.e c.c c.Sp
      (Formalism.L2.DIV.ZscOfNum3 P.1.A3 P.1.P0 P.1.ψ0 (Formalism.L2.DIV.ofRecord (Fm.D x i) (Fm.L x i) p.1.1 p.1.2) (Equiv.refl _)
        (Fm.L x i).Nc)⟩

open Formalism.L2.DIV in

structure BridgeRestT {eps : ℝ} (Fm : FamP eps) (Rt : Σ' x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ i : Fm.Ix x, DivisionRowsColumns (Fm.L x i))
    (Cabs CH : ℝ) : Prop where
  pkg : DIVinN Fm → ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (h : Rt.1 ≤ x) (i : Fm.Ix x), Nonempty (DivisionPackageColumns (Rt.2 x hx h i) C Cabs)
  cut : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∀ μ, Formalism.BasicNotions.DV.Used (Fm.D x i) μ → Formalism.L2.G.ServJoint.CutUp (Fm.D x i) μ
  c3 : ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, Compl3 (Fm.L x i) (Fm.X x i) Fm.Csz C
  hh : DIVinN Fm → Formalism.MainNotions.LocalQuadraticParts.FrameNumberBoundFamily Fm Fm.Csz CH
  c5 : Formalism.MainNotions.LocalQuadraticParts.ComplementCountFamily Fm
  bu : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).BuRational
  rr : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).RRFull
  la : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, 0 ≤ (Fm.L x i).La

open Formalism.L2.DIV in
theorem BridgeRestT.toRows {eps : ℝ} {Fm : FamP eps} {Rt : Σ' x0 : ℝ, ∀ x, Fm.x1 < x → x0 ≤ x → ∀ i : Fm.Ix x, DivisionRowsColumns (Fm.L x i)}
    {Cabs CH : ℝ} (r : BridgeRestT Fm Rt Cabs CH)
    (a : ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, Formalism.MainNotions.LocalQuadraticParts.adm2 (Fm.D x i) (Fm.L x i))
    (c2 : Formalism.MainNotions.LocalQuadraticParts.ComplementTwoFamily Fm) :
    BridgeRowsT Fm Rt Cabs CH where
  pkg := r.pkg
  adm2 := by
    obtain ⟨x0, a⟩ := a
    refine ⟨max x0 (Fm.x1 + 1), fun x hx i => a x (le_trans (le_max_left _ _) hx) ?_ i⟩
    have := le_trans (le_max_right _ _) hx
    linarith
  cut := r.cut
  c3 := r.c3
  hh := r.hh
  c2 := c2
  c5 := r.c5
  bu := r.bu
  rr := r.rr
  la := r.la

end Formalism.L2.Top3

end
