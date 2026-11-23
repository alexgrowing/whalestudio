import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AllRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.APerTw
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHostDatumOfPlaceDataStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostPlacesRayFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedArgsColumnHeq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.SelSideW

theorem plMap_refl {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) :
    Formalism.L2.Host.CT.plMap (RingEquiv.refl E) P = P := by
  ext x
  exact Formalism.L2.Host.CT.mem_plMap (RingEquiv.refl E) P x

open Classical in

theorem image_refl {E : Type} [Field E] [NumberField E] (f : E ≃+* E) (hf : f = RingEquiv.refl E)
    (S : Finset (HeightOneSpectrum (𝓞 E))) : S.image (Formalism.L2.Host.CT.plMap f) = S := by
  subst hf
  rw [show Formalism.L2.Host.CT.plMap (RingEquiv.refl E) = id from funext plMap_refl, Finset.image_id]

open Classical in

theorem qe_image_congr {D : D7} {X X' : Formalism.L2.Col.Fields} (hX : X = X') {s : Formalism.L2.Ker.Seam D X} {s' : Formalism.L2.Ker.Seam D X'}
    (hs : HEq s s') {S S' : Set ℕ} (hS : S = S') {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {sel' : HeightOneSpectrum (𝓞 X'.F) → HeightOneSpectrum (𝓞 X'.E)} (hsel : HEq sel sel')
    {tup : D.what₂.Tup → Formalism.L2.DIV.Tup X.F X.E X.K S} {tup' : D.what₂.Tup → Formalism.L2.DIV.Tup X'.F X'.E X'.K S'} (htup : HEq tup tup')
    (μ : D.what₂.Tup) :
    (Col.QE sel (tup μ : DIV.Chr X.F X.E X.K)).image (Host.CT.plMap s.iE) =
      (Col.QE sel' (tup' μ : DIV.Chr X'.F X'.E X'.K)).image (Host.CT.plMap s'.iE) := by
  subst hX
  subst hS
  cases hs
  cases hsel
  cases htup
  rfl

open Classical in

theorem qe_image_std {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt)
    {L : SizeData₂ (w.D Z)} {hT : GatTies (w.D Z)} {Gi : Formalism.MainNotions.G.Inst (w.D Z) L} {Gl : Formalism.MainNotions.G.LatInst (w.D Z)}
    {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.D Z)} {cX : ExtraC} {ex : Extra (w.D Z) L hT Gi Gl Kc Yd cX}
    (t : Formalism.L2.Ker.KerEntTied ex) (h : TC.StdKer w.I w.l Z t) (μ : (w.D Z).what₂.Tup) :
    (Col.QE t.sel (t.tup μ : DIV.Chr t.X.F t.X.E t.X.K)).image (Host.CT.plMap t.seam.iE) = w.I.Q μ := by
  rw [qe_image_congr h.X_eq h.seam h.S h.sel h.tup μ]
  exact image_refl _ rfl _

end GlobalTheory.Mem.R3.SelSideW

namespace GlobalTheory.Mem.R3.SelSideW

theorem de_pin {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx} (q : WPt p.s K) (v)
    (h : (((q.w.D q.Z).host.pde : ℕ) : 𝓞 (q.w.D q.Z).host.E) ∈ (q.core.a.Pq v).asIdeal) :
    (q.core.a.Pq v).under (𝓞 (q.w.D q.Z).host.K) = q.x.pin.d3b.pK := by
  have hm : q.core.a.Pq v ∈ Set.range q.w.I.sel := q.core.sel ▸ Set.mem_range_self v
  obtain ⟨v', hv'⟩ := hm
  have ha := q.x.pin.above v'
  have hv : OverPF q.B.host q.B.host.pde v' := by
    unfold OverPF
    have h1 : (q.w.I.sel v').asIdeal.comap (algebraMap (𝓞 q.B.host.F) (𝓞 q.B.host.E)) = v'.asIdeal := by
      have := (Set.Finite.mem_toFinset _).1 ha
      first | exact this | exact this.symm | exact congrArg HeightOneSpectrum.asIdeal this
    rw [← h1, Ideal.mem_comap, map_natCast, hv']
    exact h
  have := (q.x.pin.d3b.P_mem v' hv).2
  rw [← q.x.pin.selectedPlacesAgree.1 v' hv] at this
  rw [← hv']
  exact this

theorem de_pin' {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Prm hL} {K : Ctx} (q : WPt p.s K) (v)
    (h : (((q.w.D q.Z).host.pde' : ℕ) : 𝓞 (q.w.D q.Z).host.E) ∈ (q.core.a.Pq v).asIdeal) :
    (q.core.a.Pq v).under (𝓞 (q.w.D q.Z).host.K) = q.x.pin.d3b.pK' := by
  have hm : q.core.a.Pq v ∈ Set.range q.w.I.sel := q.core.sel ▸ Set.mem_range_self v
  obtain ⟨v', hv'⟩ := hm
  have ha := q.x.pin.above v'
  have hv : OverPF q.B.host q.B.host.pde' v' := by
    unfold OverPF
    have h1 : (q.w.I.sel v').asIdeal.comap (algebraMap (𝓞 q.B.host.F) (𝓞 q.B.host.E)) = v'.asIdeal := by
      have := (Set.Finite.mem_toFinset _).1 ha
      first | exact this | exact this.symm | exact congrArg HeightOneSpectrum.asIdeal this
    rw [← h1, Ideal.mem_comap, map_natCast, hv']
    exact h
  have := (q.x.pin.d3b.P'_mem v' hv).2
  rw [← q.x.pin.selectedPlacesAgree.2 v' hv] at this
  rw [← hv']
  exact this

open Classical in
set_option maxHeartbeats 4000000 in

theorem selected_side_realization : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (Γ : GeoP) (p : Prm hL), p = prmR N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : Formalism.L2.RecT q.O.ex), RecPinE q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.sat.P → HEq sS q.sat.S → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → ∀ (y : RealIn x R (sS.toSTiesR R)) (r : RecIn y) (HD : Formalism.L2.HostDatumC R.T.toTiedDataS), HD.d3b = q.x.pin.d3b → Formalism.L2.SelSideRT R (divisionPairOfAdelicFormsFaceColumnsData x) (realTOf y) (realRecOf r) HD q.core.a.Pq := by
  intro _ _ _ _ _ _ _ _ _ hL N Γ p hp _ K q _ _ R hR sP sS _ _ a x ax y r HD hHD
  have hQ := qe_image_std q.w q.Z R.T.ker hR.k.std
  have hsel : Set.range q.core.a.Pq = Set.range q.w.I.sel := q.core.sel
  have hlev0 := (twArgs_lev K q.B q.f q.T q.w q.Z q.x.Wt _ _ _ _ _ _ _ q.O.ex q.x.what₂ a).2.2.1
  have hlev : ∀ μ, Formalism.IndefR.RecTie.Used0 (q.w.st q.Z).toD7 μ → HEq (x.R.Q (x.Y.tupT μ)) (q.w.I.Q μ) := by
    have key : ∀ x' : TwIn q.O.ex, a.x = x' →
        ∀ μ, Formalism.IndefR.RecTie.Used0 (q.w.st q.Z).toD7 μ → HEq (x'.R.Q (x'.Y.tupT μ)) (q.w.I.Q μ) := by
      rintro x' rfl μ hμ
      exact (hlev0 μ hμ).1
    exact key x (eq_of_heq ax)
  refine ⟨⟨q.core.a.Pq_over, ?_⟩, ?_, ?_, ?_⟩
  · intro μ P hP P' hC
    have hP'eq : P' = Host.CT.plMap R.T.ker.seam.iE P :=
      HeightOneSpectrum.ext (hC.trans (SelJ.carried_plMap R.T.ker.seam P).symm)
    subst hP'eq
    have hm : Host.CT.plMap R.T.ker.seam.iE P ∈ q.w.I.Q μ := hQ μ ▸ Finset.mem_image_of_mem _ hP
    obtain ⟨v, -, hv, -⟩ := q.w.I.exists_of_mem_Q hm
    rw [hsel]
    exact ⟨v, hv⟩
  · intro μ hμ
    rw [hQ μ]
    exact (eq_of_heq (hlev μ hμ)).symm
  · intro v hv
    rw [hHD]
    exact de_pin q v hv
  · intro v hv
    rw [hHD]
    exact de_pin' q v hv

end GlobalTheory.Mem.R3.SelSideW
