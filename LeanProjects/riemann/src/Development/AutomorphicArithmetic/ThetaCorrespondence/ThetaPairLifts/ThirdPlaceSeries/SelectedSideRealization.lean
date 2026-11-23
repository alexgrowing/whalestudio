import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SelectedSideRealizationHolds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealRecOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ToSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostDatumS
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SelSideRT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SelSidePq
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3
namespace GlobalTheory.Mem.R3.SelSideW
end GlobalTheory.Mem.R3.SelSideW
namespace GlobalTheory.Mem.R3.SelSideW
theorem de_pin_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) (v)
    (h : (((q.w.D q.Z).host.pde : ℕ) : 𝓞 (q.w.D q.Z).host.E) ∈ (q.core_data_of_point.a.Pq v).asIdeal) :
    (q.core_data_of_point.a.Pq v).under (𝓞 (q.w.D q.Z).host.K) = q.x.pin.d3b.pK := by
  have hm : q.core_data_of_point.a.Pq v ∈ Set.range q.w.I.sel := q.core_data_of_point.sel ▸ Set.mem_range_self v
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
theorem under_Pq_eq_pK'_of_pde'_mem {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) (v)
    (h : (((q.w.D q.Z).host.pde' : ℕ) : 𝓞 (q.w.D q.Z).host.E) ∈ (q.core_data_of_point.a.Pq v).asIdeal) :
    (q.core_data_of_point.a.Pq v).under (𝓞 (q.w.D q.Z).host.K) = q.x.pin.d3b.pK' := by
  have hm : q.core_data_of_point.a.Pq v ∈ Set.range q.w.I.sel := q.core_data_of_point.sel ▸ Set.mem_range_self v
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
theorem selected_side_realization_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.NT.RayField → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (Γ : GeoP) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), p = _root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none Γ → (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt p.s K), (∀ X : GlobalTheory.Mem.Stages, K.Over X.B.toPre → HostHyp X.toD7 ∧ X.toD7.host.F = maximalRealSubfield X.toD7.host.E ∧ (∀ i, IsFDiag (Wc X.toD7 i) ∧ IsFDiag (Vc X.toD7 i)) ∧ (∀ i, (Vc X.toD7 i).IsPosDef) ∧ (∀ j, Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Formalism.IndefR.Seed.FrmC.StdLat (X.toD7.sp.W j))) ∧ Formalism.IndefR.Seed.FrmC.StdLat X.toD7.sp.X' ∧ (∀ i, (∀ a b, (Vc X.toD7 i).hT ((Vc X.toD7 i).frame a) ((Vc X.toD7 i).frame b) = if a = b then 1 else 0) ∧ (Vc X.toD7 i).L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range (Vc X.toD7 i).frame)) ∧ ((∀ a b, X.toD7.sp.X'.hT (X.toD7.sp.X'.frame a) (X.toD7.sp.X'.frame b) = if a = b then 1 else 0) ∧ X.toD7.sp.X'.L0 = Submodule.span (𝓞 X.toD7.host.E) (Set.range X.toD7.sp.X'.frame))) → GlobalTheory.CuspMult.MultEq q.x.what₂.r.z.R.toRealDat → ∀ (R : _root_.Formalism.L2.RecTAlt q.O.ex), _root_.GlobalTheory.Mem.Top.Bl.RecordCompatibleExtended q R → ∀ (sP : GlobalTheory.Mem.SRe.SPack (q.w.D q.Z) fun u => (R.T.cols.forms u).to0) (sS : GlobalTheory.Mem.SRe.SRest sP), HEq sP q.saturationAtWeightedPoint.P → HEq sS q.saturationAtWeightedPoint.S → ∀ (a : TwArgs q.O.ex q.x.what₂) (x : TwIn q.O.ex), HEq a.x x → ∀ (y : _root_.GlobalTheory.Mem.R3.RealInAlt x R (sS.toRealSpectralMatching R)) (r : _root_.GlobalTheory.Mem.R3.RecursiveInput y) (HD : _root_.Formalism.L2.HostDatumWithTies R.T.toTiedDataS), HD.d3b = q.x.pin.d3b → _root_.Formalism.L2.SelectedSideOfRealRecord R (divisionPairOfAdelicFormsFaceColumnsData x) (_root_.GlobalTheory.Mem.R3.realisationOfInput y) (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r) HD q.core_data_of_point.a.Pq := by
  intro _ _ _ _ _ _ _ _ _ hL N Γ p hp _ K q _ _ R hR sP sS _ _ a x ax y r HD hHD
  have hQ := qe_image_std q.w q.Z R.T.ker hR.k.std
  have hsel : Set.range q.core_data_of_point.a.Pq = Set.range q.w.I.sel := q.core_data_of_point.sel
  have hlev0 := (twArgs_lev K q.B q.f q.T q.w q.Z q.x.Wt _ _ _ _ _ _ _ q.O.ex q.x.what₂ a).2.2.1
  have hlev : ∀ μ, Formalism.IndefR.RecTie.Used0 (q.w.st q.Z).toD7 μ → HEq (x.R.Q (x.Y.tupT μ)) (q.w.I.Q μ) := by
    have key : ∀ x' : TwIn q.O.ex, a.x = x' →
        ∀ μ, Formalism.IndefR.RecTie.Used0 (q.w.st q.Z).toD7 μ → HEq (x'.R.Q (x'.Y.tupT μ)) (q.w.I.Q μ) := by
      rintro x' rfl μ hμ
      exact (hlev0 μ hμ).1
    exact key x (eq_of_heq ax)
  refine ⟨⟨q.core_data_of_point.a.Pq_over, ?_⟩, ?_, ?_, ?_⟩
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
    exact _root_.GlobalTheory.Mem.R3.SelSideW.de_pin_alt q v hv
  · intro v hv
    rw [hHD]
    exact _root_.GlobalTheory.Mem.R3.SelSideW.under_Pq_eq_pK'_of_pde'_mem q v hv
end GlobalTheory.Mem.R3.SelSideW
end
