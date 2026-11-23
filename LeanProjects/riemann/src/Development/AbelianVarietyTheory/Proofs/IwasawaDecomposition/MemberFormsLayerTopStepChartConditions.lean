import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsChartedLabAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepTiesD
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BaseLatticeSelfDualOfLocalEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChartTies3Site
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChiFinOfGlevH
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUnifPow
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DetIntOfLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChainChartLocalUnitCharacterCompatibleLeve
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChiDValuesAndCcTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedChainChartLevelCharactersRational
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOneRec
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv GlobalTheory.Mem.Top.KerOne.CertEq

noncomputable section

namespace GlobalTheory.Mem.Top.KerOne.CertEq.TopStep

open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.MainNotions.G.CmpJ.PStabEq Matrix
open scoped TensorProduct

section Stab

variable {D : D7} {X0 : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {i : ℕ} {hi : i + 1 ≤ D.R.m}

set_option maxHeartbeats 4000000 in

theorem stab_frB (Fo : FormsIn M (i + 1) hi) (S : StepD X0 u w hg Fo) (β : Fo.Ch)
    (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal)
    (hT : ¬ D.what₂.places.resChar w ∣ Fo.T)
    (x : GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] w'.adicCompletion D.host.F))
    (hx : x ∈ UPts D.sp.cm.sig (D.sp.X (i + 1)).gram (w'.adicCompletion D.host.F)) :
    x ∈ levelVL D.sp.cm.sig (D.sp.X (i + 1)).gram w' (lbOf Fo β) ↔
    (∀ a b, (((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x *
      frB X0 u w hg S.B w' h : GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F) ∧
    ∀ a b, ((((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x *
      frB X0 u w hg S.B w' h)⁻¹ : GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F := by
  have hdual := (GlobalTheory.Port.formsLev_re (rankN D (i + 1) hi) D.sp.cm.sig (D.sp.X (i + 1)).gram (gramN D (i + 1) hi)
    (gramN_apply D (i + 1) hi) (Fo.K β).lev w').2.1 (GlobalTheory.Port.T_not_mem hg.1 hT w' h)
  have hs : SplitStabL D.sp.cm.sig (D.sp.X (i + 1)).gram w' ((X0.g u w hg).spl w' h) (lbOf Fo β) (frB X0 u w hg S.B w' h) :=
    splitStabL_of D.sp.cm.sig (D.sp.X (i + 1)).gram w' ((X0.g u w hg).spl w' h) (lbOf Fo β) (frB X0 u w hg S.B w' h)
      (fun y => (X0.g u w hg).spl_sig w' h y)
      (split_integral_completion D.host.F D.host.E w' ((X0.g u w hg).spl w' h) ((X0.g u w hg).spl_alg w' h)) hdual
      (fun s => S.B_lat β w' h s)
  have key : ∀ y : w'.adicCompletion D.host.F,
      y ∈ (algebraMap (w'.adicCompletionIntegers D.host.F) (w'.adicCompletion D.host.F)).range ↔
        y ∈ w'.adicCompletionIntegers D.host.F :=
    fun y => ⟨by rintro ⟨z, rfl⟩; exact z.2, fun h => ⟨⟨y, h⟩, rfl⟩⟩
  rw [hs x hx, toFr_apply, mem_range_bc_iff _ (algMapV_injective D.host.F w')]
  simp only [key]

end Stab

set_option maxHeartbeats 4000000 in

theorem stepTies_top : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (i : ℕ) (hi : i + 1 ≤ (w.D Z).R.m), i + 1 = (w.D Z).R.m →
      ∃ (Fo : FormsIn ((w.D Z).fm u) (i + 1) hi) (_ : Finite Fo.Ch) (S : StepD t.g.herm u v hg Fo),
        StepTiesD t.g.herm u v hg hi Fo S t.cmp := by
  intro K B f T w hO hF hP Z t Wt nch n Y hmu hQp O hO' hunf E hE u v hg
  intro i hi h
  let F := t.C.forms u
  let dt := GlobalTheory.Port.detTieOf t.full.1.base (F.cls (i+1) hi (Or.inr h)).lev
  let Fo : FormsIn ((w.D Z).fm u) (i + 1) hi := GlobalTheory.Port.formsInOne (F.val (i+1) hi (Or.inr h)) dt
  let dtM : GlobalTheory.Port.MemDt F := ⟨fun j hj h' => GlobalTheory.Port.detTieOf t.full.1.base _, fun j h1 h2 β => GlobalTheory.Port.detTieOf t.full.1.base _⟩
  have hL0 := GlobalTheory.Port.base_lattice_self_dual_of_chain t.C u dtM i hi v hg
  rw [GlobalTheory.Port.formsInMem_top F dtM i hi h] at hL0
  have hL : GlobalTheory.Port.ChartBaseLatticeEqSelfDualAtP u Fo ((w.D Z).what₂.places.resChar v) := hL0
  obtain ⟨Cm, h1, h2, -⟩ := (F.val (i+1) hi (Or.inr h)).de
  obtain ⟨B0, hstd, hB⟩ := GlobalTheory.Port.baseEx_of t.g.herm u v hg Fo Cm h1 h2 hL
  haveI : IsFractionRing ((w.D Z).gat u v hg).O ((w.D Z).gat u v hg).Kf :=
    (((w.D Z).gat u v hg).P.setting (plc t.Gt u v hg)).frac_O
  have hfin := GlobalTheory.Port.chi_fin_top F (i + 1) hi h
  have hrat : Formalism.L2.G.Cmp.ChiRatAll (F.cls (i+1) hi (Or.inr h)).lev (w.D Z).what₂.embLL := by
    obtain ⟨k, hR⟩ := (t.std u).ends (i+1) hi (Or.inr h)
    exact GlobalTheory.ChiRatStd.chiRatAll_of_reads w.I w.ok w.pins w.l Z u w.I.mu0 (i+1) hi (badG (w.D Z)) (fun _ => ())
      _ rfl (fun β => Formalism.MainNotions.G.CmpJ.oneChart (F.cls (i+1) hi (Or.inr h)) β) k hR (fun _ => hfin) ()
  obtain ⟨ψ, hψ⟩ := GlobalTheory.Mem.Top.KerTwPsi.exists_psiTiedJ hi (F.cls (i+1) hi (Or.inr h)).lev
    (Formalism.MainNotions.G.ChartsLv.sameU_of Fo ()) (t.cmp.embW u v hg) hrat hfin
  let S : StepD t.g.herm u v hg Fo :=
    { B := B0
      B_lat := fun _ => hB ()
      ψ := fun _ => ψ
      fin := fun β => GlobalTheory.Port.fin_of Fo β _ }
  have hT : ¬ (w.D Z).what₂.places.resChar v ∣ Fo.T := hg.2.2.2.2.2
  refine ⟨Fo, (inferInstance : Finite Unit), S, ?_, ?_, ?_, hstd, fun _ => hψ, ?_, trivial, hT⟩
  · intro β w' hw x hx hx1 hx2
    exact (GlobalTheory.Port.formsLev_re (rankN (w.D Z) (i + 1) hi) (w.D Z).sp.cm.sig ((w.D Z).sp.X (i + 1)).gram (gramN (w.D Z) (i + 1) hi)
      (gramN_apply (w.D Z) (i + 1) hi) (Fo.K β).lev w').2.2 (fun hb => Formalism.L2.G.bad_notOver u v hg w' hb hw)
      (GlobalTheory.Port.T_not_mem hg.1 hT w' hw) ((stab_frB Fo S β w' hw hT x hx).2 ⟨hx1, hx2⟩)
  · intro β w' hw x hx
    have hle := (GlobalTheory.Port.formsLev_re (rankN (w.D Z) (i + 1) hi) (w.D Z).sp.cm.sig ((w.D Z).sp.X (i + 1)).gram (gramN (w.D Z) (i + 1) hi)
      (gramN_apply (w.D Z) (i + 1) hi) (Fo.K β).lev w').1 hx
    exact (stab_frB Fo S β w' hw hT x hle.1).1 hle
  · exact Formalism.L2.G.bad_notOver u v hg
  · intro β cl
    exact GlobalTheory.Port.chRat_ofChiD (GlobalTheory.Mem.ChiDVal.chiD_values_and_cc_top B f T w Z).1 _ _ _

end GlobalTheory.Mem.Top.KerOne.CertEq.TopStep
