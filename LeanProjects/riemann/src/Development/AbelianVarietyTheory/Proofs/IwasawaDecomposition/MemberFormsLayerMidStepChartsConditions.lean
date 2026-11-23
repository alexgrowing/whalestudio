import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsChartedLabAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepTiesD
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BaseLatticeSelfDualOfLocalEq
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChiFinOfGlevH
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUnifPow
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DetIntOfLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ChartTies3Site
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChiDValuesAndCcTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedChainChartLevelCharactersRational
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TiePtOneRec
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.MainNotions.G.CmpJ Formalism.MainNotions.G.ChartsLv GlobalTheory.Mem.Top.KerOne.CertEq
noncomputable section

namespace GlobalTheory.Mem.Top.KerOne.CertEq

open Formalism.L2.Forms Formalism.L2.G Formalism.UG Matrix
open scoped TensorProduct

section Hyp

variable {D : D7} {X0 : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {i : ℕ} {hi : i + 1 ≤ D.R.m}

set_option maxHeartbeats 2000000 in

theorem stab_iff_frB (Fo : FormsIn M (i + 1) hi) (S : StepD X0 u w hg Fo) (β : Fo.Ch)
    (w' : HeightOneSpectrum (𝓞 D.host.F)) (h : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal)
    (hdual : SelfDualAt D.sp.cm.sig (D.sp.X (i + 1)).gram w' (lbOf Fo β))
    (x : GL (Fin (D.sp.X (i + 1)).rank) (D.host.E ⊗[D.host.F] w'.adicCompletion D.host.F))
    (hx : x ∈ UPts D.sp.cm.sig (D.sp.X (i + 1)).gram (w'.adicCompletion D.host.F)) :
    x ∈ levelVL D.sp.cm.sig (D.sp.X (i + 1)).gram w' (lbOf Fo β) ↔
    (∀ a b, (((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h :
      GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F) ∧
    ∀ a b, ((((frB X0 u w hg S.B w' h)⁻¹ * bc ((RingHom.fst _ _).comp ((X0.g u w hg).spl w' h).toRingHom) x * frB X0 u w hg S.B w' h)⁻¹ :
      GL (Fin (D.sp.X (i + 1)).rank) _) : Matrix (Fin (D.sp.X (i + 1)).rank) (Fin (D.sp.X (i + 1)).rank) _) a b ∈
        w'.adicCompletionIntegers D.host.F := by
  have hs : SplitStabL D.sp.cm.sig (D.sp.X (i + 1)).gram w' ((X0.g u w hg).spl w' h) (lbOf Fo β)
      (frB X0 u w hg S.B w' h) :=
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

end Hyp

section Main

set_option maxHeartbeats 8000000 in

theorem stepTiesD_mid : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (i : ℕ) (hi : i + 1 ≤ (w.D Z).R.m), i + 1 + 1 ≤ (w.D Z).R.m →
      ∃ (Fo : FormsIn ((w.D Z).fm u) (i + 1) hi) (_ : Finite Fo.Ch) (S : StepD t.g.herm u v hg Fo),
        StepTiesD t.g.herm u v hg hi Fo S t.cmp := by
  intro K B f T w _ _ _ Z t Wt nch n Y _ _ O _ _ E _ u v hg i hi hi2
  have h1 : 1 ≤ i + 1 := Nat.succ_le_succ (Nat.zero_le i)
  let F := t.C.forms u
  let dt : GlobalTheory.Port.MemDt F :=
    ⟨fun j hj _ => GlobalTheory.Port.detTieOf t.full.1.base _, fun j _ _ β => GlobalTheory.Port.detTieOf t.full.1.base _⟩
  have hB : GlobalTheory.Port.BaseEx t.g.herm u v hg (GlobalTheory.Port.formsInMem F dt i hi) := by
    obtain ⟨Cm, hC1, hC2, -⟩ := F.deC (i + 1) h1 hi2
    exact GlobalTheory.Port.baseEx_of t.g.herm u v hg _ Cm hC1 hC2 (GlobalTheory.Port.base_lattice_self_dual_of_chain t.C u dt i hi v hg)
  have hrat : ∀ β, Formalism.L2.G.Cmp.ChiRatAll ((GlobalTheory.Port.formsInMem F dt i hi).K β).lev (w.D Z).what₂.embLL := by
    rw [GlobalTheory.Port.formsInMem_mid F dt i hi hi2]
    intro β
    obtain ⟨k, hR⟩ := (t.std u).mid (i + 1) h1 hi2
    exact GlobalTheory.ChiRatStd.chiRatAll_of_reads w.I w.ok w.pins w.l Z u w.I.mu0 (i + 1) (le_of_succ_m hi2) _ _ _ rfl
      (F.ch (i + 1) h1 hi2) k hR
      (fun β => GlobalTheory.Port.chi_fin_of_glevH (F.glevC (i + 1) h1 hi2 β) fun a => ((w.D Z).host.g_prime a).ne_zero) β
  have hψ : GlobalTheory.Port.PsiEx (GlobalTheory.Port.formsInMem F dt i hi) (t.cmp.embW u v hg) :=
    GlobalTheory.Port.psiEx_of _ (t.cmp.embW u v hg) (((w.D Z).gat u v hg).P.setting (plc t.Gt u v hg)).frac_O hrat
      (GlobalTheory.Port.finMem_of F dt i hi)
  haveI : ∀ j, Finite (t.C.herm.base.Ch u j) := fun j => t.C.herm.base.ChFin u j
  let S : StepD t.g.herm u v hg (GlobalTheory.Port.formsInMem F dt i hi) :=
    ⟨hB.choose, hB.choose_spec.2, fun β => (hψ β).choose, fun β => GlobalTheory.Port.fin_of _ β _⟩
  refine ⟨GlobalTheory.Port.formsInMem F dt i hi, GlobalTheory.Port.formsInMem_fin F dt i hi, S, ?_⟩
  have hT : ¬ (w.D Z).what₂.places.resChar v ∣ (GlobalTheory.Port.formsInMem F dt i hi).T := by
    rw [GlobalTheory.Port.memberChainForms_levelPrime_eq_member]; exact hg.2.2.2.2.2
  have hbad : ∀ w' ∈ (GlobalTheory.Port.formsInMem F dt i hi).bad,
      (((w.D Z).what₂.places.resChar v : ℕ) : 𝓞 (w.D Z).host.F) ∉ w'.asIdeal := by
    rw [GlobalTheory.Port.formsInMem_bad]; exact Formalism.L2.G.bad_notOver u v hg
  have hre := fun β w' => GlobalTheory.Port.formsLev_re (rankN (w.D Z) (i + 1) hi) (w.D Z).sp.cm.sig ((w.D Z).sp.X (i + 1)).gram
    (gramN (w.D Z) (i + 1) hi) (gramN_apply (w.D Z) (i + 1) hi) ((GlobalTheory.Port.formsInMem F dt i hi).K β).lev w'
  refine ⟨fun β w' h x hx ha hb => ?_, fun β w' h x hx => ?_, hbad, hB.choose_spec.1, fun β => (hψ β).choose_spec,
    GlobalTheory.Port.chRat_mem (GlobalTheory.Mem.ChiDVal.chiD_values_and_cc_top B f T w Z).1 F dt i hi,
    GlobalTheory.Port.formsInMem_ok F dt i hi v, hT⟩
  · have hTw := GlobalTheory.Port.T_not_mem hg.1 hT w' h
    exact (hre β w').2.2 (fun hb' => hbad w' hb' h) hTw
      ((stab_iff_frB (GlobalTheory.Port.formsInMem F dt i hi) S β w' h ((hre β w').2.1 hTw) x hx).2 ⟨ha, hb⟩)
  · have hTw := GlobalTheory.Port.T_not_mem hg.1 hT w' h
    have hl := (hre β w').1 hx
    exact (stab_iff_frB (GlobalTheory.Port.formsInMem F dt i hi) S β w' h ((hre β w').2.1 hTw) x hl.1).1 hl

end Main

end GlobalTheory.Mem.Top.KerOne.CertEq

end
