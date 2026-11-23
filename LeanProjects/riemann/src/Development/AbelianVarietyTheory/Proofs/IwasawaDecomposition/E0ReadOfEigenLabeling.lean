import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTied
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodVOfGoodL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubOrthProjPerpMem
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnitaryRealisationReadingOfIdempotentActsViaLeve
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientFieldEqLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.HeightCounting.Up.RealOfReading

noncomputable section

namespace GlobalTheory.HeightCounting.Up.IdempotentAdelicReading

set_option maxHeartbeats 4000000 in

theorem gaL_jV {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hr : R.grp_red_L)
    (hj : R.models_jV) (j : Fin D.R.m) (hc : (R.cV j).Is) (t : T) (y : (A.fam.L j t).S.Forms)
    (l : (R.cV j).W →ₗ[ℂ] ℂ) :
    gaL (Vc D j) (R.βV j) (R.datVt j t) R.eG (RealDat.eC (A := A) (sg0 D A)) (fun g => l (R.extV j t (R.jV j t y) g)) =
      fun g => l (R.extV j t (R.jV j t (∑ a, (idemOf A.X).coeff a • (A.fam.L j t).r a y)) g) := by
  let Φ : (R.HV j t).H →ₗ[ℂ] (GA D (Vc D j) → ℂ) := l.compLeft (GA D (Vc D j)) ∘ₗ R.extV j t
  have hs : ∀ a, RealDat.eC (A := A) (sg0 D A) a = D.what₂.embLL ((idemOf A.X).coeff a) := fun a => by
    show sg0 D A _ = _
    rw [sg0, sgAt_mk D.what₂.embLL R.hv0]
  have key : ∀ a, Φ (R.jV j t ((A.fam.L j t).r a y)) =
      Formalism.IndefR.Links.actL (Vc D j) (R.βV j) (R.datVt j t) (R.eG a) (Φ (R.jV j t y)) := fun a =>
    (GlobalTheory.GoodModelVec.actL_coord R hr hj j hc t a y l).symm
  show gaL (Vc D j) (R.βV j) (R.datVt j t) R.eG (RealDat.eC (A := A) (sg0 D A)) (Φ (R.jV j t y)) =
    Φ (R.jV j t (∑ a, (idemOf A.X).coeff a • (A.fam.L j t).r a y))
  rw [map_sum, map_sum]
  simp only [LinearMap.map_smulₛₗ, key, gaL, LinearMap.sum_apply, LinearMap.smul_apply, hs, RingHom.id_apply]
  rfl

set_option maxHeartbeats 4000000 in

theorem act_of_read {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A3.A Ks) (F : Face D A3.A) {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R F X0)
    (hg : GlobalTheory.LiftRows.Given R F) {s : ℕ} (hok : A3.A.fam.Ok s) (j : Fin D.R.m) :
    ∀ (μ : D.what₂.Tup) (t : T), Y.tup t = μ → ∀ (h : Used0 D μ) (f : D.what₂.Mt μ (j.1 + 1)) (l : (R.cV j).W →ₗ[ℂ] ℂ),
      gaL (Vc D j) (R.βV j) (R.datVt j t) R.eG (RealDat.eC (A := A3.A) (sg0 D A3.A)) (fun g => l ((Y.IL.jMt μ h j f).1 g)) =
        fun g => l ((Y.IL.jMt μ h j (D.what₂.eMt μ (j.1 + 1) f)).1 g) := by
  intro μ t ht h f l
  subst ht
  let Ψ : D.what₂.Mt (Y.tup t) (j.1 + 1) →ₗ[ℂ] (GA D (Vc D j) → ℂ) :=
    l.compLeft (GA D (Vc D j)) ∘ₗ
      ((((toLiftReal R F Y.tupT Y.hm Y.hTop Y.hinj).Amt (Y.tup t) j).subtype :
        _ →ₗ[ℂ] (GA D (Vc D j) → (R.cV j).W)) ∘ₗ (Y.IL.jMt (Y.tup t) h j).toLinearMap)
  have hΨ : ∀ f, Ψ f = fun g => l ((Y.IL.jMt (Y.tup t) h j f).1 g) := fun _ => rfl
  have hF := Y.formsL j t
  have main : gaL (Vc D j) (R.βV j) (R.datVt j t) R.eG (RealDat.eC (A := A3.A) (sg0 D A3.A)) ∘ₗ Ψ =
      Ψ ∘ₗ D.what₂.eMt (Y.tup t) (j.1 + 1) := by
    refine LinearMap.ext_on_range hF.span fun k => ?_
    have hop := hF.op_eq (Pi.single k 1)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hop ⊢
    rw [hop, hΨ, hΨ, Y.mtRead j t h, Y.mtRead j t h]
    generalize (Pi.single k 1 : Fin _ → D.what₂.LL) = x
    have hl : liftForm A3.A F.P0 F.ψ0 j t ((lE D A3.A F.P0 F.ψ0 j t).mulVec x) =
        ∑ g, (idemOf A3.A.X).coeff g • (A3.A.fam.L j t).r g (liftForm A3.A F.P0 F.ψ0 j t x) :=
      GlobalTheory.ClassSumIdentity.lvlE_lvlOp hok.conj _ ((hok.lifts j t).hpos _) _ (hok.lifts j t).act _ _ _
        (fun b => (idempotent_central _ _ A3.A.X hok.irr).2 b) x
    rw [hl]
    exact gaL_jV R hg.core.grp.red_L hg.core.models.jV j (hg.core.models.cV j) t _ l
  exact LinearMap.congr_fun main f

theorem goodIdempotent_eq_goodProjector_adelicReading {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A3.A Ks) (F : Face D A3.A) {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R F X0)
    {cf : CharFrame D} {nch : NChoice D} (tp : TupTied D cf nch) (hC : R.C = cf) (Xd : DivX D) (E : EigIdx D Xd)
    (labPi : E.Pi → A3.A.fam.base.Ix) (hbase : R.BaseW F)
    (htup : ∀ μ, Used0 D μ → R.toLevCh.xiH (Y.tupT μ) = tp.xi μ) (hg : GlobalTheory.LiftRows.Given R F) (hf : R.FullP)
    {s : ℕ} (hok : A3.A.fam.Ok s) :
    GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector (realOfRead R F Y tp hC Xd E labPi hbase htup hg hf) := by
  apply GlobalTheory.NRows.Model.unitaryRealisationReading_of_idempotent_acts_via_levelGroup
  intro μ hμ j f l
  rw [← D.nStage_trivialCharacter_compat.2]
  exact act_of_read R F Y hg hok j μ (Y.tupT μ) (Y.tupTie μ hμ) hμ f l

theorem goodIdempotentReadsAsGoodTypeProjector_realOfRead : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ T w Z Wt _ t nch n c => ∀ (hC : t.r.z.R.C = TC.cf w.I w.l Z) (Xd : DivX (w.D Z)) (E : EigIdx (w.D Z) Xd) (labPi : E.Pi → (famR (w.st Z) w.I t.hX (usedOf w.I T Wt) t.r.z.Xg t.r.z.tr).A.fam.base.Ix) hb htup hg hf, GlobalTheory.NRows.GoodIdempotentReadsAsGoodTypeProjector (realOfRead t.r.z.R.toRealDat t.r.z.F.lv2 t.r.Y n.tp hC Xd E labPi hb htup hg hf) := by
  intro _ hL
  exact GlobalTheory.HeightCounting.Up.CoefficientAgreement.atMem_of_forall fun _ _ _ _ _ _ _ _ t _ _ _ _ _ _ _ _ _ _ _ =>
    goodIdempotent_eq_goodProjector_adelicReading _ _ _ _ _ _ _ _ _ _ _ _ t.r.intersectionNumber_baseChange.ok.ok2

end GlobalTheory.HeightCounting.Up.IdempotentAdelicReading
