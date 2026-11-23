import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoQuotToImOmegaLieOfSplit
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulEllTheta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
open GlobalTheory.LB (resG_resG resG_self toMod)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)
open ReciprocityTheory.L2DbarEstimates (V)
open Limits (pullback biprod)
open MonoidalCategory CartesianMonoidalCategory
open GlobalTheory.Cartier
open GlobalTheory.CechPic (Pic cls lam)
open GlobalTheory.LieVB (omega unitSec dUnit)
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
open scoped ContDiff ComplexOrder CategoryTheory.Obj

namespace GlobalTheory

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {σ σ' : k →+* ℂ}

structure IsRegSurf (p : X ⟶ Sp k) : Prop extends IsArithVar p 1 where

  regular : ∀ x, IsRegularLocalRing (X.presheaf.stalk x)

theorem ProjSpace.isRegSurf_line : IsRegSurf (PSpace.str ℤ 1) := by
  have : Smooth (PSpace.str ℤ 1) := SmoothOfRelativeDimension.smooth 1 _
  refine ⟨ProjSpace.isArithVar_int 1, fun x => ?_⟩
  have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth ℤ (PSpace.str ℤ 1) x
  exact .of_isRegularRing_of_isLocalRing _

structure RegCover (p : X ⟶ Sp k) [IsIntegral X] where

  Y : Scheme.{0}

  ρ : Y ⟶ X

  reg : IsRegSurf (ρ ≫ p)

  generic : haveI := reg.isIntegral; ρ (genericPoint Y) = genericPoint X

  finite : haveI := reg.isIntegral; ρ.residueDegree (genericPoint Y) ≠ 0

namespace RegCover

variable [IsIntegral X] (C : RegCover p)

instance : IsIntegral C.Y := C.reg.isIntegral

def deg : ℕ := C.ρ.residueDegree (genericPoint C.Y)

theorem deg_pos : 0 < C.deg := Nat.pos_of_ne_zero C.finite

def self (h : IsRegSurf p) : RegCover p where
  Y := X
  ρ := 𝟙 X
  reg := (Category.id_comp p).symm ▸ h
  generic := rfl
  finite := (Scheme.Hom.residueDegree_id _).trans_ne one_ne_zero

theorem deg_self (h : IsRegSurf p) : (self h).deg = 1 := Scheme.Hom.residueDegree_id _

end RegCover

namespace HermLB

variable [IsIntegral X] [IsLocallyNoetherian X] (L M : HermLB p)

def IsInter (a : ℝ) : Prop :=
  ∃ h, M.IsArithHeight h ∧ ∀ (r : L.B.ι → X.functionFieldˣ) (hr : IsRatSec L.B r),
    M.ArchIntegrable L 1 hr ∧ a = ∑ᶠ z, ((L.div hr).mult z : ℝ) * h z - M.archInt L 1 hr

variable {L M}

theorem IsInter.unique (hX : IsArithVar p 1) {a b : ℝ} (ha : L.IsInter M a) (hb : L.IsInter M b) :
    a = b := by
  obtain ⟨h, H, ha⟩ := ha
  obtain ⟨h', H', hb⟩ := hb
  obtain ⟨r, hr⟩ := exists_isRatSec L.isLB
  rw [(ha r hr).2, (hb r hr).2, H.unique hX H']

theorem IsInter.triv_shift {t a : ℝ} (h : ((triv p).shift (fun _ => t) fun _ => rfl).IsInter M a)
    [Finite (k →+* ℂ)] : a = t * ArInt.gdeg M 1 := by
  obtain ⟨h, -, H⟩ := h
  have hr : IsRatSec (LB.triv X) fun _ => 1 := fun a b h => by
    exact ((congrArg (· * _) (map_one _)).trans (one_mul _)).symm
  have hL := LB.isLB_triv X
  have h₀ (z : X) : (divOfRatSec hL hr).IsEqn z 1 :=
    (presents_divOfRatSec hL hr).isEqn PUnit.unit z trivial
  have h₁ (z : X) : (divOfRatSec hL hr).mult z = 0 := (h₀ z).mult_eq.trans (unitAt_one z).ord_eq_zero
  have h₂ (σ) : offSupp p σ (divOfRatSec hL hr) = univ :=
    eq_univ_of_forall fun y => mem_offSupp.2 fun h => h (h₀ _)
  have h₃ (σ) : logNorm (((triv p).shift (fun _ => t) fun _ => rfl).φ σ) (fun _ => 1) =
      fun _ : CxPts p σ => -t * 1 := funext fun y => by
    have e := ratVal_fnOf (y := y) mem_ptsIn_top trivial 1
    rw [map_one, ev_one mem_ptsIn_top] at e
    rw [logNorm, Units.val_one, e]
    simp [triv, shift, Weight.ofFun, Weight.addFn]
  have e := (H _ hr).2
  have := Fintype.ofFinite (k →+* ℂ)
  simp only [archInt, div] at e
  erw [finsum_congr fun z => congrArg (fun n : ℤ => (n : ℝ) * h z) (h₁ z)] at e
  rw [e, ArInt.gdeg, ArInt.chInt]
  simp only [Int.cast_zero, zero_mul, finsum_zero, zero_sub]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  erw [h₂, h₃, Weight.chernInt_const_mul]
  ring

end HermLB

section Sum

variable {E₁ E₂ : X.Modules} {r s : ℕ}

def Met.orthSum (h₁ : Met p σ E₁ r) (h₂ : Met p σ E₂ s) : Met p σ (E₁ ⊞ E₂) (r + s) where
  isVB := h₁.isVB.biprod h₂.isVB
  G c y := h₁.gram (fun a => (biprod.fst : E₁ ⊞ E₂ ⟶ E₁).app c.U (c.e a)) y +
    h₂.gram (fun a => (biprod.snd : E₁ ⊞ E₂ ⟶ E₂).app c.U (c.e a)) y
  posDef c y hy := by
    have hS := (ShortComplex.Splitting.ofHasBinaryBiproduct E₁ E₂).shortExact
    obtain ⟨a, ha⟩ := Met.exists_adapted hS h₁.isVB h₂.isVB y
    rw [h₁.gram_app_trans _ (a.mid hS) c ha, h₂.gram_app_trans _ (a.mid hS) c ha, chg, chg,
      ← Matrix.add_mul, ← Matrix.mul_add]
    refine posDef_chg ((a.mid hS).isUnit_tr c ha hy) ?_
    rw [h₁.gram_eq (U := (a.mid hS).U) a.sub ha _ ha, h₂.gram_eq (U := (a.mid hS).U) a.quot ha _ ha]
    have p₁ := posDef_iff.1 (h₁.posDef a.sub y ha)
    have p₂ := posDef_iff.1 (h₂.posDef a.quot y ha)
    refine posDef_iff.2 ⟨(isHermitian_mul_mul_conjTranspose _ p₁.1).add
      (isHermitian_mul_mul_conjTranspose _ p₂.1), fun v hv => ?_⟩
    rw [HermFrame.form_add, form_chg, form_chg]
    have n {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (h : ∀ v, v ≠ 0 → 0 < HermFrame.form H v v) (v) :
        0 ≤ HermFrame.form H v v := by
      by_cases e : v = 0
      · simp [e, HermFrame.form]
      · exact (h v e).le
    by_contra hn
    have z₁ := not_not.1 fun e => hn (add_pos_of_pos_of_nonneg (p₁.2 _ e) (n p₂.2 _))
    have z₂ := not_not.1 fun e => hn (add_pos_of_nonneg_of_pos (n p₁.2 _) (p₂.2 _ e))
    have e₁ (b : Fin r) : a.sub.crd p σ ((biprod.fst : E₁ ⊞ E₂ ⟶ E₁).app a.U
        ((a.mid hS).e (finSumFinEquiv (.inl b)))) y = Pi.single b 1 :=
      (congrArg (a.sub.crd p σ · y) (by
        simp only [AdaptedChart.mid, Function.comp_apply, Equiv.symm_apply_apply]
        exact congr(($(biprod.inl_fst (X := E₁) (Y := E₂))).app a.U (a.e b)))).trans
        (a.sub.crd_frame ha b)
    have e₂ (b : Fin r) : a.quot.crd p σ ((biprod.snd : E₁ ⊞ E₂ ⟶ E₂).app a.U
        ((a.mid hS).e (finSumFinEquiv (.inl b)))) y = 0 :=
      (congrArg (a.quot.crd p σ · y) (by
        simp only [AdaptedChart.mid, Function.comp_apply, Equiv.symm_apply_apply]
        exact congr(($(biprod.inl_snd (X := E₁) (Y := E₂))).app a.U (a.e b)))).trans
        (a.quot.crd_zero y)
    have e₃ (b : Fin s) : a.quot.crd p σ ((biprod.snd : E₁ ⊞ E₂ ⟶ E₂).app a.U
        ((a.mid hS).e (finSumFinEquiv (.inr b)))) y = Pi.single b 1 :=
      (congrArg (a.quot.crd p σ · y) (by
        simp only [AdaptedChart.mid, Function.comp_apply, Equiv.symm_apply_apply]
        rfl)).trans (a.quot.crd_frame ha b)
    have v₂ (j : Fin s) : v (finSumFinEquiv (.inr j)) = 0 := by
      have := congrFun z₂ j
      simp only [mulVec, dotProduct, of_apply] at this
      rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type] at this
      erw [Finset.sum_congr rfl fun b _ => congrArg (· * _) (congrFun (e₂ b) j),
        Finset.sum_congr rfl fun b _ => congrArg (· * _) (congrFun (e₃ b) j)] at this
      simpa [Pi.single_apply] using this
    have v₁ (j : Fin r) : v (finSumFinEquiv (.inl j)) = 0 := by
      have := congrFun z₁ j
      simp only [mulVec, dotProduct, of_apply] at this
      rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type] at this
      simp only [v₂, mul_zero, Finset.sum_const_zero, add_zero] at this
      erw [Finset.sum_congr rfl fun b _ => congrArg (· * _) (congrFun (e₁ b) j)] at this
      simpa [Pi.single_apply] using this
    exact hv (funext fun i => by
      obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective i
      exacts [v₁ j, v₂ j])
  trans c c' y hy := by
    rw [h₁.gram_app_trans _ c c' hy, h₂.gram_app_trans _ c c' hy]
    simp only [chg, Matrix.add_mul, Matrix.mul_add]

def VMetric.orthSum (h₁ : VMetric p E₁ r) (h₂ : VMetric p E₂ s) : VMetric p (E₁ ⊞ E₂) (r + s) :=
  ⟨h₁.isVB.biprod h₂.isVB, fun σ => (h₁.met σ).orthSum (h₂.met σ), fun σ σ' =>
    Met.isConj_of_exists fun y y' e => by
      have hc := (h₁.isVB.biprod h₂.isVB).mem_pick y
      exact ⟨_, hc, (congrArg₂ (· + ·) ((h₁.conj σ σ').gram _ e hc)
        ((h₂.conj σ σ').gram _ e hc)).trans (Matrix.map_add _ star_add _ _).symm⟩⟩

theorem VMetric.isOrthSum_orthSum (h₁ : VMetric p E₁ r) (h₂ : VMetric p E₂ s) :
    (h₁.orthSum h₂).IsOrthSum h₁ h₂ := fun σ U t t' y hy => by
  have hc := (h₁.isVB.biprod h₂.isVB).mem_pick y
  have k₁ := h₁.isVB.mem_pick y
  have k₂ := h₂.isVB.mem_pick y
  rw [Met.form_eq _ _ hc _ _ hy, Met.form_eq _ _ k₁ _ _ hy, Met.form_eq _ _ k₂ _ _ hy,
    Chart.crd_app _ _ biprod.fst t hy hc, Chart.crd_app _ _ biprod.fst t' hy hc,
    Chart.crd_app _ _ biprod.snd t hy hc, Chart.crd_app _ _ biprod.snd t' hy hc, ← form_chg,
    ← form_chg, ← Met.gram_eq _ _ k₁ _ hc, ← Met.gram_eq _ _ k₂ _ hc, ← HermFrame.form_add]
  rfl

theorem VMetric.IsCInf.orthSum {h₁ : VMetric p E₁ r} {h₂ : VMetric p E₂ s} (H₁ : h₁.IsCInf)
    (H₂ : h₂.IsCInf) : (h₁.orthSum h₂).IsCInf := fun σ _ _ hy a b =>
  (((H₁ σ).gram _ hy a b).prodMk ((H₂ σ).gram _ hy a b)).comp_contDiff (Ψ := fun x => x.1 + x.2)
    (contDiff_fst.add contDiff_snd)

def HermVB.orthSum (E : HermVB p r) (F : HermVB p s) : HermVB p (r + s) :=
  ⟨_, E.h.orthSum F.h, E.cInf.orthSum F.cInf⟩

end Sum

namespace VMetric

variable [IsIntegral X] {E : X.Modules} {r : ℕ} {h : VMetric p E r} {a b : ℝ}

def IsFlagCh2 (H : h.IsCInf) (fl : Vert.Flag E r) (a : ℝ) : Prop :=
  h.FlagBcFinite fl ∧ ∃ x : Fin r → ℝ, (∀ i, (grLB fl i H).IsSelfInter (x i)) ∧
    a = ∑ i, x i / 2 - h.flagBc fl / 2

theorem IsFlagCh2.unique {D : ℕ} (hX : IsArithVar p D) {H : h.IsCInf} {fl : Vert.Flag E r}
    (ha : IsFlagCh2 H fl a) (hb : IsFlagCh2 H fl b) : a = b := by
  obtain ⟨-, x, hx, rfl⟩ := ha
  obtain ⟨-, x', hx', rfl⟩ := hb
  rw [funext fun i => (hx i).unique hX (hx' i)]

theorem isFlagCh2_rank_one {h : VMetric p E 1} (H : h.IsCInf) (fl : Vert.Flag E 1) :
    IsFlagCh2 H fl a ↔ (grLB fl 0 H).IsSelfInter (2 * a) := by
  obtain ⟨h₁, h₂⟩ := flagBc_rank_one h fl
  refine ⟨?_, fun e => ⟨h₁, fun _ => 2 * a, fun i => Subsingleton.elim 0 i ▸ e, by simp [h₂]⟩⟩
  rintro ⟨-, x, hx, rfl⟩
  convert hx 0 using 1
  rw [h₂, Fin.sum_univ_one]
  ring

theorem isFlagCh2_rank_zero {h : VMetric p E 0} (H : h.IsCInf) (fl : Vert.Flag E 0) :
    IsFlagCh2 H fl a ↔ a = 0 := by
  simp [IsFlagCh2, FlagBcFinite, flagBc]

variable (h) in

structure FlagModel extends RegCover p where

  cInf : (h.pull ρ rfl).IsCInf

  flag : Vert.Flag ((Scheme.Modules.pullback ρ).obj E) r

def FlagModel.self (hX : IsRegSurf p) (H : h.IsCInf) (fl : Vert.Flag E r) : h.FlagModel :=
  ⟨.self hX, H.pull _ _, fl.ofIso ((Scheme.Modules.pullbackId X).app E).symm⟩

variable (h) in

def IsCh2Deg (a : ℝ) : Prop :=
  Nonempty h.FlagModel ∧ ∀ M : h.FlagModel, IsFlagCh2 M.cInf M.flag (M.deg * a)

theorem IsCh2Deg.unique (ha : h.IsCh2Deg a) (hb : h.IsCh2Deg b) : a = b :=
  have ⟨M⟩ := ha.1
  mul_left_cancel₀ (Nat.cast_ne_zero.2 M.deg_pos.ne')
    ((ha.2 M).unique M.reg.toIsArithVar (hb.2 M))

variable (h) in

def ch2Deg : ℝ := Classical.epsilon h.IsCh2Deg

theorem IsCh2Deg.ch2Deg_eq (ha : h.IsCh2Deg a) : h.ch2Deg = a :=
  (Classical.epsilon_spec ⟨a, ha⟩).unique ha

theorem IsCh2Deg.eq_div (ha : h.IsCh2Deg a) (M : h.FlagModel) (hb : IsFlagCh2 M.cInf M.flag b) :
    a = b / M.deg := by
  rw [hb.unique M.reg.toIsArithVar (ha.2 M),
    mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 M.deg_pos.ne')]

theorem isCh2Deg_rank_zero (hX : IsRegSurf p) {h : VMetric p E 0} (H : h.IsCInf)
    (fl : Vert.Flag E 0) : h.IsCh2Deg 0 :=
  ⟨⟨.self hX H fl⟩, fun M => (isFlagCh2_rank_zero _ _).2 (mul_zero _)⟩

end VMetric

abbrev HermVB.ch2Deg [IsIntegral X] {r : ℕ} (E : HermVB p r) : ℝ := E.h.ch2Deg

def ProjSpace.hermSum : HermVB (PSpace.str ℤ 1) (1 + 1) :=
  (HermVB.ofLB (ProjSpace.hermitianTwistingSheaf ℤ 1)).orthSum (HermVB.ofLB (ProjSpace.hermitianTwistingSheaf ℤ 1)).dual

theorem ProjSpace.exists_flagModel_hermSum :
    haveI := ProjSpace.isRegSurf_line.isIntegral
    ∃ M : ProjSpace.hermSum.h.FlagModel, M.deg = 1 :=
  haveI := ProjSpace.isRegSurf_line.isIntegral
  ⟨.self ProjSpace.isRegSurf_line ProjSpace.hermSum.cInf (.ofBiprod
    (HermVB.ofLB (ProjSpace.hermitianTwistingSheaf ℤ 1)).h.isVB (HermVB.ofLB (ProjSpace.hermitianTwistingSheaf ℤ 1)).dual.h.isVB),
    RegCover.deg_self ProjSpace.isRegSurf_line⟩

variable (p) in

def cxFibre : Scheme.{0} := pullback (p ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom ℂ))

variable (p) in

def cxFibre.fst : cxFibre p ⟶ X := pullback.fst _ _

variable (p) in

def cxFibre.snd : cxFibre p ⟶ Sp ℂ := pullback.snd _ _

instance cxFibre.algebra : Algebra ℂ Γ(cxFibre p, ⊤) :=
  ((cxFibre.snd p).appTop.hom.comp (Scheme.ΓSpecIso (.of ℂ)).inv.hom).toAlgebra

variable (p) in

def cxDeg (E : X.Modules) (r : ℕ) : ℤ :=
  degOfRank ℂ ((Scheme.Modules.pullback (cxFibre.fst p)).obj E) r

theorem cxDeg_congr {E E' : X.Modules} (φ : E ≅ E') (r : ℕ) : cxDeg p E r = cxDeg p E' r :=
  degOfRank_congr ℂ ((Scheme.Modules.pullback _).mapIso φ)

def sqMap {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) : (A' ⊗ A').left ⟶ (A ⊗ A).left :=
  pullback.map A'.hom A'.hom A.hom A.hom φ φ f w.symm w.symm

structure PPAS (S : Scheme.{0}) where

  A : Over S

  [grp : GrpObj A]

  isAb : IsAbelianScheme A

  g : ℕ

  smoothDim : SmoothOfRelativeDimension g A.hom

  c : Pic (A ⊗ A).left

  isPol : IsPrincipalPol A c

namespace PPAS

attribute [instance] grp smoothDim

variable {S S' : Scheme.{0}} (P : PPAS S)

instance : QuasiSeparated P.A.hom :=
  have := P.isAb.proper
  inferInstance

def ofPolAV (Q : Out.PolAV S) : PPAS S where
  A := Q.A
  isAb := Q.isAb
  g := Q.g
  smoothDim := Q.smoothDim
  c := _
  isPol := IndefiniteRowSideFullHecke.ZeroSectionBase.isPrincipalPol_of_polAV Q

theorem isVB_omega : IsVB (omega P.A) P.g := LieVB.isVB_omega P.A P.g

def IsPull (P' : PPAS S') (P : PPAS S) (f : S' ⟶ S) (φ : P'.A.left ⟶ P.A.left) : Prop :=
  ∃ h : IsGrpPullback P'.A P.A f φ, P'.c = CechPic.pull (sqMap h.1.w) P.c

def HasTheta : Prop :=
  ∃ (L : LB P.A.left) (hL : L.IsLB), Out.Sym P.A L ∧ P.c = lam (cls L hL) (fst P.A P.A) (snd P.A P.A)

theorem hasTheta_ofPolAV (Q : Out.PolAV S) : (ofPolAV Q).HasTheta := ⟨Q.L, Q.isLB, Q.sym, rfl⟩

structure RiemannData (y : Sp ℂ ⟶ S) where

  B : Over (Sp ℂ)

  [grp : GrpObj B]

  φ : B.left ⟶ P.A.left

  isPull : IsGrpPullback B P.A y φ

  L : LB B.left

  isLB : L.IsLB

  pol : CechPic.pull (sqMap isPull.1.w) P.c = lam (cls L isLB) (fst B B) (snd B B)

  u : HolUnif B L P.g

  H : Matrix (Fin P.g) (Fin P.g) ℂ

  χ : u.Λ → ℂ

  isAH : u.IsAH H χ

namespace RiemannData

attribute [instance] grp

variable {P} {y : Sp ℂ ⟶ S} (d : P.RiemannData y)

theorem posDef : d.H.PosDef := posDef_iff.2 ⟨d.isAH.1, fun v hv =>
  Complex.pos_iff.2 ⟨d.isAH.2.1 v hv, (Complex.conj_eq_iff_im.1 (conj_form d.isAH.1 v v)).symm⟩⟩

def fn (W : P.A.left.Opens) (f : Γ(P.A.left, W)) (z : Fin P.g → ℂ) : ℂ :=
  valR ((d.u.ex z).left ≫ d.φ) W f

def cov (W : P.A.left.Opens) (f : Γ(P.A.left, W)) : Fin P.g → ℂ := fun a =>
  fderiv ℂ (d.fn W f) 0 (Pi.single a 1)

theorem ex_zero : (d.u.ex 0).left ≫ d.φ = y ≫ unitSec P.A := by
  rw [(d.u.ker 0).2 (zero_mem _), ← LieVB.unitSec_comp d.isPull]
  exact congrArg (·.left ≫ d.φ) (MonObj.one_eq_one d.B).symm

theorem differentiableAt_fn {W : P.A.left.Opens} (f : Γ(P.A.left, W))
    (h : ⊤ ≤ (y ≫ unitSec P.A) ⁻¹ᵁ W) : DifferentiableAt ℂ (d.fn W f) 0 := by
  obtain ⟨h₁, h₂⟩ := d.u.hol (d.φ ⁻¹ᵁ W) (d.φ.app W f)
  rw [← d.ex_zero] at h
  exact (h₂.differentiableAt (h₁.mem_nhds h)).congr_of_eventuallyEq
    (.of_forall fun z => valR_comp _ _ _ _)

end RiemannData

theorem pull_sqMap_lam {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (c : Pic A.left) :
    CechPic.pull (sqMap h.1.w) (lam c (fst A A) (snd A A)) =
      lam (CechPic.pull φ c) (fst A' A') (snd A' A') := by
  let m : Over.mk ((A' ⊗ A').hom ≫ f) ⟶ A ⊗ A := Over.homMk (sqMap h.1.w) (by
    change sqMap h.1.w ≫ pullback.fst _ _ ≫ A.hom = (pullback.fst _ _ ≫ A'.hom) ≫ f
    rw [sqMap, pullback.lift_fst_assoc, Category.assoc, Category.assoc, h.1.w])
  rw [CechPic.lam_pull_of_isGrpPullback h]
  refine (CechPic.pull_lam m c _ _).trans ?_
  congr 1 <;> refine Over.OverMorphism.ext ?_
  exacts [pullback.lift_fst _ _ _, pullback.lift_snd _ _ _]

theorem nonempty_riemannData (Q : Out.PolAV S) (y : Sp ℂ ⟶ S) :
    Nonempty ((ofPolAV Q).RiemannData y) := by
  have h := isGrpPullback_pullback Q.A y
  have hL := pull_isLB Q.isLB (pullback.fst Q.A.hom y)
  obtain ⟨w, hw⟩ := (CechPic.cls_eq_iff hL hL).1 rfl
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := S)
    (x := y (IsLocalRing.closedPoint ℂ)) (U := ⊤) trivial
  let Q' : Out.PolAV (Sp ℂ) := ⟨(Over.pullback y).obj Q.A,
    PolPull.isAbelianScheme_of_isGrpPullback Q.isAb h, Q.g,
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 Q.smoothDim, _, hL,
    PolBaseChange.rigidified_pull h Q.rigid, PolBaseChange.sym_pull h Q.sym,
    relAmple_pull h.1 Q.isLB hL ((isGen_iff w).1 hw) U hU
      (fun z => by rwa [Subsingleton.elim z (IsLocalRing.closedPoint ℂ)]) Q.ample,
    kTriv_pull h Q.isLB hL ((isGen_iff w).1 hw) Q.ktriv⟩
  obtain ⟨rig, hr⟩ := Q'.rigid
  obtain ⟨u, H, χ, -, hH, -⟩ := thetaUnifAV_all Q' rig hr
  exact ⟨⟨Q'.A, _, h, Q'.L, hL, (pull_sqMap_lam h _).trans
    (congrArg (lam · _ _) (CechPic.cls_pull Q.isLB _ hL).symm), u, H, χ, hH⟩⟩

variable (P : PPAS X)

def IsDualRiemann (t : ℝ) (h : VMetric p (omega P.A) P.g) : Prop :=
  ∀ σ (y : CxPts p σ), Nonempty (P.RiemannData y.1) ∧ ∀ (d : P.RiemannData y.1) (U : X.Opens)
    (W : P.A.left.Opens) (hU : U ≤ unitSec P.A ⁻¹ᵁ W) (f f' : Γ(P.A.left, W)), y ∈ ptsIn p σ U →
      (h.met σ).form (dUnit P.A hU f) (dUnit P.A hU f') y =
        form (dualGram ((t : ℂ) • d.H)) (d.cov W f) (d.cov W f')

abbrev IsHodge (h : VMetric p (omega P.A) P.g) : Prop := P.IsDualRiemann Real.pi h

variable {P} {t : ℝ} {h h' : VMetric p (omega P.A) P.g}

theorem IsDualRiemann.unique (H : P.IsDualRiemann t h) (H' : P.IsDualRiemann t h') : h = h' := by
  refine VMetric.ext (funext fun σ => Met.ext_form fun U s s' y hy => ?_)
  obtain ⟨U', W, hx, hle, c⟩ := Conormal.exists_isChart (LieVB.sec_hom (MonObj.one (X := P.A))) (mem_ptsIn.1 hy)
  have hy' : y ∈ ptsIn p σ U' := mem_ptsIn.2 hx
  obtain ⟨f, hf⟩ := c.d_surjective (LieVB.sec_hom (MonObj.one (X := P.A))) (resM (omega P.A) hle s)
  obtain ⟨f', hf'⟩ := c.d_surjective (LieVB.sec_hom (MonObj.one (X := P.A))) (resM (omega P.A) hle s')
  obtain ⟨d⟩ := (H σ y).1
  rw [← Met.form_resM _ s s' hle hy', ← Met.form_resM _ s s' hle hy', ← hf, ← hf']
  exact ((H σ y).2 d U' W c.le f f' hy').trans ((H' σ y).2 d U' W c.le f f' hy').symm

theorem IsDualRiemann.scale (H : P.IsDualRiemann t h) (s : ℝ) :
    P.IsDualRiemann (Real.exp (-s) * t) (h.scale s) := fun σ y => ⟨(H σ y).1,
  fun d U W hU f f' hy => by
    have e : ((Real.exp (-s) : ℂ) • (t : ℂ) • d.H)⁻¹ = (Real.exp s : ℂ) • ((t : ℂ) • d.H)⁻¹ := by
      have e₁ : (Real.exp (-s) : ℂ) * Real.exp s = 1 := by
        rw [← Complex.ofReal_mul, ← Real.exp_add]; simp
      by_cases hu : IsUnit ((t : ℂ) • d.H).det
      · exact inv_eq_right_inv (by rw [smul_mul_smul_comm, e₁, mul_nonsing_inv _ hu, one_smul])
      · rw [nonsing_inv_apply_not_isUnit _ hu, smul_zero, nonsing_inv_apply_not_isUnit]
        rw [det_smul]
        exact fun h => hu (isUnit_of_mul_isUnit_right h)
    refine ((h.met σ).form_expMul _ _ _ y).trans ?_
    rw [(H σ y).2 d U W hU f f' hy, Complex.ofReal_mul, mul_smul, dualGram, dualGram, e,
      transpose_smul, form_smul]⟩

theorem IsHodge.flat (H : P.IsHodge h) :
    P.IsDualRiemann (1 / 2) (h.scale (Real.log (2 * Real.pi))) := by
  convert H.scale (Real.log (2 * Real.pi)) using 1
  rw [Real.exp_neg, Real.exp_log (by positivity)]
  field_simp

variable (P p) [IsIntegral X]

def IsCh2Omega (a : ℝ) : Prop := ∃ h : VMetric p (omega P.A) P.g, P.IsHodge h ∧ h.IsCh2Deg a

def ch2Omega : ℝ := Classical.epsilon (P.IsCh2Omega p)

omit [IsIntegral X] in

def degOmega : ℤ := cxDeg p (omega P.A) P.g

variable {P p} {a b : ℝ}

theorem IsCh2Omega.unique (ha : P.IsCh2Omega p a) (hb : P.IsCh2Omega p b) : a = b := by
  obtain ⟨h, H, ha⟩ := ha
  obtain ⟨h', H', hb⟩ := hb
  exact ha.unique (H.unique H' ▸ hb)

theorem IsCh2Omega.ch2Omega_eq (ha : P.IsCh2Omega p a) : P.ch2Omega p = a :=
  IsCh2Omega.unique (Classical.epsilon_spec ⟨a, ha⟩) ha

theorem IsHodge.ch2Omega_eq (H : P.IsHodge h) (ha : h.IsCh2Deg a) : P.ch2Omega p = a :=
  IsCh2Omega.ch2Omega_eq ⟨h, H, ha⟩

end PPAS

example (W : _root_.WeierstrassCurve ℂ) [W.IsElliptic] :
    (PPAS.ofPolAV (WeierstrassCurve.ellPolAV W)).g = 1 ∧
      Nonempty ((PPAS.ofPolAV (WeierstrassCurve.ellPolAV W)).RiemannData (𝟙 _)) :=
  ⟨rfl, PPAS.nonempty_riemannData _ _⟩

example : dualGram ((Real.pi : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = (1 / Real.pi : ℂ) • 1 := by
  rw [dualGram, inv_eq_right_inv (B := (1 / Real.pi : ℂ) • 1), transpose_smul, transpose_one]
  rw [smul_mul_smul_comm, mul_one, mul_one_div_cancel (by simp), one_smul]

end GlobalTheory
