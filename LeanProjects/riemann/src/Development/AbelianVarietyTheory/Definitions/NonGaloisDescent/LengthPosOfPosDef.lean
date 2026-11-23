import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalRingCardinality.PosOfIsomEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.OfChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure Laws (R : RealDat D A Ks) (F : Face D A) : Prop where
  lev : R.toLevCh.Is A.μ0
  grp : R.IsGrp F
  fam : R.IsFam
  models : R.IsModels
  thP : R.IsThP

def ThOnto (R : RealDat D A Ks) : Prop :=
  ∀ i, (Submodule.span ℂ (Set.range (R.jV i A.μ0))).map (R.thF i A.μ0) = R.Wall i (sg0 D A)

def RatSpan (R : RealDat D A Ks) : Prop :=
  ∀ i t, Submodule.span ℂ (Set.range (R.jV i t)) = ⊤

def IsRaw (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (th : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H) : Prop :=
  ∀ x, (R.HW i (sg0 D A)).e (th x) = R.thF i t x

def UpInj (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) : Prop :=
  ∀ th, IsRaw R i t th → Function.Injective (LinearMap.adjoint th)

def part (R : RealDat D A Ks) (i : Fin D.R.m) (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Submodule ℂ (R.HW i (sg0 D A)).H :=
  (partFull R.θ (R.MW i (sg0 D A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) S c).comap
    (R.HW i (sg0 D A)).e

def PartsSpan (R : RealDat D A Ks) (i : Fin D.R.m) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  ⨆ c, part R i S c = ⊤

def InnerPos (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  ∀ th, IsRaw R i t th → ∀ c, ∃ l : ℝ, 0 < l ∧ ∀ x ∈ part R i S c, ∀ y,
    ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ = (l : ℂ) * ⟪x, y⟫_ℂ

def InnerNe (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  ∀ th, IsRaw R i t th → ∀ c, ∃ l : ℂ, l ≠ 0 ∧ ∀ x ∈ part R i S c, ∀ y,
    ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ = l * ⟪x, y⟫_ℂ

def thetaIP {S T' : HSp D} (μ : Measure (WO S T')) (𝓕 : Set (WO S T')) (f f' : WO S T' → ℂ) : ℂ :=
  ∫ w in 𝓕, star (f w) * f' w ∂μ

def upLift {V W : HSp D} (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W)) (𝓖 : Set (GA D W))
    (f : WO V W → ℂ) (φ : GA D W → ℂ) : GA D V → ℂ :=
  fun h => ∫ g in 𝓖, star (thetaKO om h g f) * φ g ∂ν

def RallisConv (D : D7) : Prop :=
  ∀ (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsInfFam θ → IsWeilDatumO ψ V W χV χW om → V.SigOK → V.IsPosDef →
    2 * W.rank < V.rank →
    ∀ (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W))
      (μ : Measure (WO V W)) (𝓕 : Set (WO V W)),
      νV.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓗 νV → νW.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓖 νW →
      μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 μ → μ 𝓕 = 1 →
      ∀ (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ), IsThetaFunO ψ V W f₁ → IsThetaFunO ψ V W f₂ →
        IsAutFunSm θ W φ₁ → IsCuspFun W φ₁ → IsAutFunSm θ W φ₂ → IsCuspFun W φ₂ →
        (∀ h, IntegrableOn (fun g => star (thetaKO om h g f₁) * φ₁ g) 𝓖 νW) ∧
        IntegrableOn (fun h => star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h) 𝓗 νV ∧
        Integrable (fun g => thetaIP μ 𝓕 (om (1, g) f₂) f₁ * ∫ x in 𝓖, star (φ₁ x) * φ₂ (x * g) ∂νW) νW ∧
        ∫ h in 𝓗, star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h ∂νV =
          ((νV 𝓗).toReal : ℂ) * ∫ g, thetaIP μ 𝓕 (om (1, g) f₂) f₁ * (∫ x in 𝓖, star (φ₁ x) * φ₂ (x * g) ∂νW) ∂νW

theorem Laws.of_char {R : RealDat D A Ks} {F : Face D A} (h : R.Char F) : Laws R F :=
  ⟨h.lev, h.grp, h.fam, h.models, h.thP⟩

theorem Laws.of_charTh {R : RealDat D A Ks} {F : Face D A} (h : GlobalTheory.ThetaClauses.CharTh R F) : Laws R F :=
  ⟨h.lev, h.grp, h.fam, h.models, h.thP⟩

theorem Laws.posDef {R : RealDat D A Ks} {F : Face D A} (h : Laws R F) (i : Fin D.R.m) :
    (Vc D i).SigOK ∧ (Vc D i).IsPosDef :=
  ⟨D.sp.V_sig _, h.models.vpos i⟩

theorem length_pos_of_posDef {V : HSp D} (hs : V.SigOK) (hp : V.IsPosDef) (τ : D.host.E →+* ℂ)
    (hτ : ∀ a, τ (star a) = (starRingEnd ℂ) (τ a)) (x : V.V) (hx : x ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ τ (V.hT x x) = (c : ℂ) :=
  V.form_pos hs τ hτ (hp τ) x hx

theorem exists_lift_model {X Z : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Z] [Module ℂ Z]
    (M : HMod Z) {U : Submodule ℂ Z} {ip : Z → Z → ℂ} (H : M.Is U ip) (f : X →ₗ[ℂ] Z) (hm : ∀ x, f x ∈ U) :
    ∃ th : X →ₗ[ℂ] M.H, ∀ x, M.e (th x) = f x := by
  have hm' : ∀ x, f x ∈ LinearMap.range M.e := fun x => H.2.1 ▸ hm x
  exact ⟨(LinearEquiv.ofInjective M.e H.1).symm.toLinearMap ∘ₗ f.codRestrict _ hm', fun x =>
    congrArg Subtype.val ((LinearEquiv.ofInjective M.e H.1).apply_symm_apply (f.codRestrict _ hm' x))⟩

set_option maxHeartbeats 1000000 in

theorem Laws.exists_isRaw {R : RealDat D A Ks} {F : Face D A} (h : Laws R F) (i : Fin D.R.m) (t : T) :
    ∃ th, IsRaw R i t th :=
  exists_lift_model (R.HW i (sg0 D A)) (h.models.HW i (sg0 D A)) (R.thF i t) (h.thP.thF_mem i t)

set_option maxHeartbeats 1000000 in

theorem Laws.isRaw_unique {R : RealDat D A Ks} {F : Face D A} (h : Laws R F) {i : Fin D.R.m} {t : T}
    {th th' : (R.HV i t).H →ₗ[ℂ] (R.HW i (sg0 D A)).H} (h₁ : IsRaw R i t th) (h₂ : IsRaw R i t th') : th = th' :=
  LinearMap.ext fun x => (h.models.HW i (sg0 D A)).1 ((h₁ x).trans (h₂ x).symm)

theorem InnerPos.innerNe {R : RealDat D A Ks} {i : Fin D.R.m} {t : T} {S : Finset (HeightOneSpectrum (𝓞 D.host.F))}
    (h : InnerPos R i t S) : InnerNe R i t S :=
  fun th hth c => (h th hth c).elim fun l H => ⟨l, Complex.ofReal_ne_zero.2 H.1.ne', H.2⟩

theorem thetaInner_smul_left {S T' : HSp D} (μ : Measure (WO S T')) (𝓕 : Set (WO S T')) (a : ℂ) (f f' : WO S T' → ℂ) :
    thetaIP μ 𝓕 (a • f) f' = star a * thetaIP μ 𝓕 f f' := by
  unfold thetaIP
  rw [← integral_const_mul]
  simp only [Pi.smul_apply, smul_eq_mul, star_mul', mul_assoc]

theorem thetaInner_smul_right {S T' : HSp D} (μ : Measure (WO S T')) (𝓕 : Set (WO S T')) (a : ℂ) (f f' : WO S T' → ℂ) :
    thetaIP μ 𝓕 f (a • f') = a * thetaIP μ 𝓕 f f' := by
  unfold thetaIP
  rw [← integral_const_mul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]

theorem upLift_smul {V W : HSp D} (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ν : Measure (GA D W))
    (𝓖 : Set (GA D W)) (f : WO V W → ℂ) (a : ℂ) (φ : GA D W → ℂ) (h : GA D V) :
    upLift om ν 𝓖 f (a • φ) h = a * upLift om ν 𝓖 f φ h := by
  unfold upLift
  rw [← integral_const_mul]
  simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]

end GlobalTheory.RawLift

end
