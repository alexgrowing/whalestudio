import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CommutingLevelOperators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LabelSettingScalars

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar

namespace GlobalTheory.LiftRows

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev Eig (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

structure Given (F : Face D A) : Prop where
  core : GlobalTheory.Hk3.Core R F
  params : ∃ L : SizeData₂ D, Nonempty (ParameterChoice' D L)
  irr : ∀ χ ∈ A.X, IsAbsIrrChar χ
  types : GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R
  guard : FWT.QGuard R
  gapR : ∀ (τ : D.what₂.Tau) (n : ℕ), n + 1 < D.R.r →
    100 * (D.R.r : ℚ) ^ 4 ≤ Formalism.L2.NTheta.lamAt (D.hc τ) n - Formalism.L2.NTheta.lamAt (D.hc τ) (n + 1)

def IsLval (i : Fin D.R.m) (t : T) (c : Eig D) (z : ℝ) : Prop :=
  ∃ B, GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) D.R.r c B ∧ GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.IsLValue R t B ((i : ℕ) + 1) z

variable (SF : Finset (HeightOneSpectrum (𝓞 D.host.F)))

def AForm : Prop :=
  ∃ a : Fin D.R.m → ℝ, (∀ i, 0 < a i) ∧ ∀ i t c, GlobalTheory.Hk3.Wcc R SF i c ≠ ⊥ → ∃ z : ℝ, IsLval R i t c z ∧
    ∀ x ∈ GlobalTheory.Hk3.Wcc R SF i c, R.thG i t (LinearMap.adjoint (R.thG i t) x) = ((a i * z : ℝ) : ℂ) • x

def BForm : Prop :=
  ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ t c (z : Fin D.R.m → ℝ), (∀ i, IsLval R i t c (z i)) →
    ∀ x ∈ GlobalTheory.Hk3.EEc R SF c, R.Th t (LinearMap.adjoint (R.Th t) x) = ((κ₀ * ∏ i, z i : ℝ) : ℂ) • x

def Scal : Prop :=
  ∃ (lam : Fin D.R.m → T → Eig D → ℝ) (κ : ℝ), 0 < κ ∧ (∀ i t c, 0 < lam i t c) ∧
    (∀ i t c, ∀ x ∈ GlobalTheory.Hk3.Wcc R SF i c, R.thG i t (LinearMap.adjoint (R.thG i t) x) = ((lam i t c : ℝ) : ℂ) • x) ∧
    ∀ t c, ∀ x ∈ GlobalTheory.Hk3.EEc R SF c, R.Th t (LinearMap.adjoint (R.Th t) x) = ((κ * ∏ i, lam i t c : ℝ) : ℂ) • x

def Kept : Prop :=
  ∀ t c, ∀ x ∈ GlobalTheory.Hk3.EEc R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c,
    R.Th t (LinearMap.adjoint (R.Th t) x) ∈ GlobalTheory.Hk3.EEc R (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t) c

def MatchUp : Prop := ∀ c, GlobalTheory.Hk3.EEc R SF c ≠ ⊥ → ∀ i, GlobalTheory.Hk3.Wcc R SF i c ≠ ⊥

def RowsNe (F : Face D A) : Prop := ∀ b, R.EEat (R.levR F b) ≠ ⊥

def UpInj : Prop := ∀ t, Function.Injective (LinearMap.adjoint (R.Th t))

def UpInjW : Prop :=
  ∀ i t x, GlobalTheory.Hk3.eH R i x = x → LinearMap.adjoint (R.thG i t) x = 0 → x = 0

def GoodV (i : Fin D.R.m) (y : (R.HV i A.μ0).H) : Prop :=
  ∀ ℓ : (R.cV i).W →ₗ[ℂ] ℂ,
    gaL (Vc D i) (R.βV i) (R.datVt i A.μ0) R.eG (RealDat.eC (A := A) (sg0 D A)) (fun h => ℓ (R.extV i A.μ0 y h)) =
      fun h => ℓ (R.extV i A.μ0 y h)

def LiftInj : Prop :=
  ∀ i h, GlobalTheory.Hk3.IsOpsV R i A.μ0 h → ∀ s : Eig D, ∀ x y : (R.HV i A.μ0).H,
    (∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.Hk3.IsLab (Vc D i) P d → h P (Finsupp.single d 1) x = s P d • x) →
    (∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.Hk3.IsLab (Vc D i) P d → h P (Finsupp.single d 1) y = s P d • y) →
    R.thG i A.μ0 x ≠ 0 → GoodV R i y → R.thG i A.μ0 y = 0 → y = 0

def IsLiftDataC (F : Face D A) (i : Fin D.R.m) (t : T) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (P : LevelP R.Pg D.R.r ℂ)
    (cμ cη : (AE D)ˣ →* Circle) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
    (BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ)
    (c : CoefA (Vc D i)) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) : Prop :=
  GlobalTheory.Hk3.Core R F ∧ PrimeToHost R t ∧ IsEmbOverK D σ s ∧ IsLocalLevel P ∧ IsConjChars R i t s cμ cη m ∧
    Datum.IsWeilDatumO R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω ∧
    (∀ ρ, Datum.IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (BW ρ) (pW D i ρ)) ∧
    IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i P) (R.Q t) m f₀ f ∧
    Lift.PtTheta R.ψ (Vc D i) (Wc D i) (ptAt R i σ BW f) ∧ c.Is ∧
    IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ BW f) (deltaAtEmb D i σ) io

def ForLiftDataC (F : Face D A)
    (Φ : ∀ (i : Fin D.R.m) (_t : T) (σ : D.what₂.LL →+* ℂ) (_P : LevelP R.Pg D.R.r ℂ) (_m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
      (_ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
      (_BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (_f : Datum.WO (Vc D i) (Wc D i) → ℂ)
      (c : CoefA (Vc D i)) (_io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), Prop) : Prop :=
  ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → Φ i t σ P m ω BW f c io

def SourceLevelLawC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i t σ P m ω BW f _ _ =>
    ∀ κ ∈ Lev.levA (Vc D i) (levV R i t P m), ∀ Q : PolF D (Wc D i).rank (Vc D i).rank,
      ω (κ, 1) (ptAt R i σ BW f Q) = (Lev.levChi (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m) κ)⁻¹ • ptAt R i σ BW f Q

open Datum in

def InnerProductFormulaC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i t σ P m ω BW f _ _ =>
    ∀ (ν : Measure (GA D (Vc D i))) (𝓕 : Set (GA D (Vc D i))), IsMeasDef (Vc D i) (levV R i t P m) ν 𝓕 →
    ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
    ∀ Fr : Frames (Wc D i), IsFrames (Wc D i) Fr → ∀ mR : ∀ ρ, Measure (Upq (Wc D i) ρ), (∀ ρ, Lev.IsMinf (mR ρ)) →
    ∀ U₁ ∈ R.Wall i σ, ∀ U₂ ∈ R.Wall i σ, ∀ (v₁ v₂ : ∀ ρ, lowT (R.MW i σ) ρ) (Q₁ Q₂ : PolF D (Wc D i).rank (Vc D i).rank),
      let φ₁ := ptAt R i σ BW f Q₁
      let φ₂ := ptAt R i σ BW f Q₂
      let F₁ := U₁ fun ρ => v₁ ρ
      let F₂ := U₂ fun ρ => v₂ ρ
      let Z : GA D (Wc D i) → ℂ := fun g => l2 μ 𝓧 (ω (1, g) φ₁) φ₂ * starRingEnd ℂ (petW R i (rTr (Wc D i) g F₁) F₂)
      let pt : FinCos (Wc D i) (levW R i) → (∀ ρ, Upq (Wc D i) ρ) → GA D (Wc D i) := fun x b =>
        x.rep * realElt R.θ (Wc D i) fun ρ => realMat (Wc D i) Fr ρ (b ρ)
      (∀ h, IntegrableOn (fun g => thetaKO ω h g φ₁ * starRingEnd ℂ (F₁ g)) (R.fdW i) (R.νW i)) ∧
      IntegrableOn (fun h => upLift R i ω φ₁ F₁ h * starRingEnd ℂ (upLift R i ω φ₂ F₂ h)) 𝓕 ν ∧
      ∫⁻ b, ∑' x, ‖Z (pt x b)‖ₑ ∂(Measure.pi mR) < ⊤ ∧
      l2 ν 𝓕 (upLift R i ω φ₁ F₁) (upLift R i ω φ₂ F₂) = ((ν 𝓕).toReal : ℂ) * ∫ b, ∑' x, Z (pt x b) ∂(Measure.pi mR)

open Datum in

def FockCoefficientC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i _ σ _ _ ω BW f c io =>
    ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
    ∀ x ∈ GfC (Wc D i), ∀ g : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ,
      (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) ρ)) → ∀ (e e' : ∀ ρ, lowT (R.MW i σ) ρ) (w w' : c.W),
      l2 μ 𝓧 (ω (1, x * realElt R.θ (Wc D i) g) (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e) w)))
          (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e') w')) =
        Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) *
          (∏ ρ, ⟪((e' ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ), (R.MW i σ).rep ρ (g ρ) ((e ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ) *
          ⟪w', w⟫_ℂ * l2 μ 𝓧 (ω (1, x) f) f

open Datum in

def FiniteZetaL (F : Face D A) : Prop :=
  ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io →
    ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
    ∀ ev : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, typePart R i σ t P ev ≠ ⊥ →
      ∃ B : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsSysParamD D (finS R t) D.R.r ev B ∧
        (∀ w, OffS D (finS R t) w → ∀ β ∈ B w, ‖(β : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2)) ∧
        GlobalTheory.LFun.Converges (GlobalTheory.LFun.above D.host.E (finS R t : Set (HeightOneSpectrum (𝓞 D.host.F))))
          (GlobalTheory.LFun.twist B (GlobalTheory.LFun.val cμ)⁻¹) ((1 + (D.R.t : ℂ)) / 2) ∧
        ∀ U₁ ∈ partFull R.θ (R.MW i σ) (levS _ (R.βW i) (R.datWp i P)) (Lev.levChi _ (R.βW i) (R.datWp i P)) (finS R t) ev,
        ∀ U₂ ∈ R.Wall i σ, ∀ v₁ v₂ : (R.MW i σ).Vec,
          HasSum (fun y : FinCos (Wc D i) (levW R i) =>
              l2 μ 𝓧 (ω (1, y.rep) f) f * starRingEnd ℂ (petW R i (rTr (Wc D i) y.rep (U₁ v₁)) (U₂ v₂)))
            ((Nat.card P.H : ℂ) * (nrm2 μ 𝓧 f : ℂ) * (GlobalTheory.LFun.LSD D (finS R t) B cμ ((1 + (D.R.t : ℂ)) / 2) / (dOff D (finS R t) : ℂ)) *
              starRingEnd ℂ (petW R i (U₁ v₁) (U₂ v₂)))

open Datum in

def LevelIndexNormC (F : Face D A) : Prop :=
  ForLiftDataC R F fun i t _ P m _ _ f _ _ =>
    levV R i t P m ≤ GlobalTheory.Mass.Levels.latLev (Vc D i) ∧
    ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 →
      (((levV R i t P m).relIndex (GlobalTheory.Mass.Levels.latLev (Vc D i)) : ℕ) : ℝ) * nrm2 μ 𝓧 f = ∏ v ∈ finS R t, (dLoc D v)⁻¹

def RealLowestKTypeCoeffSquareIntegrable : Prop :=
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau), ∃ δ : ℝ, 0 < δ ∧
    ∀ Fr : Frames (Wc D i), IsFrames (Wc D i) Fr → ∀ mR : Measure (Upq (Wc D i) ρ), Lev.IsMinf mR →
    ∀ e : lowT (R.MW i σ) ρ, ‖((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1 →
      let k : Upq (Wc D i) ρ → ℝ := fun b => ‖⟪((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ),
        (R.MW i σ).rep ρ (realMat (Wc D i) Fr ρ b) ((e : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ‖ ^ 2
      Integrable k mR ∧ ∫ b, k b ∂mR = δ

end GlobalTheory.LiftRows

end
