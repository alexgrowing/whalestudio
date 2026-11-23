import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TwistedLevelValues
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LiftFormsMainTerm
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBaseChangeFiniteAdeleRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeCharacterOfUnitaryTensorIdelesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HookProductPosLogEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsFiniteStabilisers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsHilbertModuleExists

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open Formalism.L2.Host (HChar ordF atFin IsUnitAt)
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.AdelicLiftCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem chrEq_mul {c c' : (AE D)ˣ →* Circle} {χ χ' : HChar D.host.E} (h : ChrEq c χ) (h' : ChrEq c' χ') :
    ChrEq (c * c') (χ * χ') := by
  refine ⟨⟨h.1.1.mul h'.1.1, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · rw [MonoidHom.mul_apply, h.1.2, h'.1.2, one_mul]
  · rw [MonoidHom.mul_apply, Circle.coe_mul, h.2 P e he k x hx, h'.2 P e he k x hx, ← Units.val_mul]
    rfl

section Places

variable {T : Type} {L : LevCh D T} {μ0 : T} (hL : L.Is μ0)
include hL

end Places

section Generic

variable {G H W : Type} [Group G] [Group H] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (π : G →* H) (ρ : G →* Module.End ℂ W)

end Generic

section Forms

variable {V : HSp D} (c : CoefA V) (hc : c.Is) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)

include hc

end Forms

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

def IsResidual (i : Fin D.R.m) (t : T) (s : ℂ →+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Prop :=
  (∀ PP ∈ R.Pg, m PP = (LiftFormsMainTerm.conjRes s (R.chi ((i : ℕ) + 1)) PP)⁻¹) ∧ ∀ PP ∈ R.Q t, m PP = LiftFormsMainTerm.conjRes s (R.xiR t) PP

variable {R}

section Residual

variable {i : Fin D.R.m} {t : T} {s : ℂ →+* ℂ} {m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} (hm : IsResidual R i t s m)
  (P : LevelP R.Pg D.R.r ℂ)

include hm

end Residual

section Concl

variable {i : Fin D.R.m} {σ : D.what₂.LL →+* ℂ}

def FirstConcl (b : ℝ) (t : T) (P : LevelP R.Pg D.R.r ℂ)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
    (pt : PolF D (Wc D i).rank (Vc D i).rank → (Datum.WO (Vc D i) (Wc D i) → ℂ)) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)
    (ν : Measure (GA D (Vc D i))) (𝓕 : Set (GA D (Vc D i))) (HV : HMod (Bridge.Gf (Vc D i) → c.W)) : Prop :=
  (∃ th, TwistedLevelValues.IsLift R i σ ω pt c io ν 𝓕 HV th) ∧
    ∀ th, TwistedLevelValues.IsLift R i σ ω pt c io ν 𝓕 HV th →
      ∀ ev : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, TwistedLevelValues.typePart R i σ t P ev ≠ ⊥ →
        ∃ l : ℝ, 0 < l ∧ (∀ x ∈ TwistedLevelValues.typePart R i σ t P ev, th (TwistedLevelValues.adjLev P th x) = (l : ℂ) • x) ∧
          TwistedLevelValues.mainTerm D i σ - 8 * (D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * TwistedLevelValues.Lp D b ≤ Real.log l

def SecondConcl (b : ℝ) (t : T) (s : ℂ →+* ℂ) (P : LevelP R.Pg D.R.r ℂ) (X : LiftFormsMainTerm.LiftInput R i σ) : Prop :=
  (∃ th : X.src t s P →ₗ[ℂ] (R.HW i σ).H, X.IsLift th) ∧
    ∀ th : X.src t s P →ₗ[ℂ] (R.HW i σ).H, X.IsLift th →
      ∀ c, LiftFormsMainTerm.typePart R i σ t P c ≠ ⊥ →
        ∃ l : ℝ, X.ActsBy th (LiftFormsMainTerm.typePart R i σ t P c) l ∧ 0 < l ∧
          LiftFormsMainTerm.mainTerm i σ - 8 * ((D.R.f : ℝ) * (D.R.nV : ℝ) ^ 2 * LiftFormsMainTerm.Lpr D b) ≤ Real.log l

variable {t : T} {s : ℂ →+* ℂ} {P : LevelP R.Pg D.R.r ℂ} (X : LiftFormsMainTerm.LiftInput R i σ)
  (HV : HMod (Bridge.Gf (Vc D i) → X.coef.W)) (φ : HV.H ≃ₗ[ℂ] X.src t s P)
  (hφ : ∀ x, (φ x : GA D (Vc D i) → X.coef.W) = X.coef.ext (HV.e x))
  (hip : ∀ x y, IntegrableOn (fun h => ⟪X.coef.ext (HV.e x) h, X.coef.ext (HV.e y) h⟫_ℂ) X.fd X.ν ∧
    ∫ h in X.fd, ⟪X.coef.ext (HV.e x) h, X.coef.ext (HV.e y) h⟫_ℂ ∂X.ν = ⟪x, y⟫_ℂ)

end Concl

variable (R)

def FirstAt (i : Fin D.R.m) (b : ℝ) : Prop :=
  ∀ t : T, TwistedLevelValues.PrimeToHost R t →
  ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ), TwistedLevelValues.IsEmbOverK D σ s →
  ∀ P : LevelP R.Pg D.R.r ℂ, TwistedLevelValues.IsLocalLevel P →
  ∀ (cμ cη : (AE D)ˣ →* Circle) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), TwistedLevelValues.IsConjChars R i t s cμ cη m →
  ∀ ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ),
    Datum.IsWeilDatumO R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω →
  ∀ BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ,
    (∀ ρ, Datum.IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (BW ρ) (TwistedLevelValues.pW D i ρ)) →
  ∀ f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ,
    TwistedLevelValues.IsLevelVec R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) (R.datWp i P) (R.Q t) m
      f₀ f →
    Lift.PtTheta R.ψ (Vc D i) (Wc D i) (TwistedLevelValues.ptAt R i σ BW f) →
  ∀ c : CoefA (Vc D i), c.Is →
  ∀ io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank,
    IsIoW R.θ (R.MW i σ) c ω (TwistedLevelValues.ptAt R i σ BW f) (TwistedLevelValues.deltaAtEmb D i σ) io →
  ∀ (ν : Measure (GA D (Vc D i))) (𝓕 : Set (GA D (Vc D i))),
    IsMeasDef (Vc D i) (lev D.sp.cm (Vc D i).gram (R.βV i) (TwistedLevelValues.datV i R.Pg (R.Q t) P m)) ν 𝓕 →
  ∀ (I : Type) [Fintype I] (y : I → Bridge.Gf (Vc D i)),
    Bridge.IsReps (Bridge.ratF (Vc D i)) (TwistedLevelValues.grpOf (Vc D i) (R.βV i) (TwistedLevelValues.datV i R.Pg (R.Q t) P m)) y →
  ∀ HV : HMod (Bridge.Gf (Vc D i) → c.W),
    HV.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (TwistedLevelValues.grpOf (Vc D i) (R.βV i) (TwistedLevelValues.datV i R.Pg (R.Q t) P m))
        (TwistedLevelValues.chrOf (Vc D i) (R.βV i) (TwistedLevelValues.datV i R.Pg (R.Q t) P m)))
      (Bridge.adInner (Bridge.ratF (Vc D i)) (TwistedLevelValues.grpOf (Vc D i) (R.βV i) (TwistedLevelValues.datV i R.Pg (R.Q t) P m)) y) →
    FirstConcl b t P ω (TwistedLevelValues.ptAt R i σ BW f) c io ν 𝓕 HV

def SecondAt (i : Fin D.R.m) (b : ℝ) : Prop :=
  ∀ (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (t : T), LiftFormsMainTerm.SameOnK σ → (s : ℂ →+* ℂ).comp D.what₂.embLL = σ →
    LiftFormsMainTerm.GoodPlaces R t → ∀ (P : LevelP R.Pg D.R.r ℂ) (X : LiftFormsMainTerm.LiftInput R i σ), X.Is t (s : ℂ →+* ℂ) P →
      TwistedLevelValues.IsLocalLevel P → X.BV = R.BV i → Lift.PtTheta R.ψ (Vc D i) (Wc D i) X.pt → SecondConcl b t (s : ℂ →+* ℂ) P X

variable {R} {F : Face D A}

end GlobalTheory.AdelicLiftCompare

end
