import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.SArith
import Formalism.FormalDegreeBessel.StatementDS
import Formalism.RealPlaceAnalysis.SmoothOnGVIff

open MeasureTheory NumberField Matrix
open scoped TensorProduct InnerProductSpace
open Formalism.MainNotions.S

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IsotropicFlagConstantTerms

def perp {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (JA : Matrix (Fin n) (Fin n) A)
    (WA : Submodule A (Fin n → A)) : Set (Fin n → A) :=
  {y | ∀ x ∈ WA, Formalism.UG.hform s JA x y = 0}

def TrivOnFlag {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (JA : Matrix (Fin n) (Fin n) A)
    (r : ℕ) (WA : ℕ → Submodule A (Fin n → A)) (g : Matrix (Fin n) (Fin n) A) : Prop :=
  (∀ i < r, ∀ x ∈ WA (i + 1), (g - 1) *ᵥ x ∈ WA i) ∧
    (∀ y ∈ perp s JA (WA r), (g - 1) *ᵥ y ∈ WA r) ∧
    ∀ i < r, ∀ y ∈ perp s JA (WA i), (g - 1) *ᵥ y ∈ perp s JA (WA (i + 1))

variable (I : AutInst)

def IsIsotFlag (r : ℕ) (W : ℕ → Submodule I.E (Fin I.n → I.E)) : Prop :=
  1 ≤ r ∧ W 0 = ⊥ ∧ (∀ i < r, W i < W (i + 1)) ∧
    ∀ x ∈ W r, ∀ y ∈ W r, Formalism.UG.hform (starRingEnd I.E) I.J x y = 0

def flagNA (r : ℕ) (W : ℕ → Submodule I.E (Fin I.n → I.E)) : Set I.GA :=
  {x | (∀ v, TrivOnFlag (starRingEnd ℂ) (I.J.map (I.φ v)) r
      (fun i => Submodule.span ℂ ((fun w : Fin I.n → I.E => fun a => I.φ v (w a)) '' (W i : Set _)))
      (I.P v * uMat (x.1 v) * (I.P v)⁻¹)) ∧
    TrivOnFlag (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))) r
      (fun i => Submodule.span (I.E ⊗[I.F] Af I.F)
        ((fun w : Fin I.n → I.E => fun a => Formalism.UG.inclE (F := I.F) (Af I.F) (w a)) '' (W i : Set _)))
      (I.fmat x.2)}

def IsFlagQuotMeas (r : ℕ) (W : ℕ → Submodule I.E (Fin I.n → I.E)) (ν : Measure I.GA) : Prop :=
  IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν (flagNA I r W)ᶜ = 0 ∧
    ∀ S : Set I.GA, MeasurableSet S → (∀ γ ∈ I.GFset ∩ flagNA I r W, ∀ y, γ * y ∈ S ↔ y ∈ S) →
      ∀ n₀ ∈ flagNA I r W, ν {m | m * n₀ ∈ S} = ν S

def ConstTermsVanish (f : I.GA → ℂ) : Prop :=
  ∀ (r : ℕ) (W : ℕ → Submodule I.E (Fin I.n → I.E)), IsIsotFlag I r W →
    ∀ ν : Measure I.GA, IsFlagQuotMeas I r W ν →
      ∀ x : I.GA, Integrable (fun m => f (m * x)) ν ∧ ∫ m, f (m * x) ∂ν = 0

def IsCuspClass (μf : Measure I.Gf) [SigmaFinite μf] (fund : Set I.GA) (Fv : I.L2 μf fund) : Prop :=
  ∃ f : I.GA → ℂ, Continuous f ∧ (∀ γ ∈ I.GFset, ∀ y, f (γ * y) = f y) ∧
    (Fv : I.GA → ℂ) =ᵐ[(I.muA μf).restrict fund] f ∧ ConstTermsVanish I f

section Test

variable {H : InfinitePlace I.F → Type} [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]

def dSigma (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) : ℝ :=
  ∏ v, fdegOf (Formalism.REAL.muG (I.ε v)) (σ v) (w v)

def ph (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) : I.Ginf → ℂ :=
  fun g => (dSigma I σ w : ℂ) * star (∏ v, coefOn (ε := I.ε v) (σ v) (w v) (w v) (g v))

def phE (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v) (e : I.Gf → ℂ) :
    I.GA → ℂ :=
  fun g => ph I σ w g.1 * e g.2

end Test

def IsIdemInK (μf : Measure I.Gf) (e : I.Gf → ℂ) : Prop :=
  IsLocallyConstant e ∧ I.convF μf e e = e ∧ (∀ x, e x⁻¹ = star (e x)) ∧ ∀ x, e x ≠ 0 → x ∈ I.Kset

def gapThreshold (C : ℝ) (p q : ℕ) : ℝ :=
  max (120 * ((p + q : ℕ) : ℝ) * ((min p q : ℕ) : ℝ) ^ ((3 : ℝ) / 2))
    (C * ((p + q : ℕ) : ℝ) ^ 2 * ((min p q : ℕ) : ℝ) ^ ((1 : ℝ) / 2))

def ProjectorWith (C : ℝ)
    (Side : ∀ I : AutInst, (InfinitePlace I.F → Fin I.n → ℝ) → Measure I.Gf → (I.Gf → ℂ) → Prop) : Prop :=
  ∀ (I : AutInst) (p q : ℕ), (∀ v, I.pAt v = p ∧ I.qAt v = q) →
  ∀ (lam : InfinitePlace I.F → Fin I.n → ℝ) (H : InfinitePlace I.F → Type)
    [∀ v, NormedAddCommGroup (H v)] [∀ v, InnerProductSpace ℂ (H v)]
    (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v)) (w : ∀ v, H v),
    (∀ v, Formalism.QuantumDeterminants.IsHCParam (lam v)) → (∀ v, IsDS (I.ε v) (lam v) (σ v)) →
    (∀ v, IsLowUnit (I.ε v) (lam v) (σ v) (w v)) →
  ∀ h : ℝ, (∀ v, Formalism.QuantumDeterminants.GapAtLeast (I.ε v) (lam v) h) → gapThreshold C p q ≤ h →
  ∀ (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs), I.IsHilbTensor σ σs tens →
  ∀ (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA),
    I.IsFundDom (I.muA μf) fund →
  ∀ R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRightReg μf fund R →
  ∀ e : I.Gf → ℂ, Side I lam μf e →
  ∀ Re : I.L2 μf fund →L[ℂ] I.L2 μf fund, I.IsRConvF μf fund R e Re →
    Integrable (ph I σ w) (Measure.pi fun v => Formalism.REAL.muG (I.ε v)) ∧
    ∃ T : I.L2 μf fund →L[ℂ] I.L2 μf fund, I.IsRConv μf fund R (phE I σ w e) T ∧
      ∃ S : Submodule ℂ (I.L2 μf fund), IsOrthProjOnto T S ∧
        FiniteDimensional ℂ S ∧ FiniteDimensional ℂ (I.eHom σs μf fund R Re) ∧
        Module.finrank ℂ S = I.Dcount σs μf fund R Re ∧
        ∀ Fv ∈ S, IsCuspClass I μf fund Fv ∧ I.IsCuspFn (I.muA μf) (I.ext Fv)

def WideSide (I : AutInst) (_ : InfinitePlace I.F → Fin I.n → ℝ) (μf : Measure I.Gf) (e : I.Gf → ℂ) : Prop :=
  IsIdemInK I μf e

def CountSide (Cg : ℝ) (I : AutInst) (lam : InfinitePlace I.F → Fin I.n → ℝ) (μf : Measure I.Gf)
    (e : I.Gf → ℂ) : Prop :=
  ∃ (b : ℝ) (g g₀ : ℕ), 2 ≤ b ∧ (∀ v a, |lam v a| ≤ b ^ 2) ∧ 1 ≤ g ∧ (g : ℝ) ≤ b ^ Cg ∧
    g₀.Prime ∧ 4 * I.n < g₀ ∧ SplitsCompl I.E g₀ ∧ I.IsAdmIdem μf g g₀ e

def GlobalProjectorFor (C : ℝ) : Prop := ProjectorWith C WideSide

def GlobalProjector : Prop := GlobalProjectorFor 40

def GlobalProjectorSome : Prop := ∃ C : ℝ, 0 < C ∧ GlobalProjectorFor C

def CountProjectorFor (C : ℝ) : Prop := ∀ Cg : ℝ, ProjectorWith C (CountSide Cg)

def CountProjector : Prop := CountProjectorFor 40

def CountProjectorSome : Prop := ∃ C : ℝ, 0 < C ∧ CountProjectorFor C

end GlobalTheory.IndefiniteRowSideFullHecke.IsotropicFlagConstantTerms
