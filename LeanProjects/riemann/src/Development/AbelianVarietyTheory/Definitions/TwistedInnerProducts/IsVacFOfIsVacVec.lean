import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.LoweredSignatureVanishing
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.Size GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators
open scoped ENNReal

namespace GlobalTheory.ChainFr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

structure Fr (V : HSp D) where

  ε : D.what₂.Tau → Fin V.rank → Bool

  fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ
  fr_unit : ∀ τ, IsUnit (fr τ)
  fr_gram : ∀ τ, (fr τ)ᴴ * Formalism.REAL.Jm (ε τ) * fr τ = gramAt D V τ

namespace Fr

variable {V : HSp D}

def ofModel {S : D.what₂.Tau → SPar} (M : DSModel V S) : Fr V := ⟨M.ε, M.fr, M.fr_unit, M.fr_gram⟩

def cart (A : Fr V) (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin V.rank) ℂ :=
  (A.fr τ)⁻¹ * Formalism.REAL.Jm (A.ε τ) * A.fr τ

def onb (A : Fr V) (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin V.rank) ℂ := (A.fr τ)⁻¹

def elt (θ : InfFam D) (A : Fr V) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) : GA D V :=
  atTau θ V τ ((A.fr τ)⁻¹ * g * A.fr τ)

end Fr

section Clauses

variable {V W : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : Fr V) (B : Fr W)

def ptF (f : WO V W → ℂ) : PolF D W.rank V.rank → (WO V W → ℂ) :=
  pureTensorO ψ θ V W A.cart B.cart A.onb B.onb f

def IsVacF (f : WO V W → ℂ) : Prop :=
  IsThetaFunO ψ V W f ∧ ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) f

variable (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau)

def LieFockWith (κS : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ) (κT : Matrix (Fin W.rank) (Fin W.rank) ℂ → ℂ) : Prop :=
  (∀ X ∈ lieAt V τ, ∀ (P : PolF D W.rank V.rank) (z : WO V W),
    HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) (ptF ψ θ A B f P) z)
      (ptF ψ θ A B f (fockS τ (A.ε τ) (B.ε τ) ((A.fr τ * X * (A.fr τ)⁻¹).map (starRingEnd ℂ)) P + κS X • P) z) 0) ∧
  ∀ Y ∈ lieAt W τ, ∀ (P : PolF D W.rank V.rank) (z : WO V W),
    HasDerivAt (fun t : ℝ => ω (1, oneP θ W τ Y t) (ptF ψ θ A B f P) z)
      (ptF ψ θ A B f (fockT τ (A.ε τ) (B.ε τ) (B.fr τ * Y * (B.fr τ)⁻¹) P + κT Y • P) z) 0

def CompactFockF (aS aT : ℚ) : Prop :=
  ∃ x y : Bool → ℤ, (∀ j, (x (A.ε τ j) : ℚ) = wtS (B.ε τ) aT (A.ε τ j)) ∧
    (∀ i, (y (B.ε τ i) : ℚ) = wtT (A.ε τ) aS (B.ε τ i)) ∧
    ∀ h ∈ Formalism.REAL.Kset (A.ε τ), ∀ k ∈ Formalism.REAL.Kset (B.ε τ), ∀ P : PolF D W.rank V.rank,
      ω (A.elt θ τ h, B.elt θ τ k) (ptF ψ θ A B f P) =
        (signBlockDeterminant (A.ε τ) true h ^ x true * signBlockDeterminant (A.ε τ) false h ^ x false *
          (signBlockDeterminant (B.ε τ) true k ^ y true * signBlockDeterminant (B.ε τ) false k ^ y false)) •
          ptF ψ θ A B f (subst τ (A.ε τ) (B.ε τ) (h.map (starRingEnd ℂ)) k P)

end Clauses

def LieFockUpTo (D : D7) : Prop :=
  ∀ (V W : HSp D) (A : Fr V) (B : Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ V W χS χT ω →
    ∃ κS κT, ∀ f, IsVacF ψ θ A B f → LieFockWith ψ θ A B ω f τ κS κT

def LieFockAll (D : D7) : Prop :=
  ∀ (V W : HSp D) (A : Fr V) (B : Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ),
    IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → HasInfExp D χS τ aS → HasInfExp D χT τ aT → IsVacF ψ θ A B f →
      LieFockWith ψ θ A B ω f τ (fun X => -((aT : ℂ) * X.trace)) fun Y => (aS : ℂ) * Y.trace

def CompactFockAll (D : D7) : Prop :=
  ∀ (V W : HSp D) (A : Fr V) (B : Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ) (τ : D.what₂.Tau) (aS aT : ℚ),
    IsInfFam θ → IsWeilDatumO ψ V W χS χT ω → HasInfExp D χS τ aS → HasInfExp D χT τ aT → IsVacF ψ θ A B f → f ≠ 0 →
      CompactFockF ψ θ A B ω f τ aS aT

def fockSpan {V W : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : Fr V) (B : Fr W)
    (U : AddSubgroup (WO V W)) : Submodule ℂ (WO V W → ℂ) :=
  Submodule.span ℂ {g | ∃ f₀ P, IsVacF ψ θ A B f₀ ∧ f₀ ∈ thetaLevel ψ V W U ∧ g = ptF ψ θ A B f₀ P}

def FockDense (D : D7) : Prop :=
  ∀ (V W : HSp D) (A : Fr V) (B : Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → ∀ f, IsThetaFunO ψ V W f →
      ∃ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) ∧ f ∈ thetaLevel ψ V W U ∧
        ∀ (d : ℕ) (δ : ℝ≥0∞), 0 < δ → ∃ g ∈ fockSpan ψ θ A B U, g ∈ thetaLevel ψ V W U ∧ sobO ψ θ μ 𝓕 d (f - g) < δ

def LowVanishFock (D : D7) : Prop :=
  ∀ (k : Fin D.R.m) (i : ℕ) (V' W : HSp D) (M' : DSModel W (parB (Ptw D) (k + 1)))
    (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → ChainPar D k →
    1 ≤ i → GlobalTheory.IndefiniteRowSideFullHecke.LoweredSignatureVanishing.SigLowered (parB (Ptw D) k) i V' →
    ∀ ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ), IsStepWeil k ψ V' W ω' →
    ∀ (ν : Measure (GA D W)) (𝓕 : Set (GA D W)), ν.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕 ν →
    ∀ (J : Set (GA D W)) (χ : GA D W → ℂ), ∀ F ∈ MultT θ M' J χ, ∀ (v : SmT M') (A : Fr V') (f₀ : WO V' W → ℂ),
      IsVacF ψ θ A (Fr.ofModel M') f₀ → ∀ P,
        Lift.liftInt ν 𝓕 (thetaKO ω') (ptF ψ θ A (Fr.ofModel M') f₀ P) (F v) = 0

theorem ptF_ofModel {V W : HSp D} {S S' : D.what₂.Tau → SPar} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ) :
    ptF ψ θ (Fr.ofModel M) (Fr.ofModel M') f = ptOf ψ θ M M' f := rfl

theorem isVacF_of_isVacVec {V W : HSp D} {S S' : D.what₂.Tau → SPar} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {M : DSModel V S} {M' : DSModel W S'} {f : WO V W → ℂ} (h : IsVacVec ψ θ M M' f) :
    IsVacF ψ θ (Fr.ofModel M) (Fr.ofModel M') f := ⟨h.theta, h.vac⟩

def posFr (D : D7) (n : ℕ) : Fr (posSp D n) where
  ε _ _ := true
  fr _ := 1
  fr_unit _ := isUnit_one
  fr_gram τ := by
    rw [gramAt_posSp]
    ext a b
    simp [Formalism.REAL.Jm, Matrix.diagonal_apply, Matrix.one_apply]

end GlobalTheory.ChainFr

end
