import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.Doubling
open MeasureTheory Matrix
open scoped TensorProduct ContDiff ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def resL (A B : HSp D) (x : WO (dblSp A) B) : WO A B := Matrix.of fun i j => x i (finSumFinEquiv (Sum.inl j))

def resR (A B : HSp D) (x : WO (dblSp A) B) : WO A B := Matrix.of fun i j => x i (finSumFinEquiv (Sum.inr j))

def lagr (A B : HSp D) (w : WO A B) : WO (dblSp A) B :=
  Matrix.of fun i j => Sum.elim (fun k => w i k) (fun k => -w i k) (finSumFinEquiv.symm j)

def delta (A B : HSp D) (f₁ f₂ : WO A B → ℂ) : WO (dblSp A) B → ℂ :=
  fun x => f₁ (resL A B x) * conj (f₂ (-resR A B x))

def ip (A B : HSp D) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (f₁ f₂ : WO A B → ℂ) : ℂ :=
  ∫ w in 𝓕, f₁ w * conj (f₂ w) ∂ν

def evZero (A B : HSp D) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (φ : WO (dblSp A) B → ℂ) : ℂ :=
  ∫ w in 𝓕, φ (lagr A B w) ∂ν

def swSec (A B : HSp D) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ))
    (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (φ : WO (dblSp A) B → ℂ) : GA D (dblSp A) → ℂ :=
  fun g => evZero A B ν 𝓕 (omh (g, 1) φ)

def sZero (A B : HSp D) : ℂ := ((B.rank : ℂ) - (A.rank : ℂ)) / 2

def IsKFinVec {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (K : Subgroup (GA D S))
    (φ : WO S T → ℂ) : Prop :=
  FiniteDimensional ℂ (Submodule.span ℂ {f : WO S T → ℂ | ∃ k ∈ K, f = om (k, 1) φ})

def IsSmoothOn (V : HSp D) (Φ : GA D V → ℂ) : Prop :=
  Continuous Φ ∧
  (∃ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) ∧ ∀ k ∈ U, k ∈ GfC V → ∀ g, Φ (g * k) = Φ g) ∧
  ∀ θ : InfFam D, IsInfFam θ →
    ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ),
      (∀ i, Xs i ∈ lieAt V (τs i)) → ∀ g,
        ContDiff ℝ ∞ fun t : Fin k → ℝ => Φ (g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod)

section Clauses

variable (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle)
  (om : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ))
  (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ))

def ThetaClause : Prop :=
  ∀ f₁ f₂, IsThetaFunO ψ A B f₁ → IsThetaFunO ψ A B f₂ →
    IsThetaFunO ψ (dblSp A) B (delta A B f₁ f₂) ∧
    ∀ (g₁ g₂ : GA D A) (h : GA D B),
      omh (io A (g₁, g₂), h) (delta A B f₁ f₂) =
        (((χB (detA A g₂))⁻¹ : Circle) : ℂ) • delta A B (om (g₁, h) f₁) (om (g₂, h) f₂) ∧
      thetaKO omh (io A (g₁, g₂)) h (delta A B f₁ f₂) =
        thetaKO om g₁ h f₁ * conj (thetaKO om g₂ h f₂) * (((χB (detA A g₂))⁻¹ : Circle) : ℂ)

variable (ν : Measure (WO A B)) (𝓕 : Set (WO A B))

def SectionClause : Prop :=
  ∀ φ, IsThetaFunO ψ (dblSp A) B φ →
    IntegrableOn (fun w => φ (lagr A B w)) 𝓕 ν ∧
    (∀ h : GA D B, evZero A B ν 𝓕 (omh (1, h) φ) = evZero A B ν 𝓕 φ) ∧
    (∀ (p : siegel A) (g : GA D (dblSp A)), swSec A B omh ν 𝓕 φ (p * g) =
      (χB⁻¹ (aP A p) : Circle) * npow (absA D (aP A p)) (sZero A B + (A.rank : ℂ) / 2) * swSec A B omh ν 𝓕 φ g) ∧
    IsSmoothOn (dblSp A) (swSec A B omh ν 𝓕 φ) ∧
    ∀ a : GL (Fin A.rank) (AE D), IsMaj A a → IsKFinVec omh (Khat A a) φ →
      swSec A B omh ν 𝓕 φ ∈ degPS A a χB⁻¹ (sZero A B)

def CoefClause : Prop :=
  ∀ f₁ f₂, IsThetaFunO ψ A B f₁ → IsThetaFunO ψ A B f₂ →
    evZero A B ν 𝓕 (delta A B f₁ f₂) = ip A B ν 𝓕 f₁ f₂ ∧
    ∀ g : GA D A, swSec A B omh ν 𝓕 (delta A B f₁ f₂) (io A (g, 1)) = ip A B ν 𝓕 (om (g, 1) f₁) f₂

end Clauses

def DoublingIso (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle)
    (om : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)), IsWeilDatumO ψ A B χA χB om →
    ∃ omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ),
      IsWeilDatumO ψ (dblSp A) B 1 χB omh ∧ ThetaClause ψ A B χB om omh ∧
      AllSome (fun m : Measure (WO A B) × Set (WO A B) => IsCovolOne (ratL B A) m.1 m.2) fun m =>
        SectionClause ψ A B χB omh m.1 m.2 ∧ CoefClause ψ A B om omh m.1 m.2

section Basic₂

variable (A B : HSp D)

@[simp] theorem resL_lagr (w : WO A B) : resL A B (lagr A B w) = w := by
  ext i j; simp [resL, lagr]

@[simp] theorem resR_lagr (w : WO A B) : resR A B (lagr A B w) = -w := by
  ext i j; simp only [resR, lagr, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inr, Matrix.neg_apply]

theorem delta_lagr (f₁ f₂ : WO A B → ℂ) (w : WO A B) : delta A B f₁ f₂ (lagr A B w) = f₁ w * conj (f₂ w) := by
  simp [delta]

theorem evZero_delta (ν : Measure (WO A B)) (𝓕 : Set (WO A B)) (f₁ f₂ : WO A B → ℂ) :
    evZero A B ν 𝓕 (delta A B f₁ f₂) = ip A B ν 𝓕 f₁ f₂ := by
  simp only [evZero, ip, delta_lagr]

example : sZero A B + (A.rank : ℂ) / 2 = (B.rank : ℂ) / 2 := by rw [sZero]; ring

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero

end
