import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothReal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReframeVStdOfPosDef

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.AdSpan

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

def RealScal (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (B : C.Bas) (a : GA D T) (z : ℂ) : Prop :=
  ∀ φ : TF S.rank C.g, SW.IsSB φ → om (1, a) (C.Th (C.xB B) φ) = z • C.Th (C.xB (C.mvB a B)) φ

def HolUpTo (C : Ctx S T) (B : C.Bas) (la : Wt C.X.Ψ T.rank) (z φ : GA D T → ℂ) : Prop :=
  ∀ g : GA D T, ∃ Q : Frame C.X.Ψ T.rank → ℂ, DifferentiableOn ℂ Q C.X.dom ∧
    (∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank, Q (rmul x b) = bchar la b * Q x) ∧
    ∀ a ∈ GinfC T, φ (g * a) = z a * Q (C.xB (C.mvB a B))

def detPow (θ : InfFam D) (V : HSp D) (m : D.what₂.Tau → ℤ) (a : GA D V) : ℂ :=
  ∏ ρ, (compAt θ ρ (Formalism.L2.Theta.mt V a)).det ^ m ρ

def torAt (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (ρ : D.what₂.Tau)
    (t : Fin V.rank → ℝ) : GA D V :=
  atTau θ V ρ (B ρ * diagonal (fun a => cexp ((t a : ℂ) * I)) * (B ρ)⁻¹)

def LowKilled (θ : InfFam D) (V : HSp D) (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) : Prop :=
  HolRead.SmoothReal θ V φ ∧ ∀ ρ (c d : Fin V.rank), d < c → RderC θ V ρ (B ρ * Matrix.single c d 1 * (B ρ)⁻¹) φ = 0

def revPos {n : ℕ} (p : ℕ) (a : Fin n) : Fin n :=
  if h : (a : ℕ) < p ∧ p ≤ n then ⟨p - 1 - a, by omega⟩ else a

theorem revPos_revPos {n : ℕ} (p : ℕ) (a : Fin n) : revPos p (revPos p a) = a := by
  by_cases h : (a : ℕ) < p ∧ p ≤ n
  · have h' : p - 1 - (a : ℕ) < p ∧ p ≤ n := ⟨by omega, h.2⟩
    ext
    simp only [revPos, dif_pos h, Fin.val_mk, dif_pos h']
    omega
  · simp only [revPos, dif_neg h]

def revB {ι : Type} {n : ℕ} (p : ℕ) (B : ι → Matrix (Fin n) (Fin n) ℂ) : ι → Matrix (Fin n) (Fin n) ℂ :=
  fun τ => (B τ).submatrix id (revPos p)

def thetaSet (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (B : C.Bas) (u : WO S T → ℂ)
    (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) : Set (GA D T → ℂ) :=
  {φ | ∃ (h : GA D S) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ), C.toH Q ∈ Harm.rowHighest ℂ c c' ∧
    φ = fun g => om (h, g) (C.fvec B u Q) 0}

def ContT (ψ : AddChar (AF D.host.F) ℂ) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop :=
  ∀ f, IsThetaFunO ψ S T f → ∀ w, Continuous fun g : GA D T => om (1, g) f w

abbrev reS (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : HSp D := StdFrame.reframe S b

def frP (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : Matrix (Fin S.rank) (Fin S.rank) D.host.E :=
  S.frame.toMatrix b

def frPinv (S : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : Matrix (Fin S.rank) (Fin S.rank) D.host.E :=
  b.toMatrix S.frame

def reW (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) (x : WO (reS S b) T) : WO S T :=
  HMul.hMul (α := Matrix (Fin T.rank) (Fin S.rank) (AE D)) x ((frPinv S b).map (incA D))

def reF (S T : HSp D) (b : Module.Basis (Fin S.rank) D.host.E S.V) : (WO S T → ℂ) →ₗ[ℂ] (WO (reS S b) T → ℂ) :=
  LinearMap.funLeft ℂ ℂ (reW S T b)

theorem reF_apply (b : Module.Basis (Fin S.rank) D.host.E S.V) (f : WO S T → ℂ) (x : WO (reS S b) T) :
    reF S T b f x = f (reW S T b x) := rfl

theorem reF_zero (b : Module.Basis (Fin S.rank) D.host.E S.V) (f : WO S T → ℂ) : reF S T b f 0 = f 0 := by
  rw [reF_apply]
  congr 1
  exact Matrix.zero_mul _

end GlobalTheory.AdSpan

end
