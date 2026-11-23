import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.WordDerivatives

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies (LieAt LieInf atPlace IsExpFam IsSmoothInf wordDer)
open scoped TensorProduct DirectSum Classical

namespace GlobalTheory.AutFinLit

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Compact

variable {K : Type} [Group K] [TopologicalSpace K]

def IsIrrMat {d : ℕ} (σ : K →* Matrix (Fin d) (Fin d) ℂ) : Prop :=
  0 < d ∧ Continuous σ ∧ ∀ S : Submodule ℂ (Fin d → ℂ), (∀ k, ∀ v ∈ S, (σ k).mulVec v ∈ S) → S = ⊥ ∨ S = ⊤

def EquivMat {d d' : ℕ} (σ : K →* Matrix (Fin d) (Fin d) ℂ) (σ' : K →* Matrix (Fin d') (Fin d') ℂ) : Prop :=
  ∃ e : (Fin d → ℂ) ≃ₗ[ℂ] (Fin d' → ℂ), ∀ k v, e ((σ k).mulVec v) = (σ' k).mulVec (e v)

def IsElemIdem (ξ : K → ℂ) : Prop :=
  ∃ (r : ℕ) (d : Fin r → ℕ) (σ : ∀ i, K →* Matrix (Fin (d i)) (Fin (d i)) ℂ),
    (∀ i, IsIrrMat (σ i)) ∧ (∀ i j, EquivMat (σ i) (σ j) → i = j) ∧ ξ = fun k => ∑ i, (d i : ℂ) * (σ i k⁻¹).trace

end Compact

variable {D : D7}

def IsMaxCompactInf (V : HSp D) (K : Subgroup (GA D V)) : Prop :=
  (∀ k ∈ K, k ∈ GinfC V) ∧ IsCompact (K : Set (GA D V)) ∧
    ∀ K' : Subgroup (GA D V), (∀ k ∈ K', k ∈ GinfC V) → IsCompact (K' : Set (GA D V)) → K ≤ K' → K' = K

def IsCompactOpenFin (V : HSp D) (L : Subgroup (GA D V)) : Prop :=
  IsCompact (L : Set (GA D V)) ∧ ∃ O : Set (GA D V), IsOpen O ∧ ∀ g, g ∈ L ↔ g ∈ O ∧ g ∈ GfC V

abbrev LieC (V : HSp D) : Type := ⨁ τ : D.what₂.Tau, ℂ ⊗[ℝ] LieAt V τ

abbrev Env (V : HSp D) : Type := UniversalEnvelopingAlgebra ℂ (LieC V)

abbrev Zg (V : HSp D) : Type := Subalgebra.center ℂ (Env V)

def envOf (V : HSp D) (w : List (Σ τ, LieAt V τ) →₀ ℂ) : Env V :=
  w.sum fun l c => c • (l.map fun p => UniversalEnvelopingAlgebra.ι ℂ
    (DirectSum.of (fun τ : D.what₂.Tau => ℂ ⊗[ℝ] LieAt V τ) p.1 ((1 : ℂ) ⊗ₜ[ℝ] p.2) : LieC V)).prod

def envDer (V : HSp D) (e : LieInf V → GA D V) (w : List (Σ τ, LieAt V τ) →₀ ℂ) (φ : GA D V → ℂ) : GA D V → ℂ :=
  w.sum fun l c => c • wordDer V e (l.map fun p => atPlace V p.1 p.2) φ

def KilledBy (V : HSp D) (e : LieInf V → GA D V) (J : Ideal (Zg V)) (φ : GA D V → ℂ) : Prop :=
  ∀ z ∈ J, ∀ w, envOf V w = z.1 → envDer V e w φ = 0

def SlowlyIncreasing (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (φ : GA D V → ℂ) : Prop :=
  ∀ x, ∃ (C : ℝ) (N : ℕ), ∀ y ∈ GinfC V, ‖φ (x * y)‖ ≤ C * normInf θ V y ^ N

def forms (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (e : LieInf V → GA D V)
    (K : Subgroup (GA D V)) [MeasurableSpace K] (μ : Measure K) (ξ : K → ℂ) (L : Subgroup (GA D V)) (J : Ideal (Zg V)) :
    Set (GA D V → ℂ) :=
  {φ | IsSmoothInf V e φ ∧ (∀ γ ∈ GQ V, ∀ g, φ (γ * g) = φ g) ∧ (∀ u ∈ L, ∀ g, φ (g * u) = φ g) ∧
    (∀ g, ∫ k : K, φ (g * (k : GA D V)⁻¹) * ξ k ∂μ = φ g) ∧ KilledBy V e J φ ∧ SlowlyIncreasing θ V φ}

end GlobalTheory.AutFinLit

namespace GlobalTheory.Published

open GlobalTheory.AutFinLit

def AutomorphicFormsFiniteIdeal : Prop :=
  ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
  ∀ (V : HSp D) (e : LieInf V → GA D V), IsExpFam θ V e →
  ∀ K : Subgroup (GA D V), IsMaxCompactInf V K →
  ∀ [MeasurableSpace K] [BorelSpace K] (μ : Measure K), μ.IsHaarMeasure → IsProbabilityMeasure μ →
  ∀ ξ : K → ℂ, IsElemIdem ξ →
  ∀ L : Subgroup (GA D V), IsCompactOpenFin V L →
  ∀ J : Ideal (Zg V), FiniteDimensional ℂ (Zg V ⧸ J) →
    FiniteDimensional ℂ (Submodule.span ℂ (forms θ V e K μ ξ L J))

end GlobalTheory.Published

end
