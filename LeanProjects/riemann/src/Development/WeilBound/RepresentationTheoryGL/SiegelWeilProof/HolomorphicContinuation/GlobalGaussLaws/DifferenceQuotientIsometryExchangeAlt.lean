import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocalL2IsometryAlt

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def aC (X : Fin n → ℝ) (z : ℂ) : M2 n :=
  Matrix.fromBlocks (Matrix.diagonal fun j => Complex.exp (z * X j)) 0 0 (Matrix.diagonal fun j => Complex.exp (-(z * X j)))

def stripS (X : Fin n → ℝ) : Set ℂ := {z | ∀ j, |z.im * X j| < Real.pi / 4}

def ptZ (y : GR n) (X : Fin n → ℝ) (z : ℂ) (sgnI : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  let M := mR y * aC X z
  (M.toBlocks₁₁ * (sgnI • 1) + M.toBlocks₁₂) * (M.toBlocks₂₁ * (sgnI • 1) + M.toBlocks₂₂)⁻¹

def jC (e : ℤ) (p q : ℕ) (y : GR n) (X : Fin n → ℝ) (z : ℂ) : ℂ :=
  let M := mR y * aC X z
  M.det ^ e * (M.toBlocks₂₁ * (Complex.I • 1) + M.toBlocks₂₂).det ^ (-(p : ℤ)) *
    (M.toBlocks₂₁ * ((-Complex.I) • 1) + M.toBlocks₂₂).det ^ (-(q : ℤ))

def gC {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (Z Z' : Matrix (Fin n) (Fin n) ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  Complex.exp (Complex.I * c * (Z * gramB (epsT t ε) true u).trace - Complex.I * c * (Z' * gramB (epsT t ε) false u).trace)

def famC {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (y : GR n) (X : Fin n → ℝ) (z : ℂ) (u : Fin m → Fin n → ℂ) : ℂ :=
  jC e (cnt (epsT t ε) true) (cnt (epsT t ε) false) y X z * gC ε t c (ptZ y X z Complex.I) (ptZ y X z (-Complex.I)) u

def DReal : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (y : GR n) (X : Fin n → ℝ) (a : ℝ → GR n), (∀ s, IsDil X s (a s)) →
    ∀ s : ℝ, famC ε t c e y X s = fun u => jF e (cnt (epsT t ε) true) (cnt (epsT t ε) false) (y * a s) (Complex.I • 1) *
      gZf ε t c (actZ (y * a s) (Complex.I • 1)) u

def DBound : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (X : Fin n → ℝ), 0 < c → |t| = c →
    (∀ y u, DifferentiableOn ℂ (fun z => famC ε t c e y X z u) (stripS X)) ∧
    ContinuousOn (fun p : GR n × ℂ × (Fin m → Fin n → ℂ) => famC ε t c e p.1 X p.2.1 p.2.2) (Set.univ ×ˢ (stripS X ×ˢ Set.univ)) ∧
    ∀ (y₀ : GR n) (z₀ : ℂ), z₀ ∈ stripS X → ∃ (N : Set (GR n × ℂ)) (δ C : ℝ), N ∈ 𝓝 (y₀, z₀) ∧ 0 < δ ∧
      ∀ p ∈ N, p.2 ∈ stripS X → ∀ u, ‖famC ε t c e p.1 X p.2 u‖ ≤ C * Real.exp (-(δ * ∑ a, ∑ j, ‖u a j‖ ^ 2))

def DCalc : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ) (e : ℤ) (X : Fin n → ℝ), 0 < c → |t| = c →
    (∀ (s : ℝ) (r : ℕ) (u : Fin m → Fin n → ℂ),
      iteratedDeriv r (fun s' : ℝ => famC ε t c e 1 X s' u) s = (Real.exp (s * (m : ℝ) * ∑ j, X j) : ℂ) *
        fP c ((dil c X ^ r) 1) (fun a j => u a j * Real.exp (s * X j))) ∧
    ∀ (r : ℕ) (s : ℝ), Filter.Tendsto (fun h : ℝ => ∫ u : Fin m → Fin n → ℂ,
        ‖(iteratedDeriv r (fun s' : ℝ => famC ε t c e 1 X s' u) (s + h) - iteratedDeriv r (fun s' : ℝ => famC ε t c e 1 X s' u) s) / h -
          iteratedDeriv (r + 1) (fun s' : ℝ => famC ε t c e 1 X s' u) s‖ ^ 2) (𝓝[≠] 0) (𝓝 0)

def DifferenceQuotientIsometryExchange : Prop :=
  ∀ (m n : ℕ) (T : ((Fin m → Fin n → ℂ) → ℂ) → ((Fin m → Fin n → ℂ) → ℂ)) (κ : ℝ), 0 < κ →
    (∀ f, IsSch f → IsSch (T f)) → (∀ f g, IsSch f → IsSch g → T (f - g) = T f - T g) →
    (∀ a f, IsSch f → T (fun u => a * f u) = fun u => a * T f u) →
    (∀ f, IsSch f → ∫ u, ‖T f u‖ ^ 2 = κ * ∫ u, ‖f u‖ ^ 2) →
    ∀ (G : ℝ → (Fin m → Fin n → ℂ) → ℂ) (G' E' : (Fin m → Fin n → ℂ) → ℂ) (s : ℝ), (∀ s', IsSch (G s')) → IsSch G' →
      Continuous E' → Filter.Tendsto (fun h : ℝ => ∫ u, ‖(G (s + h) u - G s u) / h - G' u‖ ^ 2) (𝓝[≠] 0) (𝓝 0) →
      (∀ u, Filter.Tendsto (fun h : ℝ => (T (G (s + h)) u - T (G s) u) / h) (𝓝[≠] 0) (𝓝 (E' u))) → T G' = E'

def DHol : Prop :=
  GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (n : ℕ) (V : HSp D), 1 ≤ n → n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank →
  ∀ θ : InfFam D, IsInfFam θ → ∀ (ν : Measure (GA D V)), ν.IsHaarMeasure →
  ∀ (P : Type) [TopologicalSpace P] [FirstCountableTopology P] (U : Set ℂ), IsOpen U → ∀ φ : P → ℂ → Mx D V.rank n → ℂ,
    (∀ p z, z ∈ U → φ p z ∈ schwartzA θ V.rank n) → (∀ p x, DifferentiableOn ℂ (fun z => φ p z x) U) →
    (∀ x, ContinuousOn (fun pz : P × ℂ => φ pz.1 pz.2 x) (Set.univ ×ˢ U)) →
    (∀ p, ContinuousOn (fun zx : ℂ × Mx D V.rank n => φ p zx.1 zx.2) (U ×ˢ Set.univ)) →
    (∀ (p₀ : P) (z₀ : ℂ), z₀ ∈ U → ∃ (N : Set (P × ℂ)) (M : Mx D V.rank n → ℂ), N ∈ 𝓝 (p₀, z₀) ∧ M ∈ schwartzA θ V.rank n ∧
      ∀ pz ∈ N, pz.2 ∈ U → ∀ x, ‖φ pz.1 pz.2 x‖ ≤ ‖M x‖) →
    let F : P → ℂ → ℂ := fun p z =>
      ⨍ q, descend (GQ V) (fun h => ∑' ξ, φ p z (GlobalTheory.SiegelFormula.invPt V h ξ)) q ∂autMeasure V ν
    ContinuousOn (fun pz : P × ℂ => F pz.1 pz.2) (Set.univ ×ˢ U) ∧ (∀ p, DifferentiableOn ℂ (F p) U) ∧
      ∀ p (r : ℕ) z, z ∈ U → iteratedDeriv r (F p) z =
        ⨍ q, descend (GQ V) (fun h => ∑' ξ, iteratedDeriv r (fun w => φ p w (GlobalTheory.SiegelFormula.invPt V h ξ)) z) q ∂autMeasure V ν

def DSieg : Prop :=
  ∀ (n : ℕ) (y : GR n) (X : Fin n → ℝ) (z : ℂ), z ∈ stripS X →
    IsSiegel (ptZ y X z Complex.I) ∧ IsSiegel (ptZ y X z (-Complex.I))ᴴ ∧
    ((mR y * aC X z).toBlocks₂₁ * (Complex.I • 1) + (mR y * aC X z).toBlocks₂₂).det ≠ 0 ∧
    ((mR y * aC X z).toBlocks₂₁ * ((-Complex.I) • 1) + (mR y * aC X z).toBlocks₂₂).det ≠ 0

def GCSch : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ), 0 < c → |t| = c → ∀ Z Z' : Matrix (Fin n) (Fin n) ℂ, IsSiegel Z → IsSiegel Z'ᴴ →
    IsSch (gC ε t c Z Z')

end PositivityTheory.Rg.Sw.Glob
