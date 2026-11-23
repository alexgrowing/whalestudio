import Mathlib
import GroundTheory.AutomorphicForms.Reduction
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsSiegel

noncomputable section

open NumberField MeasureTheory Filter Topology Polynomial
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace PositivityTheory.Rg.Rs.An

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def tor (K : Type) [Field K] [NumberField K] {n : ℕ} (x : Fin n → ℝ) : AdelicGLn.AdelicGL K n :=
  diagUnits n fun i => posIdele (K := K) (Real.exp (x i)) (Real.exp_pos _)

def aR (K : Type) [Field K] [NumberField K] (n r : ℕ) (t : ℝ) : AdelicGLn.AdelicGL K n :=
  tor K fun i : Fin n => if (i : ℕ) < r then t else 0

def sr (x : Fin n → ℝ) (r : ℕ) : ℝ :=
  if h : 0 < r ∧ r < n then x ⟨r - 1, by omega⟩ - x ⟨r, h.2⟩ else 0

def rho (K : Type) [Field K] [NumberField K] (n r : ℕ) : ℝ := (Module.finrank ℚ K : ℝ) * ((r : ℝ) * ((n : ℝ) - r) / 2)

def ctn (r : ℕ) (φ : AdelicGLn.AdelicGL K n → ℂ) (g : AdelicGLn.AdelicGL K n) : ℂ :=
  (((unipMeasure K n r).real (unipFundamentalDomain K n r) : ℝ) : ℂ)⁻¹ * constantTerm r φ g

def Bnd (φ : AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ) : Prop :=
  ∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set _) → ∀ t₀ : ℝ,
    ∀ Q : Set (AdelicGLn.AdelicGL K n), IsCompact Q → ∃ C : ℝ, ∀ b ∈ ω, ∀ x : Fin n → ℝ, (∀ r, -t₀ ≤ sr x r) →
      ∀ q ∈ Q, ‖φ (b * tor K x * q)‖ ≤ C * Real.exp (∑ r ∈ Finset.range n, m r * sr x r)

def Kill (r : ℕ) (φ : AdelicGLn.AdelicGL K n → ℂ) (p : ℂ[X]) : Prop :=
  ∀ g, ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * ctn r φ (aR K n r j * g) = 0

structure Nice (φ : AdelicGLn.AdelicGL K n → ℂ) : Prop where
  cont : Continuous φ
  left : IsLeftInvariant φ
  centre : ∀ (t : ℝ) g, φ (tor K (fun _ => t) * g) = φ g
  level : ∃ U : Subgroup (AdelicGLn.integralFiniteGL K n), IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) ∧
    ∀ (g : AdelicGLn.AdelicGL K n) (u : U),
      φ (g * finEmb K n ((u : AdelicGLn.integralFiniteGL K n) : AdelicGLn.FiniteAdelicGL K n)) = φ g
  lip : ∀ R : ℝ, ∃ (Q₀ : Set (AdelicGLn.AdelicGL K n)) (C : ℝ), IsCompact Q₀ ∧ 0 ≤ C ∧ ∀ g (Y : ArchMatrix K n) (M : ℝ),
    Y * Y = 0 → ‖Y‖ ≤ R → (∀ q ∈ Q₀, ‖φ (g * q)‖ ≤ M) → ‖φ (g * CuspidalSpectrum.archExp Y) - φ g‖ ≤ C * ‖Y‖ * M

def DiffStep : Prop := ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (φ : AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ) (r : ℕ),
  0 < r → r < n → Nice φ → Bnd φ m → Bnd (fun g => φ g - ctn r φ g) (Function.update m r (m r - 1))

def RecBound : Prop := ∀ (p : ℂ[X]) (κ : ℝ), p.Monic → (∀ z, p.IsRoot z → ‖z‖ < Real.exp κ) →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : ℕ → ℂ) (M : ℝ), (∀ i, ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * u (i + j) = 0) →
    (∀ j < p.natDegree, ‖u j‖ ≤ M) → 0 ≤ M → ∀ i, ‖u i‖ ≤ C * Real.exp (κ * i) * M

def CtStep : Prop := ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (φ : AdelicGLn.AdelicGL K n → ℂ) (m : ℕ → ℝ) (r : ℕ)
  (p : ℂ[X]) (κ : ℝ), 0 < r → r < n → Nice φ → Bnd φ m → p.Monic → Kill r φ p → (∀ z, p.IsRoot z → ‖z‖ < Real.exp κ) →
  Bnd (ctn r φ) (Function.update m r κ)

def Boot : Prop := ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (φ : AdelicGLn.AdelicGL K n → ℂ) (M : ℝ) (κ : ℕ → ℝ),
  Nice φ → Bnd φ (fun _ => M) →
  (∀ r, 0 < r → r < n → ∃ p : ℂ[X], p.Monic ∧ Kill r φ p ∧ ∀ z, p.IsRoot z → ‖z‖ < Real.exp (κ r)) → Bnd φ κ

def BoxVol : Prop := ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (AdelicGLn.AdelicGL K n)) [μ.IsHaarMeasure]
  (ω : Set (AdelicGLn.AdelicGL K n)), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set _) →
  ∃ C : ℝ, ∀ x : Fin n → ℝ,
    μ {g | ∃ b ∈ ω, ∃ y : Fin n → ℝ, (∀ i, |y i| ≤ n) ∧ ∃ k ∈ maxCompact (K := K) (n := n), g = b * tor K (x + y) * k} ≤
      ENNReal.ofReal (C * Real.exp (-∑ r ∈ Finset.range n, 2 * rho K n r * sr x r))

def slab (ω : Set (AdelicGLn.AdelicGL K n)) (t₀ : ℝ) : Set (AdelicGLn.AdelicGL K n) :=
  {g | ∃ b ∈ ω, ∃ x : Fin n → ℝ, (∀ r, -t₀ ≤ sr x r) ∧ (∀ i : Fin n, (i : ℕ) + 1 = n → 0 ≤ x i ∧ x i ≤ 1) ∧
    ∃ k ∈ maxCompact (K := K) (n := n), g = b * tor K x * k}

def SlabInt : Prop := ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (AdelicGLn.AdelicGL K n)) [μ.IsHaarMeasure]
  (φ : AdelicGLn.AdelicGL K n → ℂ) (κ : ℕ → ℝ), Continuous φ → Bnd φ κ → (∀ r, 0 < r → r < n → κ r < rho K n r) →
  ∀ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω → ω ⊆ (adelicBorel (K := K) (n := n) : Set _) → ∀ t₀ : ℝ,
    ∫⁻ g in slab ω t₀, ‖φ g‖ₑ ^ 2 ∂μ < ⊤

def lat (K : Type) [Field K] [NumberField K] (n : ℕ) : Subgroup (AdelicGLn.AdelicGL K n) :=
  (AdelicGLn.diagonal K n).range ⊔ Subgroup.zpowers (tor K fun _ => 1)

def Count : Prop := ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ), 0 < r → r < n →
  ∀ (D : Set (UPos n r → AdeleRing (𝓞 K) K)) (Q : Set (AdelicGLn.AdelicGL K n)), IsCompact D → IsCompact Q →
  ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t →
    {γ : lat K n | ∃ X ∈ D, ∃ Y ∈ D, ∃ q ∈ Q,
      (γ : AdelicGLn.AdelicGL K n) = unipGL X * aR K n r t * q * (aR K n r t)⁻¹ * (unipGL Y)⁻¹}.encard ≤
      (⌈C * Real.exp (2 * rho K n r * t)⌉₊ : ℕ)

def Escape : Prop := ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ), 0 < r → r < n →
  ∀ (D : Set (UPos n r → AdeleRing (𝓞 K) K)) (Q T : Set (AdelicGLn.AdelicGL K n)), IsCompact D → IsCompact Q → IsCompact T →
  ∀ᶠ t : ℝ in atTop, ∀ γ ∈ lat K n, ∀ X ∈ D, ∀ q ∈ Q, γ * (unipGL X * aR K n r t * q) ∉ T

def L2ConstantTermDecay : Prop := ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ), 0 < r → r < n →
  ∀ (μ : Measure (AdelicGLn.AdelicGL K n)) [μ.IsHaarMeasure] (φ : AdelicGLn.AdelicGL K n → ℂ)
    (F : Set (AdelicGLn.AdelicGL K n)), Continuous φ → (∀ γ ∈ lat K n, ∀ g, φ (γ * g) = φ g) →
    IsFundamentalDomain (lat K n) F μ → ∫⁻ g in F, ‖φ g‖ₑ ^ 2 ∂μ < ⊤ →
    ∀ Q : Set (AdelicGLn.AdelicGL K n), IsCompact Q →
      Tendsto (fun t : ℝ => Real.exp (-(2 * rho K n r * t)) * ∫ g in Q, ‖ctn r φ (aR K n r t * g)‖ ^ 2 ∂μ) atTop (𝓝 0)

def CtStepGlue : Prop := RecBound → CtStep
def BootGlue : Prop := DiffStep → CtStep → Boot
def SlabGlue : Prop := BoxVol → SlabInt
def L2DecayOfCountEscape : Prop := Count → Escape → L2ConstantTermDecay

end PositivityTheory.Rg.Rs.An

end
