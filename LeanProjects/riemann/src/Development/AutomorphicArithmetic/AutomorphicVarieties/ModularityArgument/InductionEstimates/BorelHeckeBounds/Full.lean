import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt

noncomputable section

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

variable {K : Type} [Field K] [NumberField K]

def Sg {n : ℕ} (ω : Set (AdelicGLn.AdelicGL K n)) (ρ : Fin n → ℝ) (z : G1 K n) : Prop :=
  ∃ (hρ : ∀ i, 0 < ρ i), ∃ b ∈ ω, ∃ k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)),
    (z : AdelicGLn.AdelicGL K n) = b * diagUnits n (fun i => posIdele (K := K) (ρ i) (hρ i)) * k

def Bor {n : ℕ} (ω : Set (AdelicGLn.AdelicGL K n)) : Prop :=
  IsCompact ω ∧ ω ⊆ ((adelicBorel : Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n))

def Full {n : ℕ} (t : ℝ) (ρ : Fin n → ℝ) : Prop := ∀ i j : Fin n, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i

def Rel (t : ℝ) (ρ : Fin (2 + 2) → ℝ) : Prop := t * ρ 1 ≤ ρ 0 ∧ t * ρ 3 ≤ ρ 2

def Rat {n : ℕ} (R : ℝ) (ρ : Fin n → ℝ) : Prop := ∀ i j : Fin n, i < j → ρ i / ρ j ≤ R

def inR (ρ : Fin (2 + 2) → ℝ) : ℝ := ρ 0 / ρ 1 * (ρ 2 / ρ 3)

structure Red (ω : Set (AdelicGLn.AdelicGL K (2 + 2))) (t : ℝ) : Prop where
  bor : Bor ω
  pos : 0 < t
  full : ∀ x : G1 K (2 + 2), ∃ γ ∈ Gam K (2 + 2), ∃ ρ, Sg ω ρ (γ * x) ∧ Full t ρ
  rel : ∀ z : G1 K (2 + 2), ∃ δ ∈ PK K, ∃ ρ, Sg ω ρ (δ * z) ∧ Rel t ρ

def Far (ω : Set (AdelicGLn.AdelicGL K (2 + 2))) (t ε : ℝ) (z : G1 K (2 + 2)) : Prop :=
  ∃ δ ∈ PK K, ∃ ρ, Sg ω ρ (δ * z) ∧ Rel t ρ ∧ qht z ^ ε ≤ inR ρ

abbrev qx (q : Cos K) (x : G1 K (2 + 2)) : G1 K (2 + 2) := (q.out : G1 K (2 + 2)) * x

def Om (T : ℝ) (x : G1 K (2 + 2)) : Prop := ∀ q : Cos K, HH (qx q x) ≤ T

def ct {n : ℕ} (r : ℕ) (ψ : G1 K n → ℂ) (z : G1 K n) : ℂ :=
  ∫ X in unipFundamentalDomain K n r, ψ (unipOne K n r X * z) ∂unipMeasure K n r

def hi (T : ℝ) (F : G1 K (2 + 2) → ℂ) : G1 K (2 + 2) → ℂ := {z | T < HH z}.indicator F

def lam (T : ℝ) (ψ : G1 K (2 + 2) → ℂ) (x : G1 K (2 + 2)) : ℂ := ψ x - th (hi T (ct 2 ψ)) x

def secF {d : ℕ} (sec : Eu d →ₗ[ℂ] (G1 K (2 + 2) → ℂ)) (U : ℝ → Eu d) (z : G1 K (2 + 2)) : ℂ :=
  Complex.exp (2 * (HH z : ℂ)) * sec (U (HH z)) z

abbrev rc {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (a : CC K n) (φ : L2 μ) : G1 K n → ℂ := rconv (Gam K n) μ a φ

abbrev Jd {μ : Measure (G1 K (2 + 2))} {d : ℕ} (J : L (Eu d) →ₗᵢ[ℂ] L2 μ) : L2 μ →L[ℂ] L (Eu d) :=
  ContinuousLinearMap.adjoint J.toContinuousLinearMap

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
