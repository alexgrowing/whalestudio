import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.C

def abelian₂ {G : Type} [Add G] [MeasurableSpace G] (μ : Measure G) (γ φ : G → ℂ) : ℂ := ∫ y, ∫ x, φ x * γ (x + y) ∂μ ∂μ

def lamR (β : ℝ) : ℂ := (1 - Complex.I * ((SignType.sign β : SignType) : ℂ)) / ((2 * √|β| : ℝ) : ℂ)

variable {F : Type} [Field F] [NumberField F]

def Pc (δ : F) (b : A F) (φ : V4 F → ℂ) (y : V4 F) : ℂ := ∫ x, φ x * ψ (b * q4 δ (x + y)) ∂(adeleMeasurePi F)

def Lam4 (δ : F) (b : A F) (φ : V4 F → ℂ) : ℂ := abelian₂ (adeleMeasurePi F) (fun v => ψ (b * q4 δ v)) φ

def Lam1 (b : A F) (φ : A F → ℂ) : ℂ := abelian₂ (adeleMeasure F) (fun x => ψ (b * x ^ 2)) φ

def IsIdx (δ : F) (b : A F) (c : ℂ) : Prop := ∀ φ : S4 F, Lam4 δ b φ.1 = c * ∫ v, φ.1 v ∂(adeleMeasurePi F)

def four (φ : A F → ℂ) (v : V4 F) : ℂ :=
  φ (rt (2⁻¹ : F) * (v 1 - v 0)) * φ (rt (2⁻¹ : F) * (v 1 + v 0)) * φ (v 2) * φ (v 3)

structure Ops (δ : F) (η : (A F)ˣ →* ℂˣ) where
  N : A F → Module.End ℂ (S4 F)
  M : (A F)ˣ → Module.End ℂ (S4 F)
  W : Module.End ℂ (S4 F)
  N_apply : ∀ b φ v, (N b φ).1 v = ψ (b * q4 δ v) * φ.1 v
  M_apply : ∀ (a : (A F)ˣ) φ v, (M a φ).1 v = ((η a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ) * φ.1 fun i => (a : A F) * v i
  W_apply : ∀ φ v, (W φ).1 v = ft4 δ φ.1 v

structure Rel {H : Type} [Monoid H] (N : A F → H) (M : (A F)ˣ → H) (W : H) : Prop where
  N_zero : N 0 = 1
  N_add : ∀ b c, N (b + c) = N b * N c
  M_one : M 1 = 1
  M_mul : ∀ a a', M (a * a') = M a * M a'
  MN : ∀ (a : (A F)ˣ) b, M a * N b = N ((a : A F) ^ 2 * b) * M a
  WM : ∀ a, W * M a = M a⁻¹ * W
  W_unit : IsUnit W

def Gauss {H : Type} [Monoid H] (N : A F → H) (M : (A F)ˣ → H) (W : H) : Prop :=
  ∀ t : (A F)ˣ, W * N t * W = N (-((t⁻¹ : (A F)ˣ) : A F)) * M (-t⁻¹) * W * N (-((t⁻¹ : (A F)ˣ) : A F))

structure IsOm (δ : F) (η : (A F)ˣ →* ℂˣ) (Om : G1 F →* Module.End ℂ (S4 F)) : Prop where
  n : ∀ b φ v, (Om (nU b) φ).1 v = ψ (b * q4 δ v) * φ.1 v
  m : ∀ (a : (A F)ˣ) φ v, (Om (mD a) φ).1 v = ((η a : ℂˣ) : ℂ) * ((ab a ^ 2 : ℝ) : ℂ) * φ.1 fun i => (a : A F) * v i
  w : ∀ φ v, (Om (wW F) φ).1 v = ft4 δ φ.1 v

variable [IsTotallyReal F]

def g1 (g : FiniteAdeleRing (𝓞 F) F → ℂ) (x : A F) : ℂ :=
  (∏ w, Complex.exp (-(Real.pi : ℂ) * ((TR.pInf F x w : ℝ) : ℂ) ^ 2)) * g x.2

def IsSgn (a : (A F)ˣ) : Prop :=
  (a : A F).2 = 1 ∧ ∃ w₀, ∀ w, TR.pInf F (a : A F) w = if w = w₀ then -1 else 1

end UpperTheory.ConvolutionTheory.R2.C

end
