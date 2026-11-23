import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.MultOneC
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.KTypeExist
import GroundTheory.AutomorphicForms.TensorProductTheorem.NonemptyAdelicDecomposition

noncomputable section

open MeasureTheory NumberField Filter Topology Matrix
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.ArchWhittakerC UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 PositivityTheory.Rg.Tf.Core
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E
open scoped ComplexConjugate Classical

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA

abbrev U4 : Type := unitaryGroup (Fin (2 + 2)) ℂ

instance : MeasurableSpace U4 := borel _
instance : BorelSpace U4 := ⟨rfl⟩

def bd (a b : U2) : U4 :=
  Classical.epsilon fun k : U4 => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ) =
    reindex finSumFinEquiv finSumFinEquiv (fromBlocks (a : Matrix (Fin 2) (Fin 2) ℂ) 0 0 (b : Matrix (Fin 2) (Fin 2) ℂ))

def w4 : U4 :=
  Classical.epsilon fun k : U4 => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ) =
    reindex finSumFinEquiv finSumFinEquiv (fromBlocks 0 (1 : Matrix (Fin 2) (Fin 2) ℂ) 1 0)

def dg (θ : Fin (2 + 2) → ℝ) : U4 :=
  Classical.epsilon fun k : U4 => (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ) = diagonal fun i => Complex.exp (Complex.I * θ i)

def chi (ν : Fin (2 + 2) → ℤ) (θ : Fin (2 + 2) → ℝ) : ℂ := Complex.exp (Complex.I * ∑ i, (ν i : ℂ) * θ i)

structure Haar4 (μ : Measure U4) : Prop where
  prob : IsProbabilityMeasure μ
  left : ∀ k, MeasurePreserving (k * ·) μ μ
  right : ∀ k, MeasurePreserving (· * k) μ μ
  inv : MeasurePreserving (·⁻¹) μ μ

def Exp (ψ : U4 → ℂ) (μ : Fin (2 + 2) → ℤ) (good good' : (Fin (2 + 2) → ℤ) → Prop) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (j₀ : J) (a b : J → U4 → ℂ) (ν : J → Fin (2 + 2) → ℤ),
    (∀ j, Continuous (a j) ∧ Continuous (b j)) ∧ (∀ h k, ψ (h * k) = ∑ j, a j h * b j k) ∧ a j₀ = ψ ∧ b j₀ = ψ ∧ ν j₀ = μ ∧
    (∀ j θ h, a j (h * dg θ) = chi (ν j) θ * a j h ∧ a j (dg θ * h) = chi μ θ * a j h ∧ b j (dg θ * h) = chi (ν j) θ * b j h) ∧
    (∀ j, good (ν j)) ∧ ∀ j, j ≠ j₀ → good' (ν j)

def WExp (ψ : U4 → ℂ) (μ : Fin (2 + 2) → ℤ) : Prop := Exp ψ μ (fun ν => ∑ i, ν i ^ 2 ≤ ∑ i, μ i ^ 2) fun ν => ν ≠ μ

def OExp (π : Equiv.Perm (Fin (2 + 2))) (ψ : U4 → ℂ) (μ : Fin (2 + 2) → ℤ) : Prop :=
  Exp ψ μ (fun ν => ∀ (w : Equiv.Perm (Fin (2 + 2))) (y : Fin (2 + 2) → ℤ), Antitone (y ∘ π) → ∑ i, ν i * y (w i) ≤ ∑ i, μ i * y i)
    fun ν => ∑ i, ν (π i) * (-(i : ℤ)) < ∑ i, μ (π i) * (-(i : ℤ))

def en (i j : Fin (2 + 2)) (k : U4) : ℂ := (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) ℂ) i j

def T (n : ℕ) (q : ℤ) (k : U2) : ℂ := ((KT.normSqInt n q : ℝ) : ℂ)⁻¹ * conj (KT.psi n q n k)

def Above (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) : Prop := n ≤ n' ∧ (n' : ℤ) + 2 * q' = n + 2 * q

def wt (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) : Fin (2 + 2) → ℤ := ![n + q, q, n' + q', q']

structure Coef (ψ : U4 → ℂ) (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) : Prop where
  exp : WExp ψ (wt n q n' q')
  star : ∀ k, ψ k⁻¹ = conj (ψ k)
  res : ∀ a b, ψ (bd a b) = KT.psi n q n a * KT.psi n' q' n' b

def eOf (μ : Measure U4) (ψ : U4 → ℂ) (k : U4) : ℂ := ((∫ h, ‖ψ h‖ ^ 2 ∂μ : ℝ) : ℂ)⁻¹ * conj (ψ k)

def RFix {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) (e Φ : G → ℂ) : Prop := ∀ g, ∫ k, e k * Φ (g * k) ∂μ = Φ g

structure Idem {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G) (e : G → ℂ) : Prop where
  cont : Continuous e
  star : ∀ k, e k⁻¹ = conj (e k)
  idem : ∀ k, ∫ h, e h * e (h⁻¹ * k) ∂μ = e k

def LAbove {G : Type} [Group G] (j : U2 → G) (n : ℕ) (q : ℤ) (Φ : G → ℂ) : Prop :=
  ∀ n' q', ¬ Above n q n' q' → ∀ (l : U2) (k : G), ∫ m, conj (KT.psi n' q' n' m) * Φ (j (l * m) * k) ∂μK = 0

structure Ext (μ : Measure U4) (e : U4 → ℂ) (n : ℕ) (q : ℤ) (n' : ℕ) (q' : ℤ) (x : U4) : Prop where
  idem : Idem μ e
  fix : ∀ Φ : U4 → ℂ, Continuous Φ → RFix μ e Φ → ∀ g, ∫ m, T n q m * Φ (g * bd m 1 * x) ∂μK = Φ (g * x) ∧
    ∫ m, T n' q' m * Φ (g * bd 1 m * x) ∂μK = Φ (g * x)
  inj : ∀ Φ : U4 → ℂ, Continuous Φ → RFix μ e Φ → LAbove (fun m => bd m 1) n q Φ → LAbove (fun m => bd 1 m) n' q' Φ →
    (∀ a b, Φ (bd a b * x) = 0) → Φ = 0
  ex : ∃ ψ : U4 → ℂ, Continuous ψ ∧ RFix μ e ψ ∧ ∀ a b, ψ (bd a b * x) = conj (T n q a) * conj (T n' q' b)

structure ExtP {ι : Type} [Fintype ι] (μ : Measure U4) (e : ι → U4 → ℂ) (n : ι → ℕ) (q : ι → ℤ) (n' : ι → ℕ) (q' : ι → ℤ)
    (x : ι → U4) : Prop where
  idem : Idem (Measure.pi fun _ : ι => μ) fun k => ∏ i, e i (k i)
  fix : ∀ Φ : (ι → U4) → ℂ, Continuous Φ → RFix (Measure.pi fun _ => μ) (fun k => ∏ i, e i (k i)) Φ → ∀ g,
    ∫ m : ι → U2, (∏ i, T (n i) (q i) (m i)) * Φ (g * (fun i => bd (m i) 1) * x) ∂(Measure.pi fun _ => μK) = Φ (g * x) ∧
    ∫ m : ι → U2, (∏ i, T (n' i) (q' i) (m i)) * Φ (g * (fun i => bd 1 (m i)) * x) ∂(Measure.pi fun _ => μK) = Φ (g * x)
  inj : ∀ Φ : (ι → U4) → ℂ, Continuous Φ → RFix (Measure.pi fun _ => μ) (fun k => ∏ i, e i (k i)) Φ →
    (∀ i, LAbove (fun m => (Pi.mulSingle i (bd m 1) : ι → U4)) (n i) (q i) Φ) →
    (∀ i, LAbove (fun m => (Pi.mulSingle i (bd 1 m) : ι → U4)) (n' i) (q' i) Φ) →
    (∀ a b : ι → U2, Φ ((fun i => bd (a i) (b i)) * x) = 0) → Φ = 0
  ex : ∃ ψ : (ι → U4) → ℂ, Continuous ψ ∧ RFix (Measure.pi fun _ => μ) (fun k => ∏ i, e i (k i)) ψ ∧
    ∀ a b : ι → U2, ψ ((fun i => bd (a i) (b i)) * x) = conj (∏ i, T (n i) (q i) (a i)) * conj (∏ i, T (n' i) (q' i) (b i))

structure Co (K : Type) [Field K] [NumberField K] (ι : Type) where
  c : mixedEmbedding.mixedSpace K ≃+* (ι → ℂ)
  Ψ : ∀ n, archGroup K n ≃ₜ* (ι → GL (Fin n) ℂ)
  Φ : ∀ n, archCompact K n ≃ₜ* (ι → unitaryGroup (Fin n) ℂ)
  Ψ_val : ∀ n (g : archGroup K n) i a b, (Ψ n g i : Matrix (Fin n) (Fin n) ℂ) a b =
    c ((show Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K) from (g.1 : ArchMatrix K n)) a b) i
  Φ_val : ∀ n (k : archCompact K n) i, (Φ n k i : Matrix (Fin n) (Fin n) ℂ) = (Ψ n (k : archGroup K n) i : Matrix (Fin n) (Fin n) ℂ)

section

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] (C : Co K ι)

def Co.gl (i : ι) (g : GL (Fin 2) ℂ) : G1 K 2 := archP K 2 ((C.Ψ 2).symm (Pi.mulSingle i g))

def Co.un (i : ι) (m : U2) : G1 K 2 := arc1 ((C.Φ 2).symm (Pi.mulSingle i m))

def Co.κ₂ : Measure (archCompact K 2) := Measure.map (C.Φ 2).symm (Measure.pi fun _ => μK)

def Co.κ₄ (μ : Measure U4) : Measure (archCompact K (2 + 2)) := Measure.map (C.Φ (2 + 2)).symm (Measure.pi fun _ => μ)

def Co.p (n : ι → ℕ) (q : ι → ℤ) (k : archCompact K 2) : ℂ := ∏ i, T (n i) (q i) (C.Φ 2 k i)

def Co.e (e : ι → U4 → ℂ) (k : archCompact K (2 + 2)) : ℂ := ∏ i, e i (C.Φ (2 + 2) k i)

variable (μ : Measure (G1 K 2)) [μ.IsHaarMeasure]

def Co.Pi (i : ι) (n : ℕ) (q : ℤ) (v : LL μ) : LL μ := ∫ m, T n q m • rightRegularRep (Gam K 2) μ (C.un i m) v ∂μK

def Co.MinAt (τ : Submodule ℂ (LL μ)) (i : ι) (n : ℕ) (q : ℤ) : Prop :=
  (∃ v ∈ τ, C.Pi μ i n q v ≠ 0) ∧ ∀ n' q', ¬ Above n q n' q' → ∀ v ∈ τ, C.Pi μ i n' q' v = 0

end

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.EA
