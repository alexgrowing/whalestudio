import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PureEqPureA
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped TensorProduct SchwartzMap LineDeriv
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RT.Lie

section Real

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

def schV (L : V →L[ℝ] V →L[ℝ] ℝ) (a b : V) (φ : V → ℂ) : V → ℂ :=
  fun x => Complex.exp (-(2 * Real.pi * Complex.I) * ((L x b + L a b / 2 : ℝ) : ℂ)) * φ (x + a)

def dS (L : V →L[ℝ] V →L[ℝ] ℝ) (a b : V) (f : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  ∂_{a} f + (-(2 * Real.pi * Complex.I)) • SchwartzMap.smulLeftCLM ℂ (L.flip b) f

variable [MeasurableSpace V]

def IsSchL (L : V →L[ℝ] V →L[ℝ] ℝ) (μ : Measure V) (ρ₀ : V → V → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) : Prop :=
  ∀ a b (h : Lp ℂ 2 μ), ρ₀ a b h =ᵐ[μ] schV L a b h

end Real

section Arch

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F) in

def trL (κ : Type) [Fintype κ] : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousBilinearMap (LinearMap.mk₂ ℝ
    (fun x y : κ → mixedEmbedding.mixedSpace F => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * y i))
    (fun x x' y => by rw [← map_add, ← Finset.sum_add_distrib]; simp only [Pi.add_apply, add_mul])
    (fun c x y => by rw [← map_smul, Finset.smul_sum]; simp only [Pi.smul_apply, smul_mul_assoc])
    (fun x y y' => by rw [← map_add, ← Finset.sum_add_distrib]; simp only [Pi.add_apply, mul_add])
    (fun c x y => by rw [← map_smul, Finset.smul_sum]; simp only [Pi.smul_apply, mul_smul_comm]))

variable (F) in

abbrev Ix (n d : ℕ) : Type := InfinitePlace F × Fin n × Fin d

def piM (τ : ∀ w : InfinitePlace F, EmbOver E w) {n d : ℕ} (u : Matrix (Fin n) (Fin d) (AE F E)) : Ix F n d → ℂ :=
  fun p => piInf (τ p.1) (u p.2.1 p.2.2)

open Classical in

def HM (τ : ∀ w : InfinitePlace F, EmbOver E w) {n d : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E) :
    Matrix (Ix F n d) (Ix F n d) ℂ :=
  fun p q => if p.1 = q.1 then 2 * Complex.I * (τ p.1).1 (JX q.2.1 p.2.1) * (τ p.1).1 (JW q.2.2 p.2.2) else 0

open Classical in

def mM (τ : ∀ w : InfinitePlace F, EmbOver E w) (n : ℕ) {d : ℕ} (g : Matrix (Fin d) (Fin d) (AE F E)) :
    Matrix (Ix F n d) (Ix F n d) ℂ :=
  fun p q => if p.1 = q.1 ∧ p.2.1 = q.2.1 then piInf (τ p.1) (g p.2.2 q.2.2) else 0

def coA {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F ((M.co.e u).1 i)

def coB {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    Fin n × Fin d → mixedEmbedding.mixedSpace F := fun i => evI F ((M.co.e u).2 i)

end Arch

end GlobalTheory.CompanionTheory.Ar.RT.Lie

end
