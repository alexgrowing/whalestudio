import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.EqZeroOfIsIsoSub

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

structure RiemLat (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] where
  free : Module.Free ℤ Λ
  fin : Module.Finite ℤ Λ
  rank : Module.finrank ℤ Λ = 2 * g

  form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ
  alt : ∀ x, form x x = 0
  unimod : Function.Bijective form
  adj : ∀ a a' : 𝓞 E, (a' : E) = IsCMField.complexConj E (a : E) → ∀ x y, form (a • x) y = form x (a' • y)

  P : Λ →+ (Fin g → ℂ)

  Hm : Matrix (Fin g) (Fin g) ℂ
  herm : Hm.IsHermitian
  pos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re
  im : ∀ x y, (P x ⬝ᵥ Hm *ᵥ star (P y)).im = form x y

  B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)
  act : ∀ (a : 𝓞 E) x, P (a • x) = B a (P x)

variable {E} {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] {Ψ : Type} [Fintype Ψ]

def IsCMFam (σ : Ψ → (𝓞 E →+* ℂ)) : Prop :=
  Function.Injective σ ∧ ∀ s : 𝓞 E →+* ℂ, (∃ τ, σ τ = s) ↔ ¬ ∃ τ, σ τ = (starRingEnd ℂ).comp s

namespace RiemLat

variable (R : RiemLat E g Λ)

def ip (x y : Fin g → ℂ) : ℂ := y ⬝ᵥ R.Hm *ᵥ star x

def gram {m : ℕ} (u : Fin m → Fin g → ℂ) : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun a b => R.ip (u a) (u b)

def normSq (v : Λ) : ℝ := (R.ip (R.P v) (R.P v)).re

def lam1 : ℝ := sInf {x | ∃ v : Λ, v ≠ 0 ∧ x = Real.sqrt (R.normSq v)}

def nzOf (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ) {r : ℕ} (v : Fin r → Λ) : ℝ :=
  (∏ τ, (R.gram fun a => eigComp R.B (σ τ) (R.P (v a))).det.re) /
    ((Submodule.span (𝓞 E) (Set.range v)).toAddSubgroup.relIndex I.toAddSubgroup : ℝ)

open Classical in

def nz (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ) : ℝ :=
  if h : ∃ r v, IsNzFamily I r v then R.nzOf σ I h.choose_spec.choose else 1

def IsCusp (I : Submodule (𝓞 E) Λ) : Prop := I ≠ ⊥ ∧ IsSaturated I ∧ IsIsoSub R.form I

def cuspW (σ : Ψ → (𝓞 E →+* ℂ)) : ℝ := max 0 (sSup {x | ∃ I, R.IsCusp I ∧ x = -Real.log (R.nz σ I)})

def HasRank (σ : Ψ → (𝓞 E →+* ℂ)) (m : ℕ) : Prop := ∀ τ, Module.finrank ℂ (eigSp R.B (σ τ)) = m

def logDet {m : ℕ} (b : Ψ → Fin m → Fin g → ℂ) : ℝ := ∑ τ, Real.log (R.gram (b τ)).det.re

end RiemLat

def IsHolFam {n : ℕ} (U : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) : Prop :=
  (∀ t ∈ U, ∀ t' ∈ U, (R t).form = (R t').form) ∧ ∀ x, DifferentiableOn ℂ (fun t => (R t).P x) U

def IsEigFrames {n m : ℕ} (U : Set (Fin n → ℂ)) (B : (Fin n → ℂ) → (𝓞 E →+* Module.End ℂ (Fin g → ℂ)))
    (σ : Ψ → (𝓞 E →+* ℂ)) (b : Ψ → Fin m → (Fin n → ℂ) → Fin g → ℂ) : Prop :=
  (∀ τ i, DifferentiableOn ℂ (b τ i) U) ∧ ∀ t ∈ U, ∀ τ, LinearIndependent ℂ (fun i => b τ i t) ∧
    Submodule.span ℂ (Set.range fun i => b τ i t) = eigSp (B t) (σ τ)

structure ActPeriods (F : Type) [Field F] [NumberField F] [IsCMField F] (n a g : ℕ) (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 F) Λ] extends Flat.LogPeriods n a g Λ where
  adj : ∀ c c' : 𝓞 F, (c' : F) = IsCMField.complexConj F (c : F) →
    ∀ x y, toLogPeriods.E (c • x) y = toLogPeriods.E x (c' • y)

  B : (Fin n → ℂ) → (𝓞 F →+* Module.End ℂ (Fin g → ℂ))
  B_hol : ∀ c x, DifferentiableOn ℂ (fun z => B z c x) (Metric.ball 0 1)
  act : ∀ w ∈ logCover a_le, ∀ (c : 𝓞 F) x, P w (c • x) = B (expCover a w) c (P w x)

def ActPeriods.riem {n a : ℕ} (L : ActPeriods E n a g Λ) (w : Fin n → ℂ) (hw : w ∈ logCover L.a_le) : RiemLat E g Λ where
  free := L.free
  fin := L.fin
  rank := L.rank
  form := L.toLogPeriods.E
  alt := L.alt
  unimod := L.unimod
  adj := L.adj
  P := L.P w
  Hm := L.H (expCover a w)
  herm := L.herm w hw
  pos := L.pos w hw
  im := L.im w hw
  B := L.B (expCover a w)
  act := L.act w hw

end GlobalTheory.CompanionTheory.Ar.Cusp
