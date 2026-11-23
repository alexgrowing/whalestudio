import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open NumberField GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights TensorProduct

structure LinPt (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] (V : Type) [AddCommGroup V] [Module L V]
    [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] where

  ρ : 𝓞 E →+* Module.End L V

  σ : Ψ ⊕ Ψ → (𝓞 E →+* L)
  σ_bij : Function.Bijective σ
  σ_inj : ∀ s, Function.Injective (σ s)

  Λ : Submodule (𝓞 L) V
  fg : Λ.FG
  span : Submodule.span L (Λ : Set V) = ⊤
  stable : ∀ a, ∀ x ∈ Λ, ρ a x ∈ Λ

  I : AddSubgroup V
  I_le : ∀ x ∈ I, x ∈ Λ
  I_stable : ∀ a, ∀ x ∈ I, ρ a x ∈ I
  I_basis : ∃ (r : ℕ) (e : Fin r → V), LinearIndependent L e ∧ AddSubgroup.closure (Set.range e) = I

  Bq : HermitianBundle.{0} L

  f : Λ →ₗ[𝓞 L] Bq.carrier
  ker : ∀ x : Λ, f x = 0 ↔ (x : V) ∈ Submodule.span (𝓞 L) (I : Set V)
  full : ∀ y : Bq.carrier, ∃ (a : 𝓞 L) (x : Λ), a ≠ 0 ∧ f x = a • y
  orth : ∀ s s', s ≠ s' → OrthAt Bq (((eigSp ρ (σ s)).restrictScalars (𝓞 L)).comap Λ.subtype |>.map f)
    (((eigSp ρ (σ s')).restrictScalars (𝓞 L)).comap Λ.subtype |>.map f)

namespace LinPt

variable {E L Ψ : Type} [Field E] [NumberField E] [Field L] [NumberField L] {V : Type} [AddCommGroup V] [Module L V]
  [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V)

def eig (s : Ψ ⊕ Ψ) : Submodule (𝓞 L) V := A.Λ ⊓ (eigSp A.ρ (A.σ s)).restrictScalars (𝓞 L)

def tor (s : Ψ ⊕ Ψ) : Submodule (𝓞 L) V := Submodule.span (𝓞 L) (A.I : Set V) ⊓ (eigSp A.ρ (A.σ s)).restrictScalars (𝓞 L)

def img (s : Ψ ⊕ Ψ) : Submodule (𝓞 L) A.Bq.carrier := ((A.eig s).comap A.Λ.subtype).map A.f

def fam (s : Ψ ⊕ Ψ) {r k : ℕ} (v : Fin r → V) (q : Fin k → A.Λ) : Fin (r + k) → V :=
  Fin.append (fun a => eigComp A.ρ (A.σ s) (v a)) fun c => (q c : V)

def IsAdapted (s : Ψ ⊕ Ψ) {r k : ℕ} (v : Fin r → V) (q : Fin k → A.Λ) : Prop :=
  LinearIndependent L (A.fam s v q) ∧ Submodule.span L (Set.range (A.fam s v q)) = eigSp A.ρ (A.σ s)

def gramDet (ι : L →+* ℂ) {k : ℕ} (q : Fin k → A.Λ) : ℝ :=
  (Matrix.of fun c c' => (A.Bq.metric.form ι).inner ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] A.f (q c))
    ((1 : ComplexAt ι) ⊗ₜ[𝓞 L] A.f (q c'))).det.re

def labDeg (s : Ψ ⊕ Ψ) (F : Submodule (𝓞 L) V) {r k : ℕ} (v : Fin r → V) (q : Fin k → A.Λ) : ℝ :=
  (logIdx F (A.fam s v q) - (∑ ι : L →+* ℂ, Real.log (A.gramDet ι q)) / 2) / Module.finrank ℚ L

def phiDeg [Fintype Ψ] (lab : Ψ → Ψ ⊕ Ψ) (F : Ψ → Submodule (𝓞 L) V) {r k : ℕ} (v : Fin r → V)
    (q : Ψ → Fin k → A.Λ) : ℝ :=
  ∑ τ, A.labDeg (lab τ) (F τ) v (q τ) - Real.log (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) / 2 +
    Fintype.card Ψ * r / 2 * Real.log (4 * Real.pi)

end LinPt

end GlobalTheory.CompanionTheory.Ar.Cusp
