import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.PerCApply

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open Polynomial
open scoped Classical

namespace UpperTheory.Gal.W2

variable {F : Type} [Field F] [NumberField F]

def rts (χ : F[X]) (τ : F →+* ℂ) : Multiset ℂ := (χ.map τ).roots

def ballW (t₀ : F →+* ℂ) (y : ℂ) (χ : F[X]) (mu : ℂ) : ℂ :=
  (((rts χ t₀).erase mu).map fun r => (r - y * mu) / (r - mu)).prod

def fibW (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ) (x : F) (y : ℂ) (χ : F[X]) (mu : ℂ) : ℂ :=
  ((1 - t₀ x * (y * mu)) * (((rts χ t₀).erase mu).map fun r => 1 - t₀ x * r).prod) *
  ((1 - (starRingEnd ℂ) (t₀ x) * (starRingEnd ℂ) mu) *
    (((rts χ t₀).erase mu).map fun r => 1 - (starRingEnd ℂ) (t₀ x) * (y * (starRingEnd ℂ) r)).prod) *
  ∏ τ ∈ (Finset.univ.erase t₀).erase (ComplexEmbedding.conjugate t₀), ((rts χ τ).map fun r => 1 - τ x * (y ^ ε τ * r)).prod

def locW (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ) {k : ℕ} (α : Fin k → 𝓞 F) (y : ℂ) (χ : F[X]) (mu : ℂ) : ℂ :=
  ballW t₀ y χ mu * ∏ s, fibW t₀ ε (α s : F) y χ mu

variable {O : Type} [Ring O] {bar : O → O} {g : ℕ}

def typeMult (n : ℕ) (t₀ : F →+* ℂ) (ε : (F →+* ℂ) → ℕ) (τ : F →+* ℂ) : ℕ :=
  if τ = t₀ then 1 else if τ = ComplexEmbedding.conjugate t₀ then n - 1 else n * ε τ

structure IsSig (a : 𝓞 F →+* O) (bar : O → O) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (n : ℕ) (t₀ : F →+* ℂ)
    (ε : (F →+* ℂ) → ℕ) : Prop where
  onto : Function.Surjective a
  conj : ∀ c : 𝓞 F, ∃ c' : 𝓞 F, bar (a c) = a c' ∧ ∀ τ : F →+* ℂ, τ (c' : F) = (starRingEnd ℂ) (τ (c : F))
  cx : ∀ τ : F →+* ℂ, ComplexEmbedding.conjugate τ ≠ τ
  pos : 1 ≤ n
  eps : ∀ τ, τ ≠ t₀ → τ ≠ ComplexEmbedding.conjugate t₀ → ε τ + ε (ComplexEmbedding.conjugate τ) = 1
  tr : ∀ c : 𝓞 F, (ρ (a c)).trace = ∑ τ : F →+* ℂ, (typeMult n t₀ ε τ : ℂ) * τ (c : F)

def Kills (a : 𝓞 F →+* O) {L : Type} [AddCommGroup L] [Module O L] (ga : L →ₗ[O] L) (q : (𝓞 F)[X]) : Prop :=
  ∀ x, (q.sum fun i b => a b • (ga ^ i) x) = 0

def IsMinOf (a : 𝓞 F →+* O) {L : Type} [AddCommGroup L] [Module O L] (ga : L →ₗ[O] L) (χ : F[X]) : Prop :=
  χ.Monic ∧ ∀ q : (𝓞 F)[X], Kills a ga q ↔ χ ∣ q.map (algebraMap (𝓞 F) F)

def IsMark (a : 𝓞 F →+* O) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (t₀ : F →+* ℂ) (H : Matrix (Fin g) (Fin g) ℂ) (mu : ℂ) : Prop :=
  ∃ v : Fin g → ℂ, v ≠ 0 ∧ (∀ c : 𝓞 F, ρ (a c) *ᵥ v = t₀ (c : F) • v) ∧ H *ᵥ v = mu • v

def IsDiag (a : 𝓞 F →+* O) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (H Sb : Matrix (Fin g) (Fin g) ℂ) (ty : Fin g → (F →+* ℂ))
    (ev : Fin g → ℂ) : Prop :=
  Sb.det ≠ 0 ∧ (∀ c : 𝓞 F, ρ (a c) * Sb = Sb * Matrix.diagonal fun i => ty i (c : F)) ∧ H * Sb = Sb * Matrix.diagonal ev

def evAt (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ) (τ : F →+* ℂ) : Multiset ℂ :=
  (Finset.univ.filter fun i => ty i = τ).val.map ev

def evFull (ty : Fin g → (F →+* ℂ)) (ev : Fin g → ℂ) (τ : F →+* ℂ) : Multiset ℂ :=
  evAt ty ev τ + (evAt ty ev (ComplexEmbedding.conjugate τ)).map (starRingEnd ℂ)

def diagAct (a : 𝓞 F →+* O) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) {k : ℕ} (α : Fin k → 𝓞 F) :
    (Fin k → Fin g → ℂ) →ₗ[ℂ] (Fin k → Fin g → ℂ) :=
  LinearMap.pi fun j => (Matrix.toLin' (ρ (a (α j)))) ∘ₗ LinearMap.proj j

end UpperTheory.Gal.W2
