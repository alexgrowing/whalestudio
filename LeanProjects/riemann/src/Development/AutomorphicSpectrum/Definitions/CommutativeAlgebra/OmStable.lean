import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

structure HTPoint (C O : Type) [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
    (c : E ≃+* E) (κ : O) (N : ℕ)
    (V Ω : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
    [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω] where

  T : Submodule O V

  ρ : 𝓞 E →+* Module.End C V

  t : Fin N → V
  free : IsFreeOn ρ T t

  e : V →ₗ[C] V →ₗ[C] C
  alt : ∀ x, e x x = 0
  nondeg : ∀ y, (∀ x, e x y = 0) → y = 0
  perfect : dualLat e T = T
  adj : ∀ (a : 𝓞 E) (x y : V), e (ρ a x) y = e x (ρ (RingOfIntegers.mapRingEquiv c a) y)

  om : Submodule O Ω
  om_lat : om.IsLattice C

  ρΩ : 𝓞 E →+* Module.End C Ω
  om_stable : ∀ (a : 𝓞 E), ∀ x ∈ om, ρΩ a x ∈ om

  ht : V →ₗ[C] Ω
  ht_lin : ∀ (a : 𝓞 E) (x : V), ht (ρ a x) = ρΩ a (ht x)
  ht_mem : ∀ x ∈ T, ht x ∈ om
  κ_ne : algebraMap O C κ ≠ 0
  κ_mem : ∀ y ∈ om, ∃ x ∈ T, ht x = κ • y
  lagr : ∀ x, ht x = 0 ↔ ∀ y, ht y = 0 → e x y = 0

namespace HTPoint

variable {C O : Type} [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {κ : O} {N : ℕ}
  {V Ω : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]
  (P : HTPoint C O c κ N V Ω)

def W : Submodule C V := LinearMap.ker P.ht

def om' : Submodule O Ω := P.T.map (P.ht.restrictScalars O)

def lie : Submodule O V :=
  dualLat P.e.flip (P.om.comap (P.ht.restrictScalars O)) ⊓ P.W.restrictScalars O

def Wsp (σ : E →+* C) : Submodule C V := P.W ⊓ eigSp P.ρ σ

def Ωsp (σ : E →+* C) : Submodule C Ω := eigSp P.ρΩ σ

def WHT (σ : E →+* C) : Submodule O V := P.W.restrictScalars O ⊓ eigQuot P.ρ σ P.T

def W' (σ : E →+* C) : Submodule O V := P.W.restrictScalars O ⊓ eigSub P.ρ σ P.T

def Wrec (σ : E →+* C) : Submodule O V := eigSub P.ρ σ P.lie

def omHT (σ : E →+* C) : Submodule O Ω := eigQuot P.ρΩ σ P.om'

def omRec (σ : E →+* C) : Submodule O Ω := eigQuot P.ρΩ σ P.om

def dW (v : Valuation C NNReal) (σ : E →+* C) {j : ℕ} (b : Basis (Fin j) C (P.Wsp σ)) (i : Fin j) : ℝ :=
  grLog v (latIn (P.WHT σ) (P.Wsp σ)) b i - grLog v (latIn (P.Wrec σ) (P.Wsp σ)) b i

def dΩ (v : Valuation C NNReal) (σ : E →+* C) {k : ℕ} (b : Basis (Fin k) C (P.Ωsp σ)) (i : Fin k) : ℝ :=
  grLog v (latIn (P.omHT σ) (P.Ωsp σ)) b i - grLog v (latIn (P.omRec σ) (P.Ωsp σ)) b i

def phiDiff (v : Valuation C NNReal) {Ψ : Type} [Fintype Ψ] (τ : Ψ → (E →+* C)) {j k : Ψ → ℕ}
    (bW : ∀ s, Basis (Fin (j s)) C (P.Wsp (τ s))) (bΩ : ∀ s, Basis (Fin (k s)) C (P.Ωsp (τ s)))
    (lW : ∀ s, Fin (j s) → ℝ) (lΩ : ∀ s, Fin (k s) → ℝ) : ℝ :=
  ∑ s, ((∑ i, lW s i * P.dW v (τ s) (bW s) i) + ∑ i, lΩ s i * P.dΩ v (τ s) (bΩ s) i)

def tate (x : Fin N → 𝓞 E) : V := ∑ i, P.ρ (x i) (P.t i)

end HTPoint

end GlobalTheory.CompanionTheory.Ar.HT
