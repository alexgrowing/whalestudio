import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsSelfDualFor
import Development.DiscreteGroups.GlobalIrreducibility.LConvCut

noncomputable section

open ValuativeRel Matrix MeasureTheory
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.LocLanglands

namespace GlobalTheory.GamMul

section Blocks

variable {R : Type} [CommRing R]

def put (n o₁ o₂ : ℕ) {p q : ℕ} (X : Matrix (Fin p) (Fin q) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j =>
    if h : (o₁ ≤ i.val ∧ i.val < o₁ + p) ∧ (o₂ ≤ j.val ∧ j.val < o₂ + q) then
      X ⟨i.val - o₁, by omega⟩ ⟨j.val - o₂, by omega⟩ else 0

def eye (R : Type) [CommRing R] (n o₁ o₂ p : ℕ) : Matrix (Fin n) (Fin n) R :=
  put n o₁ o₂ (1 : Matrix (Fin p) (Fin p) R)

open Classical in

def toGL {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : GL (Fin n) R := if h : IsUnit M then h.unit else 1

def uni (n o₁ o₂ : ℕ) {p q : ℕ} (X : Matrix (Fin p) (Fin q) R) : GL (Fin n) R := toGL (1 + put n o₁ o₂ X)

def dg (n o : ℕ) {p : ℕ} (g : GL (Fin p) R) : GL (Fin n) R :=
  toGL (1 - eye R n o o p + put n o o (g : Matrix (Fin p) (Fin p) R))

def shuf (R : Type) [CommRing R] (n m : ℕ) : GL (Fin n) R := toGL (eye R n 0 m (n - m) + eye R n (n - m) 0 m)

theorem toGL_val {n : ℕ} (g : GL (Fin n) R) : toGL (g : Matrix (Fin n) (Fin n) R) = g := by
  unfold toGL
  rw [dif_pos g.isUnit]
  exact Units.ext rfl

end Blocks

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def mint [MeasurableSpace k] (μ : Measure k) {p q : ℕ} (F : Matrix (Fin p) (Fin q) k → ℂ) : ℂ :=
  ∫ x : Fin p → Fin q → k, F (Matrix.of x) ∂(Measure.pi fun _ => Measure.pi fun _ => μ)

def box (p q : ℕ) (c : kˣ) : Set (Matrix (Fin p) (Fin q) k) := {X | ∀ i j, valuation k (X i j) ≤ valuation k (c : k)}

def ad {m : ℕ} (s : ℂ) (g : GL (Fin m) k) : ℂ := (absPow k s (GeneralLinearGroup.det g) : ℂ)

def intA [MeasurableSpace k] (μ : Measure k) {n m : ℕ} (i : ℕ) (W : GL (Fin n) k → ℂ) (g : GL (Fin m) k) : ℂ :=
  mint μ fun X : Matrix (Fin i) (Fin m) k => W (dg n 0 g * uni n m 0 X)

def intD [MeasurableSpace k] (μ : Measure k) {n m : ℕ} (i : ℕ) (W : GL (Fin n) k → ℂ) (g : GL (Fin m) k) : ℂ :=
  mint μ fun Y : Matrix (Fin m) (Fin i) k => W (shuf k n m * dg n 0 g * uni n 0 (n - i) Y)

def IsCuspFun {n : ℕ} (ψ : AddChar k Circle) (W : GL (Fin n) k → ℂ) : Prop :=
  (∀ u ∈ unipB k (Fin n), ∀ g, W (u * g) = (ψ (superDiag u) : ℂ) * W g) ∧
  (∃ K : Subgroup (GL (Fin n) k), IsOpen (K : Set (GL (Fin n) k)) ∧ ∀ x ∈ K, ∀ g, W (g * x) = W g) ∧
  ∃ C : Set (GL (Fin n) k), IsCompact C ∧ ∀ g, W g ≠ 0 →
    ∃ z : kˣ, ∃ u ∈ unipB k (Fin n), ∃ c ∈ C, g = GeneralLinearGroup.scalar (Fin n) z * u * c

def IsCuspSpace {n : ℕ} (ψ : AddChar k Circle) (𝒲 : Submodule ℂ (GL (Fin n) k → ℂ)) : Prop :=
  ∀ W ∈ 𝒲, IsCuspFun ψ W ∧ ∀ x, (fun g => W (g * x)) ∈ 𝒲

def whMap {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V)
    (l : Module.Dual ℂ V) : V →ₗ[ℂ] (GL (Fin n) k → ℂ) :=
  LinearMap.pi fun g => l ∘ₗ π g

def FE [MeasurableSpace k] (μ : Measure k) (ψ : AddChar k Circle) {n m : ℕ} (𝒲 : Submodule ℂ (GL (Fin n) k → ℂ))
    {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin m) k) V) (i : ℕ) (c : ℂ) : Prop :=
  ∀ l : Module.Dual ℂ V, IsFunctional ψ⁻¹ τ l → ∀ I : (GL (Fin m) k → ℂ) →ₗ[ℂ] ℂ, IsInvIntegral I →
    ∀ W ∈ 𝒲, ∀ v : V,
      I (fun g => intD μ (n - m - 1 - i) W g * ad (((n - m - 1 : ℕ) : ℂ) / 2) g * l (τ g v)) =
        c * I (fun g => intA μ i W g * ad (-((n - m - 1 : ℕ) : ℂ) / 2) g * l (τ g v))

def intJ [MeasurableSpace k] (μ : Measure k) {m m₁ m₂ : ℕ} (φ : GL (Fin m) k → ℂ) (a : GL (Fin m₁) k)
    (b : GL (Fin m₂) k) : ℂ :=
  mint μ fun x : Matrix (Fin m₂) (Fin m₁) k => φ (dg m 0 a * dg m m₁ b * uni m m₁ 0 x)

def intM [MeasurableSpace k] (μ : Measure k) {n m₁ m₂ : ℕ} (j : ℕ) (W : GL (Fin n) k → ℂ) (a : GL (Fin m₁) k)
    (b : GL (Fin m₂) k) : ℂ :=
  mint μ fun Y : Matrix (Fin m₁) (Fin j) k => W (dg n 0 b * (shuf k n m₁ * dg n 0 a * uni n 0 (n - j) Y))

def IsTest₂ {m₁ m₂ : ℕ} (ψ : AddChar k Circle) (F : GL (Fin m₁) k → GL (Fin m₂) k → ℂ) : Prop :=
  (∀ u ∈ unipB k (Fin m₁), ∀ a b, F (u * a) b = (ψ (superDiag u) : ℂ) * F a b) ∧
  (∀ u ∈ unipB k (Fin m₂), ∀ a b, F a (u * b) = (ψ (superDiag u) : ℂ) * F a b) ∧
  IsLocallyConstant (Function.uncurry F) ∧
  ∃ (C₁ : Set (GL (Fin m₁) k)) (C₂ : Set (GL (Fin m₂) k)), IsCompact C₁ ∧ IsCompact C₂ ∧ ∀ a b, F a b ≠ 0 →
    (∃ u ∈ unipB k (Fin m₁), ∃ c ∈ C₁, a = u * c) ∧ ∃ u ∈ unipB k (Fin m₂), ∃ c ∈ C₂, b = u * c

def IsAvg {m : ℕ} (m₁ m₂ : ℕ) (φ φ₀ : GL (Fin m) k → ℂ) : Prop :=
  ∃ (N : ℕ) (y : Fin N → Matrix (Fin m₂) (Fin m₁) k) (c : Fin N → ℂ), ∑ i, c i = 1 ∧
    ∀ g, φ₀ g = ∑ i, c i * φ (g * uni m m₁ 0 (y i))

def InCell {m m₁ m₂ : ℕ} (h : m₁ + m₂ = m) (φ : GL (Fin m) k → ℂ) : Prop :=
  ∃ C : Set (GL (Fin m) k), IsCompact C ∧ C ⊆ parabLower k (two (stdSum h)) ∧
    ∀ g, φ g ≠ 0 → ∃ u ∈ unipB k (Fin m), ∃ c ∈ C, g = u * c

abbrev LowSp {m m₁ m₂ : ℕ} (h : m₁ + m₂ = m) {V : Type} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GL (Fin m₁) k × GL (Fin m₂) k) V) : Type :=
  IndSpLower (two (stdSum h)) (σ.comp (leviTwo k (Fin m₁) (Fin m₂)).symm.toMonoidHom)

def lowInd {m m₁ m₂ : ℕ} (h : m₁ + m₂ = m) {V : Type} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GL (Fin m₁) k × GL (Fin m₂) k) V) : Representation ℂ (GL (Fin m) k) (LowSp h σ) :=
  ind₂Lower (stdSum h) σ

def IsBump {m m₁ m₂ : ℕ} (h : m₁ + m₂ = m) {V : Type} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GL (Fin m₁) k × GL (Fin m₂) k) V) (Λ : Set (Matrix (Fin m₁) (Fin m₂) k)) (v : V)
    (f : LowSp h σ) : Prop :=
  (∀ y ∈ Λ, f.1.1 (uni m 0 m₁ y) = v) ∧
    ∀ g, f.1.1 g ≠ 0 → ∃ p ∈ parabLower k (two (stdSum h)), ∃ y ∈ Λ, g = p * uni m 0 m₁ y

def vol [MeasurableSpace k] (μ : Measure k) {p q : ℕ} (Λ : Set (Matrix (Fin p) (Fin q) k)) : ℂ :=
  mint μ (Λ.indicator fun _ => 1)

def pairJ [MeasurableSpace k] (μ : Measure k) {m m₁ m₂ : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GL (Fin m₁) k × GL (Fin m₂) k) V) (l : Module.Dual ℂ V) (v : V) (φ : GL (Fin m) k → ℂ)
    (a : GL (Fin m₁) k) (b : GL (Fin m₂) k) : ℂ :=
  intJ μ φ a b * (ad (-(m₂ : ℂ) / 2) a * ad ((m₁ : ℂ) / 2) b) * l (σ (a, b) v)

def IsBiFun {m₁ m₂ : ℕ} (ψ : AddChar k Circle) {V : Type} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GL (Fin m₁) k × GL (Fin m₂) k) V) (l : Module.Dual ℂ V) : Prop :=
  IsFunctional ψ (σ.comp (MonoidHom.inl _ _)) l ∧ IsFunctional ψ (σ.comp (MonoidHom.inr _ _)) l

end GlobalTheory.GamMul

end
