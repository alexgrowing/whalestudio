import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Values

variable {κ : Type*} [Fintype κ] {ι : κ → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def IsValueAt (y : (Σ k, ι k) → Ω) (a : Ω) (z : (Σ k, ι k) → ℂ) (v : ℂ) : Prop :=
  ∃ (d : κ → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧ aeval y h ≠ 0 ∧
    aeval y g = a * aeval y h ∧ eval z (map (Int.castRingHom ℂ) h) ≠ 0 ∧
    eval z (map (Int.castRingHom ℂ) g) = v * eval z (map (Int.castRingHom ℂ) h)

def RegularAt (y : (Σ k, ι k) → Ω) (a : Ω) (z : (Σ k, ι k) → ℂ) : Prop :=
  ∃ v, IsValueAt y a z v

open Classical in

def valAt (y : (Σ k, ι k) → Ω) (a : Ω) (z : (Σ k, ι k) → ℂ) : ℂ :=
  if h : RegularAt y a z then h.choose else 0

end Values

section Frames

variable {κ : Type*} [Fintype κ] {ι : κ → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]
  {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

def IsLocSection (y : (Σ k, ι k) → Ω) (W : ChartBundle ℤ (NumbersDVR.segreVec y) N E)
    (z : (Σ k, ι k) → ℂ) (e : E) : Prop :=
  ∃ c : ∀ k, ι k, (∀ k, z ⟨k, c k⟩ ≠ 0) ∧ ∃ (m : ℕ) (a : Fin m → Ω) (s : Fin m → E),
    (∀ l, s l ∈ W.lat c) ∧ (∀ l, RegularAt y (a l) z) ∧ e = ∑ l, a l • s l

def IsFrameAt (y : (Σ k, ι k) → Ω) (W : ChartBundle ℤ (NumbersDVR.segreVec y) N E)
    (z : (Σ k, ι k) → ℂ) (b : Fin N → E) : Prop :=
  (∀ q, IsLocSection y W z (b q)) ∧
    ∀ e, IsLocSection y W z e → ∃ a : Fin N → Ω, (∀ q, RegularAt y (a q) z) ∧ e = ∑ q, a q • b q

open scoped ComplexOrder in

structure HermMetricOn (y : (Σ k, ι k) → Ω) (W : ChartBundle ℤ (NumbersDVR.segreVec y) N E)
    (U : Set ((Σ k, ι k) → ℂ)) where

  H : ((Σ k, ι k) → ℂ) → (Fin N → E) → Matrix (Fin N) (Fin N) ℂ

  posDef : ∀ z ∈ U, ∀ b, IsFrameAt y W z b → (H z b).PosDef

  frameChange : ∀ z ∈ U, ∀ (b : Fin N → E) (g : Matrix (Fin N) (Fin N) Ω) (gz : Matrix (Fin N) (Fin N) ℂ),
    IsFrameAt y W z b → (∀ p q, IsValueAt y (g p q) z (gz p q)) →
    IsFrameAt y W z (fun q => ∑ p, g p q • b p) →
    H z (fun q => ∑ p, g p q • b p) = gz.conjTranspose * H z b * gz

  scale : ∀ z ∈ U, ∀ s : κ → ℂ, (∀ k, s k ≠ 0) → (fun p => s p.1 * z p) ∈ U → ∀ b,
    IsFrameAt y W z b → H (fun p => s p.1 * z p) b = H z b

  conj : ∀ z ∈ U, (fun p => starRingEnd ℂ (z p)) ∈ U → ∀ b, IsFrameAt y W z b →
    H (fun p => starRingEnd ℂ (z p)) b = (H z b).map (starRingEnd ℂ)

  smooth : ∀ (m : ℕ) (O : Set (Fin m → ℂ)) (γ : (Fin m → ℂ) → (Σ k, ι k) → ℂ), IsOpen O →
    AnalyticOnNhd ℂ γ O → (∀ w ∈ O, γ w ∈ U) → ∀ w ∈ O, ∀ b, IsFrameAt y W (γ w) b →
      ∀ p q, ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w' => H (γ w') b p q) w

end Frames

section Charts

variable {κ : Type*} [Fintype κ] {ι : κ → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

structure SncChart (y : (Σ k, ι k) → Ω) (bd : Ideal (MRing ι)) (n : ℕ) where

  c : ∀ k, ι k

  φ : (Fin n → ℂ) → (Σ k, ι k) → ℂ

  kb : ℕ
  kb_le : kb ≤ n

  z : Fin n → Ω
  mem : ∀ w ∈ Metric.ball (0 : Fin n → ℂ) 1, φ w ∈ mcPts (mCoordIdeal y)
  normalised : ∀ w ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ k, φ w ⟨k, c k⟩ = 1
  holo : AnalyticOnNhd ℂ φ (Metric.ball 0 1)
  coord : ∀ w ∈ Metric.ball (0 : Fin n → ℂ) 1, ∀ i, IsValueAt y (z i) (φ w) (w i)
  isOpen_image : ∃ O : Set ((Σ k, ι k) → ℂ), IsOpen O ∧
    φ '' Metric.ball 0 1 = O ∩ {x | x ∈ mcPts (mCoordIdeal y) ∧ ∀ k, x ⟨k, c k⟩ = 1}
  boundary : ∀ w ∈ Metric.ball (0 : Fin n → ℂ) 1,
    φ w ∈ mcPts bd ↔ ∃ i : Fin n, (i : ℕ) < kb ∧ w i = 0

def lwP₂ {n : ℕ} (kb : ℕ) (w : Fin n → ℂ) : ℝ :=
  Real.exp 1 + ∑ i : Fin n, if (i : ℕ) < kb then Real.log (1 / ‖w i‖ ^ 2) else 0

def interiorPts (y : (Σ k, ι k) → Ω) (bd : Ideal (MRing ι)) : Set ((Σ k, ι k) → ℂ) :=
  mcPts (mCoordIdeal y) \ mcPts bd

end Charts

section Subbundles

variable {Ω : Type*} [Field Ω] {τ : Type*} {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]

def IsSubbundle {x : τ → Ω} (W : ChartBundle ℤ x N E) (V : Submodule Ω E) (r : ℕ) : Prop :=
  r ≤ N ∧ ∀ c, x c ≠ 0 → ∃ (m : ℕ) (f a : Fin m → Ω), (∀ l, f l ∈ chartRing ℤ x c) ∧
    (∀ l, a l ∈ chartRing ℤ x c) ∧ ∑ l, a l * f l = 1 ∧ ∀ l, ∃ b : Fin N → E, LinearIndependent Ω b ∧
      (∀ e, (∃ n : ℕ, f l ^ n • e ∈ W.lat c) ↔
        ∃ a' : Fin N → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a' q ∈ chartRing ℤ x c) ∧ e = ∑ q, a' q • b q) ∧
      Submodule.span Ω (b '' {q | (q : ℕ) < r}) = V

end Subbundles

section Lines

variable {κ : Type*} [Fintype κ] {ι : κ → Type*} [∀ k, Fintype (ι k)]

def IsAmpleOn (P : Ideal (MRing ι)) (a : κ → ℤ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ NefOnFibres P (fun k => (m : ℤ) * a k - 1)

def IsPositiveH (P : Ideal (MRing ι)) (A : HermLine ι) : Prop :=
  IsSmoothHerm A ∧ ∀ z ∈ mcPts P, ∀ w, IsConeTangent (Int.castRingHom ℂ) P z w →
    (¬ ∃ s : κ → ℂ, w = fun p => s p.1 * z p) → 0 < leviForm (fun z => Real.log (A.h z)) z w

structure IsVerticalCartier (P : Ideal (MRing ι)) (p : ℕ) (b : κ → ℤ) (f g : MRing ι) : Prop where
  degrees : ∃ bf bg : κ → ℕ, IsMultiHomog f bf ∧ IsMultiHomog g bg ∧
    (fun k => (bf k : ℤ) - bg k) = b
  num_not_mem : f ∉ P
  den_not_mem : g ∉ P
  unit_off_special : ∀ W : Ideal (MRing ι), W.IsPrime → P ≤ W → IsRelevant W →
    (C (p : ℤ) : MRing ι) ∉ W → ∃ u v : MRing ι, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P

end Lines

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
