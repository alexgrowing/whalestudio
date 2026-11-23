import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

structure OrbitChart (P : Ideal (MRing ι)) (e : ℕ) where

  D : Set (Fin e → ℂ)
  isOpen_D : IsOpen D

  φ : (Fin e → ℂ) → (Σ k, ι k) → ℂ
  holo : ∀ p, AnalyticOnNhd ℂ (fun w => φ w p) D
  mem : ∀ w ∈ D, φ w ∈ mcPts P

  O : Set ((Σ k, ι k) → ℂ)
  O_open : ∃ O' : Set ((Σ k, ι k) → ℂ), IsOpen O' ∧ O = O' ∩ mcPts P
  O_orbit : ∀ z ∈ O, ∀ z' ∈ mcPts P, SameOrbit z' z → z' ∈ O

  ρ : ((Σ k, ι k) → ℂ) → Fin e → ℂ
  ρ_cont : ContinuousOn ρ O
  ρ_orbit : ∀ z ∈ O, ∀ z' ∈ O, SameOrbit z' z → ρ z' = ρ z
  φ_mem_O : ∀ w ∈ D, φ w ∈ O
  ρ_φ : ∀ w ∈ D, ρ (φ w) = w
  ρ_mem : ∀ z ∈ O, ρ z ∈ D
  φ_ρ : ∀ z ∈ O, SameOrbit (φ (ρ z)) z
  immersion : ∀ w ∈ D, ∀ p : (k : K) → ι k, (∀ k, φ w ⟨k, p k⟩ ≠ 0) →
    (fderiv ℂ (fun w' => affCoord p (φ w')) w).ker = ⊥

end Orbit

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def stepOf (N j : ℕ) (c : Fin N) : Fin N :=
  ⟨if N - j ≤ (c : ℕ) then (c : ℕ) - (N - j) else (c : ℕ) + j, by
    have := c.2
    split_ifs <;> omega⟩

def lowMat (c : LowIdx Ψ N j → ℂ) (τ : Ψ) : Matrix (Fin N) (Fin N) ℂ := fun a b =>
  if h : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) then c ⟨(τ, a, b), h⟩ else if a = b then 1 else 0

def flagZ (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : (Σ k, ι k) → ℂ := fun q =>
  if e : ∃ p, M.blk p = some q.1 then
    ∑ I, valAt M.x (F.u q I) zb * minorIJ (h e.choose.1) I (stepCols N j e.choose.2)
  else zb ⟨⟨q.1, fun p hp => e ⟨p, hp⟩⟩, q.2⟩

def sqZ (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (k₀ : K) (τ : Ψ) (ca cb : Fin N) (t : ℂ) :
    (Σ o : Option K, ι (o.getD k₀)) → ℂ
  | ⟨some k, m⟩ => flagZ M F zb h ⟨k, m⟩
  | ⟨none, m⟩ => flagZ M F zb (Function.update h τ (h τ * (1 + Matrix.single cb ca t))) ⟨k₀, m⟩

def pluck (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (k : K)
    (z : (Σ k, ι k) → ℂ) (I : Finset (Fin N)) : ℂ :=
  ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) zb * z ⟨k, m⟩

def twMinor (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (i : Fin N)
    (k : K) (g : Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) (J : Finset (Fin N)) : ℂ :=
  ∑ I ∈ Finset.univ.filter (IsStepRows N j i), minorIJ g J I * pluck M F zb k z I

def lowRead (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) (τ' : Ψ) (a' b' : Fin N) : ℂ :=
  (M.blk (τ', stepOf N j b')).elim 0 fun k =>
    twMinor M F zb (stepOf N j b') k (h τ')⁻¹ z (insert a' ((stepCols N j (stepOf N j b')).erase b')) /
      twMinor M F zb (stepOf N j b') k (h τ')⁻¹ z (stepCols N j (stepOf N j b'))

def baseOf (M : FlagModel y Ψ N j) (k₀ : K) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) :
    (Σ k, baseIdx ι M.blk k) → ℂ := basePart M.blk (fstPt k₀ z)

abbrev wP (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) :
    Ideal (MRing fun o : Option K => ι (o.getD k₀)) :=
  mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)

section Param

variable {n e : ℕ} {Λ : Type}

def wB (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (w : Fin e → ℂ) : Fin n → ℂ := fun i => w (ε (Sum.inl i))

def wL (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (w : Fin e → ℂ) : Λ → ℂ := fun q => w (ε (Sum.inr (Sum.inl q)))

def wT (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (w : Fin e → ℂ) : ℂ := w (ε (Sum.inr (Sum.inr ())))

def wD (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (V : Set (Fin n → ℂ)) : Set (Fin e → ℂ) := {w | wB ε w ∈ V}

end Param

variable {n e : ℕ}

def wH (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (τ' : Ψ) (w : Fin e → ℂ) :
    Matrix (Fin N) (Fin N) ℂ := h τ' * lowMat (wL ε w) τ'

def wPhi (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (k₀ : K) (τ : Ψ) (ca cb : Fin N)
    (w : Fin e → ℂ) : (Σ o : Option K, ι (o.getD k₀)) → ℂ :=
  sqZ M F (bl (wB ε w)) (fun τ' => wH h ε τ' w) k₀ τ ca cb (wT ε w)

def IsBaseChart (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (F : FrameData ι Ψ N M.Ω M.blk)
    (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) : Prop :=
  IsOpen V ∧ V ⊆ (Rb.A.chart kb).target ∧ (∀ q, AnalyticOnNhd ℂ (fun w => bl w q) V) ∧
    (∀ q I, AnalyticOnNhd ℂ (fun w => valAt M.x (F.u q I) (bl w)) V) ∧
    ∀ w ∈ V, bl w ∈ mcPts (mCoordIdeal M.x) ∧ (∀ k, bl w ⟨k, F.c k⟩ = 1) ∧ M.GoodAt F (mCoordIdeal (bl w)) ∧
      SameOrbit (Rb.lift ((Rb.A.chart kb).symm w) ((Rb.A.chart kb).symm w)) (bl w)

def IsWCtx (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N)
    (d : ℕ) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
    (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  (b : ℕ) = a + 1 ∧ ((b : ℕ) < j ∨ j ≤ (a : ℕ)) ∧ M.blk (τ, a) = some k₀ ∧ (ca : ℕ) = lastCol N j a ∧
    (cb : ℕ) = ca + 1 ∧ IsArithVar (mCoordIdeal y) (d + 2) ∧ M.IsFrame F ∧ IsBaseChart M Rb F kb V bl ∧
    (∀ z ∈ mcPts (mCoordIdeal M.x), SameOrbit (Rb.lift (r z) (r z)) z) ∧ ContinuousOn r (mcPts (mCoordIdeal M.x)) ∧
    ∀ τ', IsBlockDiag j (h τ') ∧ (h τ').det ≠ 0

def wO (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N)
    (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
    (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) :
    Set ((Σ o : Option K, ι (o.getD k₀)) → ℂ) :=
  {z | z ∈ mcPts (wP M τ a k₀ ca cb) ∧ r (baseOf M k₀ z) ∈ (Rb.A.chart kb).source ∧
    Rb.A.chart kb (r (baseOf M k₀ z)) ∈ V ∧
    (∀ p k, M.blk p = some k →
      twMinor M F (baseOf M k₀ z) p.2 k (h p.1)⁻¹ (fstPt k₀ z) (stepCols N j p.2) ≠ 0) ∧
    twMinor M F (baseOf M k₀ z) a k₀ (h τ)⁻¹ (sndPt k₀ z) (stepCols N j a) ≠ 0}

def wRho (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (k₀ : K) (ca cb : Fin N)
    (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e)
    (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) : Fin e → ℂ := fun i =>
  match ε.symm i with
  | Sum.inl l => Rb.A.chart kb (r (baseOf M k₀ z)) l
  | Sum.inr (Sum.inl q) => lowRead M F (baseOf M k₀ z) h (fstPt k₀ z) q.1.1 q.1.2.1 q.1.2.2
  | Sum.inr (Sum.inr _) =>
    lowRead M F (baseOf M k₀ z) h (sndPt k₀ z) τ cb ca - lowRead M F (baseOf M k₀ z) h (fstPt k₀ z) τ cb ca

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.WMan
