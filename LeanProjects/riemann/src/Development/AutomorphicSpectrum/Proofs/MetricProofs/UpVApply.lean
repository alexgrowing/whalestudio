import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl

section Cell

variable {Ψ : Type} {N j : ℕ}

def Sep (keep : Ψ × Fin N → Prop) (q : LowIdx Ψ N j) : Prop :=
  ∃ i, keep (q.1.1, i) ∧ IsProperStep N j i ∧ q.1.2.2 ∈ stepCols N j i ∧ q.1.2.1 ∉ stepCols N j i

abbrev PIdx (j : ℕ) (keep : Ψ × Fin N → Prop) : Type := {q : LowIdx Ψ N j // Sep keep q}

def cExt (keep : Ψ × Fin N → Prop) (c : PIdx j keep → ℂ) : LowIdx Ψ N j → ℂ :=
  fun q => if h : Sep keep q then c ⟨q, h⟩ else 0

def pMat (keep : Ψ × Fin N → Prop) (c : PIdx j keep → ℂ) (τ : Ψ) : Matrix (Fin N) (Fin N) ℂ :=
  lowMat (cExt keep c) τ

def pSteps (j : ℕ) (keep : Ψ × Fin N → Prop) (τ : Ψ) (b : Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun i => keep (τ, i) ∧ IsProperStep N j i ∧ b ∈ stepCols N j i

def pStep (j : ℕ) (keep : Ψ × Fin N → Prop) (τ : Ψ) (b : Fin N) : Fin N :=
  if h : (pSteps j keep τ b).Nonempty then (pSteps j keep τ b).min' h else b

def pSgn (S : Finset (Fin N)) (a b : Fin N) : ℂ :=
  minorIJ (1 + Matrix.single a b (1 : ℂ)) (insert a (S.erase b)) S

end Cell

section Param

variable {n e : ℕ} {Λ : Type}

def pB (ε : Fin n ⊕ Λ ≃ Fin e) (w : Fin e → ℂ) : Fin n → ℂ := fun i => w (ε (Sum.inl i))

def pL (ε : Fin n ⊕ Λ ≃ Fin e) (w : Fin e → ℂ) : Λ → ℂ := fun q => w (ε (Sum.inr q))

def pD (ε : Fin n ⊕ Λ ≃ Fin e) (V : Set (Fin n → ℂ)) : Set (Fin e → ℂ) := {w | pB ε w ∈ V}

end Param

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)] {n e : ℕ}

def upV (v : (Σ k, ιk k) → (Σ k, ι k)) (z : (Σ k, ιk k) → ℂ) : (Σ k, ι k) → ℂ :=
  fun q => if h : ∃ q', v q' = q then z h.choose else 0

def pBase (M : FlagModel y Ψ N j) (v : (Σ k, ιk k) → (Σ k, ι k)) (z : (Σ k, ιk k) → ℂ) :
    (Σ k, baseIdx ι M.blk k) → ℂ := basePart M.blk (upV v z)

def pRead (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (keep : Ψ × Fin N → Prop)
    (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) (τ : Ψ) (a b : Fin N) : ℂ :=
  (M.blk (τ, pStep j keep τ b)).elim 0 fun k =>
    twMinor M F zb (pStep j keep τ b) k (h τ)⁻¹ z (insert a ((stepCols N j (pStep j keep τ b)).erase b)) /
      (pSgn (stepCols N j (pStep j keep τ b)) a b *
        twMinor M F zb (pStep j keep τ b) k (h τ)⁻¹ z (stepCols N j (pStep j keep τ b)))

def pH (keep : Ψ × Fin N → Prop) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e) (τ : Ψ)
    (w : Fin e → ℂ) : Matrix (Fin N) (Fin N) ℂ := h τ * pMat keep (pL ε w) τ

def pPhi (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (keep : Ψ × Fin N → Prop)
    (v : (Σ k, ιk k) → (Σ k, ι k)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e) (w : Fin e → ℂ) : (Σ k, ιk k) → ℂ :=
  fun q => flagZ M F (bl (pB ε w)) (fun τ => pH keep h ε τ w) (v q)

def IsPCtx (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (κ : Kk → K)
    (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
    (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : Prop :=
  IsBlockMap κ v ∧ (∀ k, k ∈ Set.range κ ↔ ((∀ p, M.blk p ≠ some k) ∨ ∃ p, keep p ∧ M.blk p = some k)) ∧
    M.IsFrame F ∧ IsBaseChart M Rb F kb V bl ∧
    (∀ z ∈ mcPts (mCoordIdeal M.x), SameOrbit (Rb.lift (r z) (r z)) z) ∧ ContinuousOn r (mcPts (mCoordIdeal M.x)) ∧
    ∀ τ, IsBlockDiag j (h τ) ∧ (h τ).det ≠ 0

def pO (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop)
    (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ))
    (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) : Set ((Σ k, ιk k) → ℂ) :=
  {z | z ∈ mcPts (mCoordIdeal (y ∘ v)) ∧ r (pBase M v z) ∈ (Rb.A.chart kb).source ∧
    Rb.A.chart kb (r (pBase M v z)) ∈ V ∧
    ∀ p k, keep p → M.blk p = some k →
      twMinor M F (pBase M v z) p.2 k (h p.1)⁻¹ (upV v z) (stepCols N j p.2) ≠ 0}

def pRho (M : FlagModel y Ψ N j) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop)
    (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n)
    (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (ε : Fin n ⊕ PIdx j keep ≃ Fin e) (z : (Σ k, ιk k) → ℂ) : Fin e → ℂ := fun i =>
  match ε.symm i with
  | Sum.inl l => Rb.A.chart kb (r (pBase M v z)) l
  | Sum.inr q => pRead M F keep (pBase M v z) h (upV v z) q.1.1.1 q.1.1.2.1 q.1.1.2.2

theorem upV_apply {v : (Σ k, ιk k) → (Σ k, ι k)} (hv : Function.Injective v) (z : (Σ k, ιk k) → ℂ) (q : Σ k, ιk k) :
    upV v z (v q) = z q := by
  have h : ∃ q', v q' = v q := ⟨q, rfl⟩
  simp only [upV, dif_pos h]
  rw [hv h.choose_spec]

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.PFl
