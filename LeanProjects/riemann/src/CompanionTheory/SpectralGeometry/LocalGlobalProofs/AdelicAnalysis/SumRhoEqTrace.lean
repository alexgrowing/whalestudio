import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

def toA (x : ι → F) : ι → A F := fun j => algebraMap F (A F) (x j)

theorem oh_add {x y : A F} (hx : x ∈ Oh F) (hy : y ∈ Oh F) : x + y ∈ Oh F :=
  fun v => add_mem (hx v) (hy v)

theorem oh_zero : (0 : A F) ∈ Oh F := fun _ => zero_mem _

theorem oh_neg {x : A F} (hx : x ∈ Oh F) : -x ∈ Oh F := fun v => neg_mem (hx v)

variable (ι F) in

def latN (N : ℕ) : AddSubgroup (ι → A F) where
  carrier := {x | ∀ i, ∃ y ∈ Oh F, x i = (N : A F) * y}
  add_mem' := by
    intro a b ha hb i
    obtain ⟨y, hy, e⟩ := ha i
    obtain ⟨z, hz, e'⟩ := hb i
    exact ⟨y + z, oh_add hy hz, by simp [e, e', mul_add]⟩
  zero_mem' := fun i => ⟨0, oh_zero, by simp⟩
  neg_mem' := by
    intro a ha i
    obtain ⟨y, hy, e⟩ := ha i
    exact ⟨-y, oh_neg hy, by simp [e]⟩

def indC (N : ℕ) (a : ι → F) : (ι → A F) → ℂ :=
  Set.indicator {x | x - toA a ∈ latN F ι N} fun _ => 1

def emb (ρ : InfinitePlace F → (F →+* ℝ)) (x : ι → F) : ι × InfinitePlace F → ℝ :=
  fun p => ρ p.2 (x p.1)

def cur (x : ι × InfinitePlace F → ℝ) : InfinitePlace F → ι → ℝ := fun w i => x (i, w)

def DM [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) :
    Matrix (ι × InfinitePlace F) (ι × InfinitePlace F) ℝ :=
  blockDiagonal fun w => B.map (ρ w)

def ZM [DecidableEq (InfinitePlace F)] (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (τ : InfinitePlace F → ℂ) :
    Matrix (ι × InfinitePlace F) (ι × InfinitePlace F) ℂ :=
  blockDiagonal fun w => fun i j =>
    ((τ w).re : ℂ) * ((ρ w (B i j) : ℝ) : ℂ) + Complex.I * ((τ w).im : ℂ) * ((P w i j : ℝ) : ℂ)

def EM (ρ : InfinitePlace F → (F →+* ℝ)) (b : InfinitePlace F → 𝓞 F) :
    Matrix (InfinitePlace F) (InfinitePlace F) ℝ :=
  fun w v => ρ w (b v : F)

def gM [DecidableEq (InfinitePlace F)] (ρ : InfinitePlace F → (F →+* ℝ))
    (b : InfinitePlace F → 𝓞 F) (N : ℕ) :
    Matrix (ι × InfinitePlace F) (ι × InfinitePlace F) ℝ :=
  (N : ℝ) • ((1 : Matrix ι ι ℝ) ⊗ₖ EM ρ b)

theorem sum_rho_eq_trace {ρ : InfinitePlace F → (F →+* ℝ)} (hT : IsTotallyReal F)
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (c : F) :
    ∑ w, ρ w c = ((Algebra.trace ℚ F c : ℚ) : ℝ) := by
  have h1 := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := c)
  have hb : Function.Bijective
      (fun w : InfinitePlace F => (w.embedding).toRatAlgHom) := by
    constructor
    · intro w v h
      have : w.embedding = v.embedding := by
        ext x
        exact DFunLike.congr_fun h x
      rw [← InfinitePlace.mk_embedding w, ← InfinitePlace.mk_embedding v, this]
    · intro σ
      refine ⟨InfinitePlace.mk σ.toRingHom, ?_⟩
      have hr : (InfinitePlace.mk σ.toRingHom).IsReal := hT.isReal _
      have he := InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.mp hr)
      ext x
      show ((InfinitePlace.mk σ.toRingHom).embedding) x = σ x
      rw [he]
      rfl
  have h2 : ∑ σ : F →ₐ[ℚ] ℂ, σ c = ∑ w : InfinitePlace F, w.embedding c := by
    rw [← (Equiv.ofBijective _ hb).sum_comp]
    rfl
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  simp only [hρ]
  rw [← h2, ← h1]
  simp

end GlobalTheory.CompanionTheory.SW.ThW
