import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN

def pos (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℕ :=
  if i.val < r then i.val else if i.val ≤ r + k then r else i.val - k

def Dep (k r d : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  ∀ i j, pos k r j < pos k r i + d → X i j = 0

abbrev UTr (r : ℕ) : Type := {p : Fin r × Fin r // p.1 < p.2}

abbrev Bk (r : ℕ) : Type := UTr r ⊕ Fin r ⊕ UTr r ⊕ Fin r

def VM (k r : ℕ) : Bk r → Type
  | .inl _ => ℂ
  | .inr (.inl _) => Fin (k + 1) → ℂ
  | .inr (.inr (.inl _)) => ℂ
  | .inr (.inr (.inr _)) => ℝ

instance instVM (k r : ℕ) : ∀ β, AddCommGroup (VM k r β)
  | .inl _ => inferInstanceAs (AddCommGroup ℂ)
  | .inr (.inl _) => inferInstanceAs (AddCommGroup (Fin (k + 1) → ℂ))
  | .inr (.inr (.inl _)) => inferInstanceAs (AddCommGroup ℂ)
  | .inr (.inr (.inr _)) => inferInstanceAs (AddCommGroup ℝ)

def cM (k r : ℕ) : ∀ β : Bk r, Mt k r → VM k r β
  | .inl p, x => x (eI k r p.1.1) (eI k r p.1.2)
  | .inr (.inl a), x => fun j => x (eI k r a) (wI k r j)
  | .inr (.inr (.inl p)), x => x (eI k r p.1.1) (esI k r p.1.2)
  | .inr (.inr (.inr a)), x => (x (eI k r a) (esI k r a)).im

def degB (r : ℕ) : Bk r → ℕ
  | .inl p => p.1.2.val - p.1.1.val
  | .inr (.inl a) => r - a.val
  | .inr (.inr (.inl p)) => 2 * r - p.1.1.val - p.1.2.val
  | .inr (.inr (.inr a)) => 2 * r - 2 * a.val

section Glob

variable {E : Type} [Field E] [NumberField E]

def gM {k r : ℕ} (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (w : InfinitePlace E) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  A w * γ.map w.embedding * (A w)⁻¹

def actM {k r : ℕ} (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (x : InfinitePlace E → Mt k r) :
    InfinitePlace E → Mt k r :=
  fun w => Matrix.of.symm (A w * γ.map w.embedding * (A w)⁻¹ * Matrix.of (x w))

def GN (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
    (P : Matrix (Fin n) (Fin (r + 1)) E) : Set (Matrix (Fin n) (Fin n) E) :=
  {γ | InN σ J P γ ∧ latMap γ Λ = Λ}

def ideLat (I : FractionalIdeal (𝓞 E)⁰ E) (c : ℝ) : AddSubgroup (InfinitePlace E → ℂ) where
  carrier := {z | ∃ y ∈ I, ∀ w, z w = (c : ℂ) * w.embedding y}
  zero_mem' := ⟨0, (I : Submodule (𝓞 E) E).zero_mem, by simp⟩
  add_mem' := by
    rintro a b ⟨y, hy, h⟩ ⟨y', hy', h'⟩
    exact ⟨y + y', (I : Submodule (𝓞 E) E).add_mem hy hy', fun w => by simp [h, h', mul_add]⟩
  neg_mem' := by
    rintro a ⟨y, hy, h⟩
    exact ⟨-y, (I : Submodule (𝓞 E) E).neg_mem hy, fun w => by simp [h]⟩

def skewLat (σ : E →+* E) (I : FractionalIdeal (𝓞 E)⁰ E) (c : ℝ) : AddSubgroup (InfinitePlace E → ℝ) where
  carrier := {z | ∃ y ∈ I, σ y = -y ∧ ∀ w, z w = c * (w.embedding y).im}
  zero_mem' := ⟨0, (I : Submodule (𝓞 E) E).zero_mem, by simp, by simp⟩
  add_mem' := by
    rintro a b ⟨y, hy, hs, h⟩ ⟨y', hy', hs', h'⟩
    exact ⟨y + y', (I : Submodule (𝓞 E) E).add_mem hy hy', by simp [hs, hs']; ring, fun w => by simp [h, h', mul_add]⟩
  neg_mem' := by
    rintro a ⟨y, hy, hs, h⟩
    exact ⟨-y, (I : Submodule (𝓞 E) E).neg_mem hy, by simp [hs], fun w => by simp [h]⟩

def midLat (σ : E →+* E) {k r : ℕ} (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E)
    (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (I : FractionalIdeal (𝓞 E)⁰ E) :
    Set (Fin (2 * r + k + 1) → E) :=
  {t | (∀ a : Fin r, form σ J t (fun i => P i a.castSucc) = 0 ∧ form σ J t (fun i => f i a) = 0) ∧
    ∀ c ∈ I⁻¹, c • t ∈ Λ}

def homLat (σ : E →+* E) {k r : ℕ} (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E)
    (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E)
    (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (I : FractionalIdeal (𝓞 E)⁰ E) (c : ℝ) : Set (InfinitePlace E → Fin (k + 1) → ℂ) :=
  {z | ∃ t ∈ midLat σ J Λ P f I, ∀ w l,
    z w l = (c : ℂ) * herm (Hpk k r) (bvec (wI k r l)) ((A w).mulVec fun i => w.embedding (t i))}

end Glob

section Bundle

variable {E : Type} [Field E] [NumberField E]

def HasDom {V : Type} [AddCommGroup V] [MeasurableSpace V] (μ : Measure V) (L : Set V) (c : ℝ≥0∞) : Prop :=
  ∃ D : Set V, MeasurableSet D ∧ (∀ v, ∃! l, l ∈ L ∧ v + l ∈ D) ∧ μ D = c

def blkSet (ι : Type) (k r : ℕ) (SU : UTr r → Set (ι → ℂ)) (SH : Fin r → Set (ι → Fin (k + 1) → ℂ))
    (SC : UTr r → Set (ι → ℂ)) (SG : Fin r → Set (ι → ℝ)) : ∀ β : Bk r, Set (ι → VM k r β)
  | .inl p => SU p
  | .inr (.inl a) => SH a
  | .inr (.inr (.inl p)) => SC p
  | .inr (.inr (.inr a)) => SG a

def IsVolData {F : Type} [Field F] [NumberField F] [Algebra F E] (σ : E →ₐ[F] E) {k r : ℕ}
    (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E))
    (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F)
    (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ) : Prop :=
  IsCMExt F E σ ∧ Algebra.FormallyUnramified (𝓞 F) (𝓞 E) ∧ IsHermND σ J ∧
    GlobalTheory.SgGlob.SelfDual (σ : E →+* E) J Λ ∧ IsFrame (σ : E →+* E) J (algebraMap F E T) P ∧
    IsDual (σ : E →+* E) J P f ∧ tupLat (id1 E r) (sideM P f) ≤ Λ ∧ IsModelAt J A ∧ (∀ a, 0 < s a) ∧
    Adapted A P f s

def rowE (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (e y : Fin n → E) (t : E) : Matrix (Fin n) (Fin n) E :=
  fun i j => (if i = j then 1 else 0) + (y i + t * e i) * Matrix.vecMul (fun l => σ (e l)) J j -
    e i * Matrix.vecMul (fun l => σ (y l)) J j

end Bundle

end GlobalTheory.SnMass.VolN
