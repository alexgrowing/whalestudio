import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

def vH {K : Type} {M : ℕ} (a s : K) (Y : Fin M → K) : Fin (M + 2) → K :=
  Fin.cons a (Fin.cons s Y)

def tailH {K : Type} {M : ℕ} (x : Fin (M + 2) → K) : Fin M → K := fun i => x i.succ.succ

section Chart

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def halfR : R ⊗[F] E := inclR R (algebraMap F E (1 / 2))

def tHalf (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin (M + 2) → R ⊗[F] E) : R ⊗[F] E :=
  halfR (F := F) (E := E) R * hR R σ (hypOne J) x x

def cvec (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x v : Fin (M + 2) → R ⊗[F] E) :
    Fin (M + 2) → R ⊗[F] E :=
  vH (x 0 * v 0)
    (v 0 * x 1 + Ring.inverse (sigR R σ (x 0)) *
      (v 1 - tHalf R σ J x * v 0 - hR R σ J (tailH x) (tailH v)))
    (fun i => v 0 * x i.succ.succ + v i.succ.succ)

def chartS (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (x : Fin 1 → Fin (M + 2) → R ⊗[F] E)
    (a s : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E) : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E :=
  Fin.cons (x 0) fun j => cvec R σ J (x 0) (vH (a 0 j) (s 0 j - tHalf R σ J (x 0) * a 0 j) (Y j))

variable {R} in

def yPart {K : Type} [CommRing K] {M n : ℕ} (X : Fin (n + 1) → Fin (M + 2) → K) : Fin n → Fin M → K :=
  fun j i => X j.succ i.succ.succ - X j.succ 0 * Ring.inverse (X 0 0) * X 0 i.succ.succ

def freeCell (K : Type) [CommRing K] (M n : ℕ) : Set (Fin (n + 1) → Fin (M + 2) → K) :=
  {X | IsUnit (X 0 0) ∧ LinearIndependent K (yPart X)}

theorem sigR_sigR (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) (y : R ⊗[F] E) : sigR R σ (sigR R σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, hσ]
  | add u v hu hv => simp only [map_add, hu, hv]

def qH (σ : E →ₐ[F] E) (hσ : ∀ e, σ (σ e) = e) {n : ℕ} (t : HermR R σ 1) (s a : Fin 1 → Fin n → R ⊗[F] E) :
    HermR R σ n :=
  ⟨Matrix.of fun i j => sigR R σ (a 0 i) * s 0 j + sigR R σ (s 0 i) * a 0 j -
      (t : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 * (sigR R σ (a 0 i) * a 0 j), by
    intro i j
    have ht : sigR R σ ((t : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0) = (t : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 :=
      t.2 0 0
    simp only [Matrix.of_apply, map_add, map_sub, map_mul, sigR_sigR R σ hσ, ht]
    ring⟩

end Chart

theorem sig_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ]
  simp

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage
