import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff

namespace GlobalTheory.TorsionForm.HorChain

theorem per_differentiableAt {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}
    (τ : E → Matrix (Fin g) (Fin g) ℂ) (x : Fl g) (b : E)
    (hτ : ∀ i j, DifferentiableAt ℂ (fun b => τ b i j) b) :
    DifferentiableAt ℂ (fun b => per (τ b) x) b := by
  rw [differentiableAt_pi]
  intro i
  simp only [per, Pi.add_apply, Matrix.vecMul, dotProduct]
  apply DifferentiableAt.add _ (differentiableAt_const _)
  apply DifferentiableAt.fun_sum
  intro j _
  exact (differentiableAt_const _).mul (hτ j i)

theorem hor_comp {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
    [NormedSpace ℂ E'] {g : ℕ} (τ : E → Matrix (Fin g) (Fin g) ℂ) (φ : E' → E) (P : Pt E' g) (v : E')
    (hφ : DifferentiableAt ℂ φ P.1) (hτ : ∀ i j, DifferentiableAt ℂ (fun b => τ b i j) (φ P.1)) :
    hor (τ ∘ φ) P v = (v, (hor τ (φ P.1, P.2) (fderiv ℂ φ P.1 v)).2) := by
  simp only [hor]
  congr 1
  have hf : flat (τ ∘ φ) P = flat τ (φ P.1, P.2) := rfl
  rw [hf]
  have h := per_differentiableAt τ (flat τ (φ P.1, P.2)) (φ P.1) hτ
  have := fderiv_comp (x := P.1) h hφ
  rw [show (fun b => per ((τ ∘ φ) b) (flat τ (φ P.1, P.2))) =
      (fun c => per (τ c) (flat τ (φ P.1, P.2))) ∘ φ from rfl, this]
  rfl

end GlobalTheory.TorsionForm.HorChain
