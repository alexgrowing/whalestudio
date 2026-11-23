import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

noncomputable section

namespace GlobalTheory.PlaneBasis

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : Pl F}

def basV (τ : E →ₐ[F] Fv F v) {b : ℕ} (H : Plane E (b + 2) b) : Matrix (Fin (b + 2)) (Fin (b + 2)) (Fv F v) :=
  fun r i => if h0 : i.1 = 0 then τ (H.x r) else if h : i.1 = b + 1 then τ (H.y r) else
    τ (H.ι r ⟨i.1 - 1, by have := i.2; omega⟩)

def basW (τ : E →ₐ[F] Fv F v) {a b : ℕ} (H' : Plane E (a + (b + 2)) (a + b)) :
    Matrix (Fin (a + (b + 2))) (Fin (a + (b + 2))) (Fv F v) :=
  fun r j => if ha : j.1 = a then τ (H'.x r) else if hb : j.1 = a + b + 1 then τ (H'.y r) else
    if h : j.1 < a then τ (H'.ι r ⟨j.1, by omega⟩) else τ (H'.ι r ⟨j.1 - 1, by have := j.2; omega⟩)

def crdP (τ : E →ₐ[F] Fv F v) {b : ℕ} (H : Plane E (b + 2) b) : Matrix (Fin (b + 2)) (Fin (b + 2)) (Fv F v) :=
  (basV τ H)ᵀ⁻¹

def crdQ (τ : E →ₐ[F] Fv F v) {a b : ℕ} (H' : Plane E (a + (b + 2)) (a + b)) :
    Matrix (Fin (a + (b + 2))) (Fin (a + (b + 2))) (Fv F v) :=
  (basW τ H')⁻¹

end GlobalTheory.PlaneBasis

end
