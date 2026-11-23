import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart

noncomputable section

namespace GlobalTheory.ThK.LemF

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def coneEvFun (B : Base F E) {b a' : ℕ} (G : Geo σ (b + 2) a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (om : Rep σ G.V G.W) (v : Pl F)
    (ev : ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ)
    (l : ((Fin b × Fin (b + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (φ : (Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ)
    (x : UA σ G.V.J) : ℂ :=
  l (ev (locOp v (G.M.co.rho B.ψ (partFin v (shiftA H H' 1))) (locOp v (om (x, 1)) φ)))

end GlobalTheory.ThK.LemF
