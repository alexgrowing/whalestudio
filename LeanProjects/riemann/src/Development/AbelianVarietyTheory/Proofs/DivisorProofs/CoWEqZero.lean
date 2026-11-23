import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

open NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LinWAt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def coW (G : Geo σ a a') {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v) (u : Matrix (Fin a) (Fin (a + a')) (AE F E)) :
    Matrix (Fin a) (Fin (a + a')) (Fv F v) :=
  -(G.V.J.map t * u.map (piW (t.comp σ)) * (G.W.J.map t)ᵀ)

theorem coW_eq_zero (G : Geo σ a a') {v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} (t : E →ₐ[F] Fv F v)
    (u : Matrix (Fin a) (Fin (a + a')) (AE F E)) (h : u.map (piW (t.comp σ)) = 0) : coW G t u = 0 := by
  unfold coW; rw [h]; simp

end GlobalTheory.LinWAt
