import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeSquareIntegrable.FormalDegreeFromOrthogonality

noncomputable section

namespace PIW.HCFdeg

open MeasureTheory PI.UpqRep
open scoped InnerProductSpace

lemma umat_mem {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : umat g ∈ UJset ε := g.2

def repOf {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : IsCRepOn (UJset ε) σ) :
    UJ ε →* (H →L[ℂ] H) where
  toFun g := σ (umat g)
  map_one' := h.1
  map_mul' g g' := h.2 _ (umat_mem g) _ (umat_mem g')

lemma irr_repOf {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : IsCRepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) : Irr (repOf ε σ h) := by
  intro S hS hst
  refine hI S hS ?_
  intro g hg v hv
  obtain ⟨x, rfl⟩ : g ∈ Set.range (coeMatrixAlt ε) := by rw [range_coeMatrix]; exact hg
  exact hst x v hv

theorem formal_degree_orthogonality : FormalDegreeFromOrthogonality := by
  intro hOrth hUni n ε H _ _ _ _ σ hU hI hSq
  haveI := (hUni n ε).1
  haveI := (hUni n ε).2
  obtain ⟨d, hd, h⟩ := hOrth (UJ ε) (muG ε) H (repOf ε σ hU.1)
    (fun g v => hU.2.1 _ (umat_mem g) v)
    (fun v => (hU.2.2 v).comp_continuous (continuous_coeMatrix ε) umat_mem)
    (irr_repOf ε σ hU.1 hI) (fun v w => hSq v w)
  exact ⟨d, hd, fun v w v' w' => h v w v' w'⟩

end PIW.HCFdeg
