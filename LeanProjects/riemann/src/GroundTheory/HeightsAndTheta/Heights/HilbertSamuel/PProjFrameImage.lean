import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjFrameImage
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace ProjFrameImage

variable {D : ℕ} {Ω : Type} [Field Ω] {κ : Type} [Fintype κ]

theorem linForm_projMat (e : Fin (D + 1) → Ix κ) (k : Fin (D + 1)) :
    linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨(), k⟩ = X (e k) := by
  classical
  simp only [linForm, projMat]
  rw [Finset.sum_eq_single (e k).2]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

def coneEval (x : Ix κ → Ω) :
    MvPolynomial Unit (MRing (GlobalTheory κ) ⧸ coordIdeal ℤ x) →+* Polynomial Ω :=
  eval₂Hom (Ideal.Quotient.lift (coordIdeal ℤ x) (coneMap ℤ x).toRingHom
    (fun _a ha => (RingHom.mem_ker).1 ha)) (fun _ => 1)

theorem coneEval_graphMap (x : Ix κ → Ω) (e : Fin (D + 1) → Ix κ) (f : MRing (GlobalTheory (Fin (D + 1)))) :
    coneEval x (graphMap (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))
        (rename (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1)))) f)) =
      coneMap ℤ (x ∘ e) (rename (fun q : Σ _ : Unit, Fin (D + 1) => q.2) f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [graphMap, coneEval, coneMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p q hp =>
    obtain ⟨⟨⟩, k⟩ := q
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [graphMap, inrV, coneEval, coneMap, linForm_projMat]

end ProjFrameImage

open ProjFrameImage in

theorem ProjFrameImage.proof : ProjFrameImage.Statement := by
  intro D Ω _ _ κ _ x e hP
  refine le_antisymm (fun f hf => ?_) bot_le
  have h0 : graphMap (coordIdeal ℤ x) (linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))
      (rename (inrV (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1)))) f) = 0 :=
    (RingHom.mem_ker).1 (Ideal.mem_comap.1 hf)
  have h1 : rename (fun q : Σ _ : Unit, Fin (D + 1) => q.2) f ∈ coordIdeal ℤ (x ∘ e) := by
    rw [coordIdeal, RingHom.mem_ker, ← coneEval_graphMap x e f, h0, map_zero]
  rw [hP.free, Ideal.mem_bot] at h1
  have hinj : Function.Injective (fun q : Σ _ : Unit, Fin (D + 1) => q.2) := by
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    cases h
    rfl
  exact (Ideal.mem_bot).2 (rename_injective _ hinj (by rw [h1, map_zero]))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
