import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ShortVectorIsotropic.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : HermAtPlace.Statement h v) (h₂ : GramAtData.Statement h v)
    (h₃ : ArchInvariant.Statement h v) (h₄ : MajorantBound.Statement ι)
    (h₅ : LenSq.Statement h v) (h₆ : IntegerSmallAtPlaces.Statement E) :
    ShortVectorIsotropic.Statement h v := by
  intro M D La g x hLa hx hlen
  apply h₆ _ (hLa.integral x hx x hx)
  intro w
  set y := vecAt v x
  set z := invApply g y
  have hP : IsMajorantOf (gramAt h v w) (M.P w) :=
    ⟨M.posDef w, (h₂ w).1, (h₂ w).2, M.siegel w⟩
  obtain ⟨hnn, hsq⟩ := h₅ M z
  have hlen0 : 0 ≤ M.len z := Real.sqrt_nonneg _
  have hsq1 : M.len z ^ 2 < 1 := by nlinarith
  have hterm : (star (z w) ⬝ᵥ (M.P w *ᵥ z w)).re ≤ M.len z ^ 2 := by
    rw [hsq]
    exact Finset.single_le_sum (f := fun w' => (star (z w') ⬝ᵥ (M.P w' *ᵥ z w')).re)
      (fun w' _ => hnn w') (Finset.mem_univ w)
  have hform : w.embedding (h.toSesq x x) = star (z w) ⬝ᵥ (gramAt h v w *ᵥ z w) := by
    rw [h₁ w x x, h₃ g y y w]
  rw [← InfinitePlace.norm_embedding_eq, hform]
  exact lt_of_le_of_lt ((h₄ _ _ hP (z w)).trans hterm) hsq1

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
