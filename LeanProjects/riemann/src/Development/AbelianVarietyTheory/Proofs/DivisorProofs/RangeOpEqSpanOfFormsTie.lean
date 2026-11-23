import Mathlib
import Formalism.LocalToGlobal.Divisibility.RowSideTie
import Formalism.LocalRingCardinality.DataBu
import Formalism.QuotientMetricDivisors.FinalW
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2.DIV Formalism.L2.Indef

namespace GlobalTheory

theorem range_op_eq_span_of_formsTie :
    ∀ {K : Type} [Field K] [NumberField K] [StarRing K] {n k : ℕ} (σ : K →+* ℂ) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (j : (Fin n → K) →ₛₗ[σ] W) (H E : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W) (V : Matrix (Fin n) (Fin k) K), FormsTie σ j H E op → LinearMap.range E.mulVecLin = LinearMap.range V.mulVecLin → LinearMap.range op = Submodule.span ℂ (Set.range fun x => j (V.mulVec x)) := by
  intro K _ _ _ n k σ W _ _ j H E op V h hr
  apply le_antisymm
  · rw [← Submodule.map_top, ← h.span, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have hm : E.mulVec (Pi.single i 1) ∈ LinearMap.range V.mulVecLin := by
      rw [← hr]
      exact ⟨Pi.single i 1, rfl⟩
    obtain ⟨y, hy⟩ := hm
    refine Submodule.subset_span ⟨y, ?_⟩
    have hy' : V.mulVec y = E.mulVec (Pi.single i 1) := hy
    show j (V.mulVec y) = op (j (Pi.single i 1))
    rw [h.op_eq, hy']
  · rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    have hm : V.mulVec y ∈ LinearMap.range E.mulVecLin := by
      rw [hr]
      exact ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := hm
    have hx' : E.mulVec x = V.mulVec y := hx
    refine ⟨j x, ?_⟩
    show op (j x) = j (V.mulVec y)
    rw [h.op_eq, hx']

end GlobalTheory
