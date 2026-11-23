import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.CompVInvMulVec

noncomputable section

namespace PI.LevelKSplit.W.Meas

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open scoped TensorProduct

theorem measurableSet_borel_of_isClosed {X : Type} [TopologicalSpace X] {s : Set X}
    (h : IsClosed s) : MeasurableSet[borel X] s := by
  have : MeasurableSet[borel X] sᶜ := MeasurableSpace.measurableSet_generateFrom h.isOpen_compl
  simpa using this.compl

theorem lattice_borel : LatBorel := by
  classical
  intro F E _ _ _ _ _ n v Λ
  have hE := countable_nf E
  have hfd : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let _ : MeasurableSpace (Fin n → Fv F v ⊗[F] E) := borel _
  have hT2 : T2Space (Fv F v ⊗[F] E) := by
    obtain ⟨ι, _, ⟨h⟩⟩ := PI.AdicCompletionValuation.exists_homeomorph_tens (F := F) (E := E) (Fv F v)
    exact h.isEmbedding.t2Space
  have hO : CompactSpace (v.adicCompletionIntegers F) :=
    isCompact_iff_compactSpace.mp (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v)
  set S : Set (Fin n → Fv F v ⊗[F] E) := ratV (F := F) (Fv F v) '' Λ with hS
  have hSc : Countable S := ((Set.to_countable Λ).image _).to_subtype
  have hL : (latLoc (E := E) v Λ : Set (Fin n → Fv F v ⊗[F] E)) =
      ⋃ T : Finset S, (Submodule.span (v.adicCompletionIntegers F)
        (Set.range fun i : T => ((i : S) : Fin n → Fv F v ⊗[F] E)) : Set _) := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_iUnion]
    constructor
    · intro hx
      obtain ⟨T', hT'S, hxT'⟩ := Submodule.mem_span_finite_of_mem_span hx
      refine ⟨T'.subtype (· ∈ S), ?_⟩
      have : (Set.range fun i : T'.subtype (· ∈ S) => ((i : S) : Fin n → Fv F v ⊗[F] E)) =
          (T' : Set (Fin n → Fv F v ⊗[F] E)) := by
        ext y
        constructor
        · rintro ⟨i, rfl⟩
          exact Finset.mem_subtype.1 i.2
        · intro hy
          exact ⟨⟨⟨y, hT'S hy⟩, Finset.mem_subtype.2 hy⟩, rfl⟩
      rw [this]
      exact hxT'
    · rintro ⟨T, hxT⟩
      refine Submodule.span_mono ?_ hxT
      rintro _ ⟨i, rfl⟩
      exact (i : S).2
  rw [hL]
  refine MeasurableSet.iUnion fun T => measurableSet_borel_of_isClosed (IsCompact.isClosed ?_)
  rw [← Fintype.range_linearCombination]
  have hc : Continuous (Fintype.linearCombination (v.adicCompletionIntegers F)
      fun i : T => ((i : S) : Fin n → Fv F v ⊗[F] E)) := by
    have : (Fintype.linearCombination (v.adicCompletionIntegers F)
        fun i : T => ((i : S) : Fin n → Fv F v ⊗[F] E)) =
        fun c : T → v.adicCompletionIntegers F => ∑ i : T, ((c i : v.adicCompletionIntegers F) : Fv F v) • ((i : S) : Fin n → Fv F v ⊗[F] E) := by
      funext c
      rw [Fintype.linearCombination_apply]
      rfl
    rw [this]
    refine continuous_finsetSum _ fun i _ => ?_
    have h1 : Continuous fun c : T → v.adicCompletionIntegers F =>
        ((c i : v.adicCompletionIntegers F) : Fv F v) :=
      continuous_subtype_val.comp (continuous_apply i)
    exact h1.smul continuous_const
  exact isCompact_range hc

end PI.LevelKSplit.W.Meas
