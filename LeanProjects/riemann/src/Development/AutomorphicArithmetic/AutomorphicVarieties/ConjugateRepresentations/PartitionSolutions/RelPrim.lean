import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.RelPoin
open UpperTheory.V.Cj.A

theorem UpperTheory.V.Cj.A.relPrim :
    RelPrim := by
  intro Γ V S _ _ _ _ d G hc C hC q w hw hv
  have h0 : ∀ s, ∀ p ∈ G.Y, extDeriv (w.1 s) p = 0 := fun s p hp => by
    rw [← G.dOm_apply w s hp, hw]; rfl
  choose η hη hd hz using fun s =>
    relPoin V (Fin d → ℂ) G.Y (C s) G.isOpen hc (hC s).1 (hC s).2 q (w.1 s) (w.2 s).1 (h0 s) (hv s)
  refine ⟨⟨fun s => G.Y.indicator (η s), fun s =>
    ⟨(hη s).congr fun p hp => Set.indicator_of_mem hp _,
      fun p hp => Set.indicator_of_notMem hp _⟩⟩, ?_, ?_⟩
  · refine Subtype.ext (funext fun s => funext fun p => ?_)
    by_cases hp : p ∈ G.Y
    · rw [G.dOm_apply _ s hp, ← hd s p hp]
      refine Filter.EventuallyEq.extDeriv_eq ?_
      filter_upwards [G.isOpen.mem_nhds hp] with x hx using Set.indicator_of_mem hx _
    · rw [((G.dOm q _).2 s).2 p hp, (w.2 s).2 p hp]
  · intro s p hp
    exact (Set.indicator_of_mem ((hC s).2 hp) _).trans (hz s p hp)
