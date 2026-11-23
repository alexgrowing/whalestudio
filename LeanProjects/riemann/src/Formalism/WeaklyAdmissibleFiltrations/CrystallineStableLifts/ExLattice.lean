import Formalism.WeaklyAdmissibleFiltrations.CocyclesFunctorial

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

theorem existsStableLattice_holds : ExLattice := by
  intro G _ LL _ O _ _ _ hinj
  have hli : LinearIndependent O (fun _ : Unit => (1 : LL)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    cases i
    simp only [Finset.univ_unique, Finset.sum_singleton, Algebra.smul_def, mul_one] at hg
    exact (map_eq_zero_iff _ hinj).mp (by simpa using hg)
  refine ⟨⟨Submodule.span O (Set.range fun _ : Unit => (1 : LL)), ?_, ?_, ?_, ?_⟩⟩
  · intro g x hx
    simpa using hx
  · exact Submodule.fg_span (Set.finite_range _)
  · exact Module.Free.of_basis (Module.Basis.span hli)
  · rw [eq_top_iff]
    intro x _
    have h1 : (1 : LL) ∈ (Submodule.span O (Set.range fun _ : Unit => (1 : LL)) : Set LL) :=
      Submodule.subset_span ⟨(), rfl⟩
    have h2 := Submodule.smul_mem (Submodule.span LL (Submodule.span O (Set.range fun _ : Unit => (1 : LL)) : Set LL)) x
      (Submodule.subset_span h1)
    simpa using h2

end Formalism.WeaklyAdmissibleFiltrations
