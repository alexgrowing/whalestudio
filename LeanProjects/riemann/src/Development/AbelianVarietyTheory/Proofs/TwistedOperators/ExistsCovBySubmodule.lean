import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviEmbMulSingle
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible

open GlobalTheory.PRep GlobalTheory.SmGL

namespace GlobalTheory.IrrSubquot

theorem exists_covBy_submodule {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Nontrivial M] :
    ∃ S T : Submodule R M, T ⋖ S := by
  obtain ⟨m, hm⟩ := exists_ne (0 : M)
  haveI := CompleteLattice.Iic_coatomic_of_compact_element (Submodule.singleton_span_isCompactElement (R := R) m)
  rcases IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Set.Iic (Submodule.span R {m})) with h0 | ⟨c, hc, -⟩
  · have h1 : (⊥ : Submodule R M) = Submodule.span R {m} := congrArg Subtype.val h0
    exact absurd (Submodule.mem_span_singleton_self m) (by rw [← h1]; simpa using hm)
  · refine ⟨Submodule.span R {m}, c.1, lt_of_le_of_ne c.2 fun h => hc.1 (Subtype.ext h), ?_⟩
    intro x h1 h2
    have := congrArg Subtype.val (hc.2 ⟨x, h2.le⟩ h1)
    exact h2.ne this

theorem exists_irreducible_subquotient : ∀ (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V), Nontrivial V → ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y)
      (σ : Representation ℂ G Y), σ.IsIrreducible ∧ IsSubquotient σ ρ := by
  intro G _ V _ _ ρ hV
  haveI : Nontrivial ρ.asModule := hV
  obtain ⟨S, T, h⟩ := exists_covBy_submodule (R := MonoidAlgebra ℂ G) (M := ρ.asModule)
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  have h' : e.symm T ⋖ e.symm S :=
    ⟨e.symm.lt_iff_lt.2 h.1, fun c h1 h2 => h.2 (c := e c) (by simpa using e.lt_iff_lt.2 h1)
      (by simpa using e.lt_iff_lt.2 h2)⟩
  refine ⟨_, _, _, subQuot (e.symm S) (e.symm T), isIrreducible_subQuot h', e.symm S,
    ⟨Submodule.mkQ _, fun g => ?_⟩, Submodule.mkQ_surjective _⟩
  ext x
  rfl

end GlobalTheory.IrrSubquot
