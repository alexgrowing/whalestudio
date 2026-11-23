import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinrankMaxUnramifiedSubfieldPadicFinExtPos
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.HubLoc Module

namespace GlobalTheory

theorem finrank_le_of_subset_closure_range {l : ℕ} [Fact l.Prime] {E : Type} [Field E] [NumberField E]
    (J : E →+* PadicAlgCl l) (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    (hdense : (K : Set (PadicAlgCl l)) ⊆ closure (Set.range J)) :
    finrank ℚ_[l] ↥K ≤ finrank ℚ E := by
  classical
  let b := Module.finBasis ℚ E
  let S : Submodule ℚ_[l] (PadicAlgCl l) := Submodule.span ℚ_[l] (Set.range fun k => J (b k))
  have hfd : FiniteDimensional ℚ_[l] S := FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have hcl : IsClosed (S : Set (PadicAlgCl l)) := Submodule.closed_of_finiteDimensional S
  have hsub : Set.range J ⊆ S := by
    rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    refine S.sum_mem fun k _ => ?_
    have e : J (b.repr x k • b k) = ((b.repr x k : ℚ) : ℚ_[l]) • J (b k) := by
      rw [Rat.smul_def, map_mul, map_ratCast, Algebra.smul_def, map_ratCast]
    rw [e]
    exact S.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩)
  have hle : K.toSubalgebra.toSubmodule ≤ S := fun x hx => closure_minimal hsub hcl (hdense hx)
  have h1 : finrank ℚ_[l] ↥K.toSubalgebra.toSubmodule ≤ finrank ℚ_[l] S := Submodule.finrank_mono hle
  have h2 : finrank ℚ_[l] S ≤ finrank ℚ E := by
    have := finrank_range_le_card (R := ℚ_[l]) (fun k => J (b k))
    simpa [Set.finrank] using this
  exact le_trans h1 h2

theorem bridge_finrank_le (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E))
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    finrank ℚ_[D.nd.l i] ↥(D.nbr i w hw).Kw.1 ≤ 4 * D.R.n := by
  have h1 : finrank ℚ D.host.E = 4 * D.R.ord := D.host.finrank_cmField
  have h2 := finrank_le_of_subset_closure_range
    ((D.nbr i w hw).j.comp (algebraMap D.host.E D.nd.Om)) (D.nbr i w hw).Kw.1 (D.nbr i w hw).j_dense
  have h3 : D.R.n = D.R.ord := rfl
  have h4 : finrank ℚ D.host.E = 4 * D.R.n := by rw [h1, h3]
  exact le_trans h2 h4.le

end GlobalTheory
