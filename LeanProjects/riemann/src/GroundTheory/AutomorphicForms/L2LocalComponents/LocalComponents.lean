import Mathlib
import GroundTheory.AutomorphicForms.L2LocalComponents.Summand
import GroundTheory.AutomorphicForms.SupercuspidalCoefficients

open NumberField IsDedekindDomain MeasureTheory

namespace GroundTheory.Automorphic

noncomputable section

set_option linter.unusedSectionVars false

namespace Parabolic

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {V V' : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  {π : Representation ℂ (GL (Fin n) F) V} {π' : Representation ℂ (GL (Fin n) F) V'}

theorem IsSupercuspidal.of_equiv (h : IsSupercuspidal π) (e : π.Equiv π') : IsSupercuspidal π' := by
  intro γ hγ
  haveI := h γ hγ
  have hsurj : Function.Surjective (jacquetMap F n γ e.toIntertwiningMap) := by
    intro x
    obtain ⟨a, rfl⟩ := Representation.Coinvariants.mk_surjective _ x
    refine ⟨Representation.Coinvariants.mk _ (e.toLinearEquiv.symm a), ?_⟩
    rw [jacquetMap_mk]
    congr 1
    exact e.toLinearEquiv.apply_symm_apply a
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨b, rfl⟩ := hsurj y
  rw [Subsingleton.elim a b]

theorem isSupercuspidal_iff_of_equiv (e : π.Equiv π') : IsSupercuspidal π ↔ IsSupercuspidal π' :=
  ⟨fun h => h.of_equiv e, fun h => h.of_equiv e.symm⟩

end Parabolic

namespace AutomorphicForm

open CuspidalSpectrum Parabolic

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

namespace CuspidalAutomorphicRepresentation

variable (π : CuspidalAutomorphicRepresentation K n)

def IsSupercuspidalAt (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∃ D : AdelicDecomposition π.toModule, IsSupercuspidal (D.finite.π v)

theorem isSupercuspidalAt_iff (v : HeightOneSpectrum (𝓞 K)) :
    π.IsSupercuspidalAt v ↔ ∀ D : AdelicDecomposition π.toModule, IsSupercuspidal (D.finite.π v) := by
  constructor
  · rintro ⟨D, hD⟩ D'
    obtain ⟨e⟩ := AdelicDecomposition.nonempty_equiv_local D D' v
    exact hD.of_equiv e
  · intro h
    obtain ⟨D⟩ := π.nonempty_adelicDecomposition
    exact ⟨D, h D⟩

variable {μ : Measure (Reduction.normOneGL K n)} [μ.IsHaarMeasure]

theorem nonempty_adelicDecomposition_ofSummand (V : Submodule ℂ (CuspL2 μ)) [CompleteSpace V]
    (hV : (cuspRepT μ).IsInvariant V) (hirr : ((cuspRepT μ).restrict V hV).IsIrreducible)
    (hne : summandCuspForms V ≠ ⊥) :
    Nonempty (AdelicDecomposition (ofSummand V hV hirr hne).toModule) :=
  (ofSummand V hV hirr hne).nonempty_adelicDecomposition

end CuspidalAutomorphicRepresentation

end AutomorphicForm

end

end GroundTheory.Automorphic
