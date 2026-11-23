import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem span_basis_image_adicCompletion_eq_top
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L))
    (f : v.adicCompletion K →+* v'.adicCompletion L) (hfc : Continuous f)
    (hf : ∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) :
    letI := f.toAlgebra; ∀ (n : ℕ) (b : Module.Basis (Fin n) K L),
      Submodule.span (v.adicCompletion K)
        (Set.range fun i => algebraMap L (v'.adicCompletion L) (b i)) = ⊤ := by
  letI := f.toAlgebra
  intro n b
  letI : NontriviallyNormedField (v.adicCompletion K) := Valued.toNontriviallyNormedField _ _
  set S := Submodule.span (v.adicCompletion K)
    (Set.range fun i => algebraMap L (v'.adicCompletion L) (b i)) with hS
  haveI : ContinuousSMul (v.adicCompletion K) (v'.adicCompletion L) := by
    constructor
    have : (fun p : v.adicCompletion K × v'.adicCompletion L => p.1 • p.2)
        = fun p => f p.1 * p.2 := by
      funext p; exact Algebra.smul_def _ _
    rw [this]
    exact (hfc.comp continuous_fst).mul continuous_snd
  haveI : FiniteDimensional (v.adicCompletion K) S :=
    FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have hclosed : IsClosed (S : Set (v'.adicCompletion L)) := S.closed_of_finiteDimensional
  have hmem : ∀ z : L, algebraMap L (v'.adicCompletion L) z ∈ S := by
    intro z
    rw [← b.sum_repr z, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : algebraMap L (v'.adicCompletion L) (b.repr z i • b i)
        = (algebraMap K (v.adicCompletion K) (b.repr z i)) •
            algebraMap L (v'.adicCompletion L) (b i) := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, hf]
    rw [this]
    exact S.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hdense := HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 L) L v'
  have hsub : Set.range (algebraMap L (v'.adicCompletion L)) ⊆ (S : Set _) := by
    rintro _ ⟨z, rfl⟩; exact hmem z
  have huniv : (S : Set (v'.adicCompletion L)) = Set.univ := by
    have := closure_minimal hsub hclosed
    rw [hdense.closure_range] at this
    exact Set.univ_subset_iff.mp this
  exact eq_top_iff.mpr fun x _ => by
    have : x ∈ (S : Set (v'.adicCompletion L)) := huniv ▸ Set.mem_univ x
    exact this

end GlobalTheory
