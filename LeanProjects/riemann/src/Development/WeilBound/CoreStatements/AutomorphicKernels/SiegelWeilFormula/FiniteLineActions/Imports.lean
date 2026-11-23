import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealAdelicFockSpace.JnArcFin

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

theorem exists_poly {Φ : d.Fn} (hΦ : d.KFin Φ) {k : d.G} (hk : k ∈ d.K) :
    ∃ q : Polynomial ℂ, q ≠ 0 ∧ ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • d.om (k ^ i) Φ = 0 := by
  set W := Submodule.span ℂ (Set.range fun k' : d.K => d.om k'.1 Φ) with hW
  haveI : FiniteDimensional ℂ W := hΦ.2
  set φ := Polynomial.lsum (R := ℂ) (fun n => LinearMap.toSpanSingleton ℂ _ (d.om (k ^ n) Φ)) with hφ
  have hmem : ∀ p, φ p ∈ W := by
    intro p
    rw [hφ, Polynomial.lsum_apply, Polynomial.sum_def]
    refine Submodule.sum_mem _ (fun n _ => ?_)
    rw [LinearMap.toSpanSingleton_apply]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨k ^ n, pow_mem hk n⟩, rfl⟩)
  have hni : ¬ Function.Injective φ := by
    intro hinj
    have hinj' : Function.Injective (φ.codRestrict W hmem) := fun a b h => hinj (congrArg Subtype.val h)
    haveI : Module.Finite ℂ (Polynomial ℂ) := Module.Finite.of_injective _ hinj'
    have hfin : Finite ℕ := (Polynomial.basisMonomials ℂ).linearIndependent.finite
    exact not_finite ℕ
  rw [injective_iff_map_eq_zero] at hni
  push_neg at hni
  obtain ⟨q, hq0, hq⟩ := hni
  refine ⟨q, hq, ?_⟩
  rw [hφ, Polynomial.lsum_apply, Polynomial.sum_over_range] at hq0
  · simpa using hq0
  · intro n
    exact map_zero _

end PositivityTheory.SiegelWeilFormula.KFP

end
