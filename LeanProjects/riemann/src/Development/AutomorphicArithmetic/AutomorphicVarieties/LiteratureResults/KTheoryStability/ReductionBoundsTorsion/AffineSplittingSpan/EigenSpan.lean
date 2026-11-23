import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Transfer

noncomputable section

open NumberField

namespace PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes

variable (L : Type) [Field L] [NumberField L]

def embLin (σ : L →+* ℂ) : 𝓞 L →ₗ[ℤ] ℂ := (σ.comp (algebraMap (𝓞 L) L)).toAddMonoidHom.toIntLinearMap

def coeLin : (𝓞 L →ₗ[ℤ] ℂ) →ₗ[ℂ] (𝓞 L → ℂ) where
  toFun f := ⇑f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem embLin_linIndep : LinearIndependent ℂ (embLin L) := by
  have hinj : Function.Injective
      (fun σ : L →+* ℂ => ((σ.comp (algebraMap (𝓞 L) L)).toMonoidHom : 𝓞 L →* ℂ)) := by
    intro σ τ h
    apply IsFractionRing.ringHom_ext (A := 𝓞 L)
    intro x
    exact DFunLike.congr_fun h x
  have h1 := (linearIndependent_monoidHom (𝓞 L) ℂ).comp _ hinj
  apply LinearIndependent.of_comp (coeLin L)
  exact h1

theorem finrank_lin : Module.finrank ℂ (𝓞 L →ₗ[ℤ] ℂ) = Fintype.card (L →+* ℂ) := by
  rw [Module.finrank_linearMap_self, NumberField.RingOfIntegers.rank, NumberField.Embeddings.card]

theorem emb_span (α : 𝓞 L →+ ℝ) :
    ∃ c : (L →+* ℂ) → ℂ, ∀ x : 𝓞 L, (α x : ℂ) = ∑ σ, c σ * σ (algebraMap (𝓞 L) L x) := by
  have hspan := (embLin_linIndep L).span_eq_top_of_card_eq_finrank' (finrank_lin L).symm
  let f : 𝓞 L →ₗ[ℤ] ℂ := ((Complex.ofRealHom : ℝ →+* ℂ).toAddMonoidHom.comp α).toIntLinearMap
  have hf : f ∈ Submodule.span ℂ (Set.range (embLin L)) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  refine ⟨c, fun x => ?_⟩
  have hx := LinearMap.congr_fun hc x
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hx
  exact hx.symm

theorem mat_span (n r : ℕ) (α : Additive (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L))) →+ ℝ) :
    ∃ c : Fin n × Fin r × (L →+* ℂ) → ℂ, ∀ x,
      (α x : ℂ) = ∑ j, c j * j.2.2 (algebraMap (𝓞 L) L
        (Multiplicative.toAdd (Additive.toMul x) j.1 j.2.1)) := by
  let e : Matrix (Fin n) (Fin r) (𝓞 L) →+ Additive (Multiplicative (Matrix (Fin n) (Fin r) (𝓞 L))) :=
    { toFun := fun m => Additive.ofMul (Multiplicative.ofAdd m)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hc : ∀ i j, ∃ c : (L →+* ℂ) → ℂ, ∀ y : 𝓞 L,
      ((α.comp (e.comp (Matrix.singleAddMonoidHom i j))) y : ℂ) =
        ∑ σ, c σ * σ (algebraMap (𝓞 L) L y) :=
    fun i j => emb_span L _
  choose c hc using hc
  refine ⟨fun j => c j.1 j.2.1 j.2.2, fun x => ?_⟩
  have lhs : (α x : ℂ) = ∑ i, ∑ j, ((α.comp (e.comp (Matrix.singleAddMonoidHom i j)))
      (Multiplicative.toAdd (Additive.toMul x) i j) : ℂ) := by
    have hx : x = e (Multiplicative.toAdd (Additive.toMul x)) := rfl
    conv_lhs => rw [hx, Matrix.matrix_eq_sum_single (Multiplicative.toAdd (Additive.toMul x))]
    simp only [map_sum, Complex.ofReal_sum]
    rfl
  rw [lhs]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact hc i j _

end PositivityTheory.KB.SplitAffineSpectral.EigenLocalizationShapes
