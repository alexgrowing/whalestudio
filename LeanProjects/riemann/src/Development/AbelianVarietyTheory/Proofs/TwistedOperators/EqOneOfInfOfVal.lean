import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits

open NumberField IsDedekindDomain NumberField.mixedEmbedding Classical
open scoped ContDiff
open Formalism.L2.Host (HChar)

namespace GlobalTheory.HeckeUnrTrivial

theorem eq_one_of_val_eq_one {K : Type} [Field K] [NumberField K] (χ : HChar K)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), χ.UnrAt v → χ.val v = 1) : χ = 1 := by
  refine Subtype.ext (GlobalTheory.FrobDense.eq_one_of_away χ.1 χ.2.1 χ.2.2
    (GlobalTheory.Mem.UnrAe.finite_ramified χ).toFinset fun v hv => ?_)
  have hu : χ.UnrAt v := by simpa using hv
  exact GlobalTheory.FrobDense.eq_one_of_unif (χ.loc v) fun x hx => (χ.val_eq hu x hx).trans (h v hu)

theorem eq_one_of_inf_of_val : ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K), (∀ k : Kˣ, χ.inf k = 1) → (∀ v : HeightOneSpectrum (𝓞 K), χ.UnrAt v → χ.val v = 1) → χ = 1 :=
  fun _ _ _ χ _ h => eq_one_of_val_eq_one χ h

end GlobalTheory.HeckeUnrTrivial
