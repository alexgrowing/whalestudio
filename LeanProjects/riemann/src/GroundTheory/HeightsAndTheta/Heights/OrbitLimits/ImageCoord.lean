import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem ImageCoord.mConeMap_rename {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (hv : ∀ p, (v p).1 = κ p.1)
    {Ω : Type} [Field Ω] (y : (Σ k', ι' k') → Ω) (f : MRing ι) :
    mConeMap y (rename v f) = rename κ (mConeMap (y ∘ v) f) := by
  have h : ((mConeMap y).comp (rename v : MRing ι →ₐ[ℤ] MRing ι')) =
      ((rename κ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K' Ω).restrictScalars ℤ).comp
        (mConeMap (y ∘ v)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap, hv p]
  exact congrArg (fun φ => φ f) h

theorem ImageCoord.proof : ImageCoordStatement := by
  intro K _ ι _ K' _ ι' _ κ v Ω _ y hB
  obtain ⟨hκ, -, hv, -⟩ := hB
  ext f
  simp only [imageZ, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, ImageCoord.mConeMap_rename κ v hv y f]
  constructor
  · intro h
    exact rename_injective κ hκ (by rw [h, map_zero])
  · intro h
    rw [h, map_zero]

end GroundTheory.Heights₂.Heights.Targets
