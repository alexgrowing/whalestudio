import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.MemSatSqIffConstantCoeffAndLinearCoeffEqZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AbsDefs
open IsLocalRing MvPowerSeries UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia.Abs

theorem UpperTheory.smoothPt_weightedGradedAlgebra_basePoint :
    ∀ (O : Type) [CommRing O] [IsDomain O] (σ : Type) [Fintype σ] (wt : σ → ℤ),
        SmoothPt (Fgr O wt) (x0 O wt) (fun j => Nat.card {i // wt i = j}) := by
  intro O _ _ σ hσ wt
  classical
  have hinj : Function.Injective (algebraMap O (FractionRing O)) := IsFractionRing.injective O _
  let φ : FA O wt →ₐ[O] MvPowerSeries σ (FractionRing O) :=
    (MvPowerSeries.mapAlgHom (Algebra.ofId O (FractionRing O))).comp (WPres.free O wt).A.val
  have hφ : ∀ (f : FA O wt) (d : σ →₀ ℕ),
      coeff d (φ f) = algebraMap O (FractionRing O) (coeff d (ser f)) := fun f d => rfl
  refine ⟨σ, hσ, wt, φ, ⟨?_, ?_, ?_, ?_⟩, fun j => rfl⟩
  · intro j f hf d hd
    rw [hφ, mem_Fgr.1 hf d hd, map_zero]
  · intro f
    rw [weightedSeriesOrigin_apply]
    exact hφ f 0
  · intro i
    have hz : ser ((WPres.free O wt).zA i) = MvPowerSeries.X i := rfl
    refine ⟨(WPres.free O wt).zA i, ?_, fun i' hi => ?_⟩
    · rw [hφ, hz, coeff_index_single_self_X, map_one]
      exact one_ne_zero
    · rw [hφ, hz, coeff_index_single_X, if_neg hi, map_zero]
  · intro f h0 h1
    refine (UpperTheory.mem_satSq_iff_constantCoeff_and_linearCoeff_eq_zero O σ wt f).2 ⟨by rw [← weightedSeriesOrigin_apply, h0], fun i => hinj ?_⟩
    rw [← hφ, h1, map_zero]
