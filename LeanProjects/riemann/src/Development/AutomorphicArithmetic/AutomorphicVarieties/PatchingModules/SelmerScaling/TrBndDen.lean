import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.TrLatRange
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem trBnd_den {K : Type} [Field K] (Q : Submodule (PowerSeries K) (FractionRing (PowerSeries K)))
    (hQ : Q.FG) : ∃ s : ℕ, ∀ z ∈ Q, ∃ a : PowerSeries K,
      algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) a =
        algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) PowerSeries.X ^ s * z := by
  obtain ⟨T, rfl⟩ := hQ
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (PowerSeries K)) T
  have hb0 : (b : PowerSeries K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  obtain ⟨s, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 PowerSeries.X_irreducible
  refine ⟨s, fun z hz => ?_⟩
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, ha⟩ := hb z hz
    refine ⟨(u⁻¹ : (PowerSeries K)ˣ) * a, ?_⟩
    rw [map_mul, ha, Algebra.smul_def, hu, ← mul_assoc, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul, map_pow]
  | zero => exact ⟨0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨c, hc⟩ := hz
    exact ⟨a + c, by rw [map_add, ha, hc, mul_add]⟩
  | smul c z _ hz =>
    obtain ⟨a, ha⟩ := hz
    exact ⟨c * a, by rw [map_mul, ha, Algebra.smul_def]; ring⟩

theorem UpperTheory.V.Pa.trBnd :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ (R : Type) [CommRing R] [Algebra S.F R] (e : R →ₐ[S.F] S.F) (θ : S.U.AA →+* R), S.Test R e θ → ∀ (lam : R →ₗ[S.F] S.F) (i j : Fin S.n), BndF S.x.t fun g : S.G.G₀ => lam (θ (S.U.vr g i j)) := by
  intro l _ S R _ _ e θ hT lam i j
  letI : Algebra S.x.A R := ((algebraMap S.F R).comp (algebraMap S.x.A S.F)).toAlgebra
  haveI : IsScalarTower S.x.A S.F R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨M, -, -, -, hM, P, hP, hPm, hMP⟩ := trLat l S R e θ hT
  obtain ⟨s, hs⟩ := trBnd_den (P.map (lam.restrictScalars S.x.A)) (hP.map _)
  have hs' : ∀ z ∈ P, ∃ a : S.x.A, algebraMap S.x.A S.F a = algebraMap S.x.A S.F S.x.t ^ s * lam z :=
    fun z hz => hs _ (Submodule.mem_map_of_mem hz)
  choose φ hφ using fun g : S.G.G₀ => hs' _ (hPm _ (S.U.vr_mem g) i j)
  refine ⟨s, φ, fun N => ?_, hφ⟩
  obtain ⟨j', hj'⟩ := hM N
  obtain ⟨V, hV⟩ := S.U.cont j'
  have key : ∀ q ∈ maximalIdeal S.B ^ j' • S.U.P, ∃ z ∈ P, θ (q i j) = S.x.t ^ N • z := by
    intro q hq
    refine Submodule.smul_induction_on hq ?_ ?_
    · intro b hb p hp
      obtain ⟨y, hy, hby⟩ := hj' b hb
      refine ⟨y * θ (p i j), hMP y hy _ (hPm p hp i j), ?_⟩
      rw [Matrix.smul_apply, Algebra.smul_def, map_mul, hby, smul_mul_assoc]
    · rintro a b ⟨z, hz, ha⟩ ⟨w, hw, hb⟩
      exact ⟨z + w, P.add_mem hz hw, by rw [Matrix.add_apply, map_add, ha, hb, smul_add]⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨{y | g⁻¹ * y ∈ V}, V.toOpenSubgroup.isOpen.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp only [Set.mem_setOf_eq, inv_mul_cancel]
    exact one_mem V
  · intro y hy
    obtain ⟨z, hz, hq⟩ := key _ (hV g _ hy)
    rw [mul_inv_cancel_left, Matrix.sub_apply, map_sub] at hq
    obtain ⟨a, ha⟩ := hs' z hz
    rw [Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    refine ⟨a, IsFractionRing.injective S.x.A S.F ?_⟩
    rw [map_sub, hφ, hφ, ← mul_sub, ← map_sub, hq, LinearMap.map_smul_of_tower, map_mul, ha, Algebra.smul_def]
    ring
