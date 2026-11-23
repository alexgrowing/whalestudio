import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpanImageDenominators
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem UpperTheory.V.Pa.Det.exists_ne_zero_smul_mem_span_image {A F M N : Type} [CommRing A] [IsDomain A] [Field F] [Algebra A F]
    [IsFractionRing A F] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module F N]
    [IsScalarTower A F N] (φ : M →ₗ[A] N) (T : Set M) (y : N)
    (hy : y ∈ Submodule.span F (φ '' T)) :
    ∃ d : A, d ≠ 0 ∧ ∃ w ∈ Submodule.span A T, d • y = φ w :=
  _root_.UpperTheory.Reformulated.B.SpanImageDenominators.exists_ne_zero_smul_mem_span_image φ T y hy

theorem UpperTheory.V.Pa.Det.spanInt :
    ∀ {K ι : Type} [Field K] {n a : ℕ} (r : ι → Matrix (Fin n) (Fin n) (PowerSeries K)) (S : Set ι), Submodule.span (FractionRing (PowerSeries K)) ((fun i => (r i).map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) '' S) = Ev (FractionRing (PowerSeries K)) (FractionRing (PowerSeries K)) n a → ∀ Z ∈ Ev (PowerSeries K) (PowerSeries K) n a, ∃ s : ℕ, (PowerSeries.X : PowerSeries K) ^ s • Z ∈ Submodule.span (PowerSeries K) (r '' S) := by
  intro K ι _ n a r S h Z hZ
  let φ : Matrix (Fin n) (Fin n) (PowerSeries K) →ₗ[PowerSeries K]
      Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K)) :=
    (Algebra.linearMap (PowerSeries K) (FractionRing (PowerSeries K))).mapMatrix
  have hφ : ∀ Y, φ Y = Y.map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K))) := fun _ => rfl
  have hinj : Function.Injective φ :=
    Matrix.map_injective (IsFractionRing.injective (PowerSeries K) (FractionRing (PowerSeries K)))
  have hmem : φ Z ∈ Submodule.span (FractionRing (PowerSeries K)) (φ '' (r '' S)) := by
    rw [Set.image_image]
    simp only [hφ]
    rw [h]
    intro i j
    refine ⟨fun _ => Submodule.mem_top, fun hij => ?_⟩
    have : Z i j = 0 := (Submodule.mem_bot _).1 ((hZ i j).2 hij)
    simp [this]
  obtain ⟨d, hd, w, hw, e⟩ := UpperTheory.V.Pa.Det.exists_ne_zero_smul_mem_span_image φ _ _ hmem
  rw [← map_smul] at e
  have e' := hinj e
  obtain ⟨s, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd
    (PowerSeries.X_irreducible (R := K))
  refine ⟨s, ?_⟩
  have : (PowerSeries.X : PowerSeries K) ^ s • Z = (↑u⁻¹ : PowerSeries K) • w := by
    rw [← e', smul_smul, Units.inv_mul_cancel_left]
  rw [this]
  exact Submodule.smul_mem _ _ hw
