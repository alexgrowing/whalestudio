import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerPow
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemSpanVariable

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem mem_span_X {O σ : Type} [CommRing O] [Fintype σ] (f : MvPowerSeries σ O)
    (hf : constantCoeff f = 0) : f ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)) :=
  _root_.UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X f hf

private theorem der_algebraMap {O A Q : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup Q]
    [Module O Q] (x : A →ₐ[O] O) (D : A →ₗ[O] Q) (hD : D ∈ PtDer x Q) (c : O) : D (algebraMap O A c) = 0 := by
  have h1 : D 1 = 0 := by
    have h : D (1 * 1) = x 1 • D 1 + x 1 • D 1 := hD 1 1
    rw [mul_one, map_one x, one_smul] at h
    simpa using h
  rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]

private theorem der_sq {O A Q : Type} [CommRing O] [CommRing A] [Algebra O A] [AddCommGroup Q]
    [Module O Q] (x : A →ₐ[O] O) (D : A →ₗ[O] Q) (hD : D ∈ PtDer x Q) (f : A) (hf : f ∈ RingHom.ker x ^ 2) :
    D f = 0 := by
  rw [pow_two] at hf
  refine Submodule.mul_induction_on hf (fun a ha b hb => ?_) (fun a b ha hb => by rw [map_add, ha, hb, add_zero])
  have h : D (a * b) = x a • D b + x b • D a := hD a b
  rw [h, (RingHom.mem_ker).1 ha, (RingHom.mem_ker).1 hb, zero_smul, zero_smul, add_zero]

theorem UpperTheory.V.Alg.der_extend :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [DecidableEq X] (W : WPres O X R) (h : W.HasOrigin) (Q : Type) [AddCommGroup Q] [Module O Q],
      (∀ D ∈ PtDer (W.originA h) Q, ∃! D' : R →ₗ[O] Q, D' ∈ PtDer (W.origin h) Q ∧ D' ∘ₗ W.A.val.toLinearMap = D) ∧
      ∀ D ∈ PtDer (W.origin h) Q, (∀ s, D (W.z s) = 0) → D = 0 := by
  intro O R _ _ _ X _ _ _ _ W h Q _ _
  obtain ⟨hk, hy⟩ := UpperTheory.V.Alg.ker_pow O R X W h 2
  choose y hy using hy
  refine ⟨fun D hD => ?_, fun D hD hz => ?_⟩
  · have key : ∀ (x : R) (a : W.A), x - a ∈ RingHom.ker (W.origin h) ^ 2 → D (y x) = D a := fun x a ha => by
      rw [← sub_eq_zero, ← map_sub]
      refine der_sq _ D hD _ ?_
      rw [← hk, Ideal.mem_comap]
      have := sub_mem ha (hy x)
      convert this using 1
      simp
    have horig : ∀ x : R, W.origin h x = W.originA h (y x) := fun x => by
      have h1 : x - y x ∈ RingHom.ker (W.origin h) := Ideal.pow_le_self two_ne_zero (hy x)
      rw [RingHom.mem_ker, map_sub, sub_eq_zero] at h1
      exact h1
    let D' : R →ₗ[O] Q :=
      { toFun := fun x => D (y x)
        map_add' := fun a b => by
          rw [← map_add]
          refine key _ _ ?_
          have := add_mem (hy a) (hy b)
          convert this using 1
          push_cast
          ring
        map_smul' := fun c a => by
          rw [RingHom.id_apply, ← map_smul]
          refine key _ _ ?_
          have := Submodule.smul_of_tower_mem _ c (hy a)
          convert this using 1
          rw [smul_sub]
          rfl }
    refine ⟨D', ⟨fun a b => ?_, ?_⟩, ?_⟩
    · have h1 : D (y a * y b) = W.originA h (y a) • D (y b) + W.originA h (y b) • D (y a) := hD _ _
      show D (y (a * b)) = W.origin h a • D (y b) + W.origin h b • D (y a)
      rw [horig a, horig b, ← h1]
      refine key _ _ ?_
      have := add_mem (Ideal.mul_mem_right b _ (hy a)) (Ideal.mul_mem_left _ (y a : R) (hy b))
      convert this using 1
      push_cast
      ring
    · ext a
      exact key _ a (by simp)
    · rintro E ⟨hE, rfl⟩
      ext x
      have := der_sq _ E hE _ (hy x)
      rw [map_sub, sub_eq_zero] at this
      exact this
  · ext x
    obtain ⟨f, rfl⟩ := W.surj x
    have hspan : ∀ g ∈ Ideal.span (Set.range (MvPowerSeries.X : W.σ → MvPowerSeries W.σ O)),
        D (W.π g) = 0 := fun g hg => by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hg
      rw [map_sum, map_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      have h1 : D (W.π (c i) * W.z i) = W.origin h (W.π (c i)) • D (W.z i) + W.origin h (W.z i) • D (W.π (c i)) :=
        hD _ _
      have h2 : W.origin h (W.z i) = 0 := by
        rw [WPres.z, W.origin_π]
        simp
      rw [map_mul]
      rw [hz i, h2, smul_zero, zero_smul, add_zero] at h1
      exact h1
    have h1 := hspan (f - algebraMap O _ (constantCoeff f))
      (mem_span_X _ (by simp [MvPowerSeries.algebraMap_apply]))
    rw [map_sub, AlgHom.commutes, map_sub, der_algebraMap _ D hD, sub_zero] at h1
    exact h1
