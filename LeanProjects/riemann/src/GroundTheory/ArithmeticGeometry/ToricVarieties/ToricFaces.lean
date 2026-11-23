import Mathlib
import GroundTheory.ArithmeticGeometry.ToricVarieties.IsFaceOfIffExistsEqExposedFace
import GroundTheory.ArithmeticGeometry.ToricVarieties.Lattice

namespace GroundTheory.Arith.Toric

open Module PointedCone TensorProduct

theorem IsRationalPolyhedral.of_isFaceOf {L E : Type*} [AddCommGroup L] [AddCommGroup E]
    [Module ℝ E] {ι : L →ₗ[ℤ] E} {σ τ : PointedCone ℝ E} (hσ : IsRationalPolyhedral ι σ)
    (hτ : τ.IsFaceOf σ) : IsRationalPolyhedral ι τ := by
  classical
  obtain ⟨S, rfl⟩ := hσ
  have hτ' : τ.IsFaceOf (hull ℝ ((S.image ι : Finset E) : Set E)) := by
    rwa [Finset.coe_image]
  refine ⟨S.filter (fun n => ι n ∈ τ), ?_⟩
  conv_rhs => rw [isFaceOf_eq_hull_filter _ hτ']
  congr 1
  ext y
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨hnS, hnτ⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hn)
    exact Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hnS, hnτ⟩)
  · intro hy
    obtain ⟨hy1, hy2⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 hy)
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hy1
    exact ⟨n, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hn, hy2⟩), rfl⟩

variable {N : Type*} [AddCommGroup N]

theorem toRealDual_injective : Function.Injective (toRealDual N) := by
  intro m m' h
  refine LinearMap.ext fun n => ?_
  have := congrArg (fun f => f (toRealSpan N n)) h
  simp only [toRealDual_apply_toRealSpan] at this
  exact_mod_cast this

theorem dualMonoid_anti {σ₁ σ₂ : PointedCone ℝ (ℝ ⊗[ℤ] N)} (h : σ₁ ≤ σ₂) :
    dualMonoid σ₂ ≤ dualMonoid σ₁ :=
  fun _ hm => mem_dualMonoid.2 fun x hx => mem_dualMonoid.1 hm x (h hx)

variable [Module.Free ℤ N] [Module.Finite ℤ N]

theorem exists_separating_rational {σ σ' : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) (hσ' : IsRationalPolyhedral (toRealSpan N) σ')
    (h : (σ ⊓ σ').IsFaceOf σ) (h' : (σ ⊓ σ').IsFaceOf σ') :
    ∃ u : Dual ℤ N, u ∈ dualMonoid σ ∧ -u ∈ dualMonoid σ' ∧
      exposedFace σ (toRealDual N u) = σ ⊓ σ' ∧ exposedFace σ' (toRealDual N u) = σ ⊓ σ' := by
  classical
  obtain ⟨S, rfl⟩ := hσ
  obtain ⟨S', rfl⟩ := hσ'
  obtain ⟨TM, hTM⟩ := (show IsRationalPolyhedral (toRealSpan N)
    (hull ℝ (toRealSpan N '' ↑(S ∪ S'.image Neg.neg))) from ⟨_, rfl⟩).dual
  rw [dual_hull] at hTM
  set SR := S.image (toRealSpan N) with hSR
  set SR' := S'.image (toRealSpan N) with hSR'
  have e1 : hull ℝ (toRealSpan N '' (S : Set N)) = hull ℝ (SR : Set (ℝ ⊗[ℤ] N)) := by
    rw [hSR, Finset.coe_image]
  have e2 : hull ℝ (toRealSpan N '' (S' : Set N)) = hull ℝ (SR' : Set (ℝ ⊗[ℤ] N)) := by
    rw [hSR', Finset.coe_image]
  rw [e1, e2] at h h' ⊢
  set TR := TM.image (toRealDual N) with hTR
  have hT : ∀ u : Dual ℝ (ℝ ⊗[ℤ] N), u ∈ hull ℝ (TR : Set (Dual ℝ (ℝ ⊗[ℤ] N))) ↔
      (∀ x ∈ hull ℝ (SR : Set (ℝ ⊗[ℤ] N)), 0 ≤ u x) ∧
        (∀ x ∈ hull ℝ (SR' : Set (ℝ ⊗[ℤ] N)), u x ≤ 0) := by
    intro u
    rw [hTR, Finset.coe_image, hTM]
    constructor
    · intro hu
      refine ⟨fun x hx => nonneg_of_mem_hull (fun y hy => ?_) hx, fun x hx => ?_⟩
      · obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
        simpa using hu ⟨n, by simp [hn], rfl⟩
      · have := nonneg_of_mem_hull (f := -u) (s := (SR' : Set (ℝ ⊗[ℤ] N))) (fun y hy => by
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
          simpa using hu ⟨-n, by simp [hn], rfl⟩) hx
        simpa using this
    · rintro ⟨h1, h2⟩ y ⟨n, hn, rfl⟩
      simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Finset.mem_coe,
        Set.mem_image] at hn
      rcases hn with hn | ⟨n', hn', rfl⟩
      · simpa using h1 _ (subset_hull (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hn)))
      · simpa using h2 _ (subset_hull (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hn')))
  obtain ⟨hu1, hu2, hE1, hE2⟩ := separation_of_generators SR SR' TR hT h h'
  have hsum : (∑ t ∈ TR, t) = toRealDual N (∑ t ∈ TM, t) := by
    rw [hTR, Finset.sum_image (fun x _ y _ hxy => toRealDual_injective hxy), map_sum]
  rw [hsum] at hu1 hu2 hE1 hE2
  exact ⟨∑ t ∈ TM, t, mem_dualMonoid.2 hu1, mem_dualMonoid.2 fun x hx => by simpa using hu2 x hx,
    hE1, hE2⟩

theorem exists_mem_dualMonoid_eq_exposedFace {σ τ : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) (hτ : τ.IsFaceOf σ) :
    ∃ u ∈ dualMonoid σ, τ = exposedFace σ (toRealDual N u) := by
  have hστ : σ ⊓ τ = τ := inf_eq_right.2 hτ.le
  obtain ⟨u, hu, -, hE, -⟩ := exists_separating_rational hσ (hσ.of_isFaceOf hτ)
    (by rw [hστ]; exact hτ) (by rw [hστ])
  exact ⟨u, hu, by rw [hE, hστ]⟩

omit [Module.Free ℤ N] [Module.Finite ℤ N] in

theorem dualMonoid_exposedFace {σ : PointedCone ℝ (ℝ ⊗[ℤ] N)}
    (hσ : IsRationalPolyhedral (toRealSpan N) σ) {u : Dual ℤ N} (hu : u ∈ dualMonoid σ) :
    dualMonoid (exposedFace σ (toRealDual N u)) = dualMonoid σ ⊔ AddSubmonoid.closure {-u} := by
  classical
  obtain ⟨S, rfl⟩ := hσ
  rw [← Finset.coe_image] at hu ⊢
  apply le_antisymm
  · intro m hm
    obtain ⟨p, -, hp⟩ := exists_add_smul_mem_dual (S.image (toRealSpan N))
      (u := toRealDual N u) (w := toRealDual N m) (mem_dualMonoid.1 hu) (mem_dualMonoid.1 hm)
    have hk : p ≤ ((⌈p⌉₊ : ℕ) : ℝ) := Nat.le_ceil p
    rw [AddSubmonoid.mem_sup]
    refine ⟨m + ⌈p⌉₊ • u, mem_dualMonoid.2 fun x hx => ?_, ⌈p⌉₊ • (-u),
      AddSubmonoid.nsmul_mem _ (AddSubmonoid.subset_closure (Set.mem_singleton _)) _,
      by rw [smul_neg, add_neg_cancel_right]⟩
    have := hp _ hk x hx
    rw [map_add, map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
    exact this
  · refine sup_le (dualMonoid_anti fun x hx => (mem_exposedFace.1 hx).1) ?_
    rw [AddSubmonoid.closure_le, Set.singleton_subset_iff]
    exact mem_dualMonoid.2 fun x hx => by simp [(mem_exposedFace.1 hx).2]

end GroundTheory.Arith.Toric
