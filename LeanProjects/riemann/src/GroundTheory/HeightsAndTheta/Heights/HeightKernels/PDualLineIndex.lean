import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.IsArithVarBotDualBlocksUnit
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PLineIdealDual
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIdealIndexPlaces
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.POneBlockPoints
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField Matrix

noncomputable section

namespace DualLineIndexAlt

theorem genIndex_span_eq_finprod {L : Type*} [Field L] [NumberField L] {ι : Type*} [Fintype ι] {y : ι → L}
    (hy : y ≠ 0) :
    genIndex (Submodule.span (𝓞 L) (Set.range y)).toAddSubgroup (1 : Submodule (𝓞 L) L).toAddSubgroup =
      ∏ᶠ w : FinitePlace L, ⨆ i, w (y i) := by
  obtain ⟨⟨b, hb⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 L)) y
  choose z hz using hint
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbL : (b : L) ≠ 0 := by rwa [Ne, RingOfIntegers.coe_eq_zero_iff]
  have hzy : ∀ i, ((z i : 𝓞 L) : L) = (b : L) * y i := fun i ↦ by
    have h := hz i
    simp only [Algebra.smul_def] at h
    exact h
  let g : 𝓞 L →ₗ[𝓞 L] L :=
    (LinearMap.mulLeft (𝓞 L) ((b : L)⁻¹)).comp (Algebra.linearMap (𝓞 L) L)
  have hg : ∀ t, g t = (b : L)⁻¹ * t := fun t ↦ rfl
  have hginj : Function.Injective g := fun s t h ↦ by
    rw [hg, hg] at h
    exact RingOfIntegers.ext (mul_left_cancel₀ (inv_ne_zero hbL) h)
  set J : Ideal (𝓞 L) := Ideal.span (Set.range z) with hJdef
  have hS : Submodule.span (𝓞 L) (Set.range y) = Submodule.map g J := by
    rw [hJdef]
    change _ = Submodule.map g (Submodule.span (𝓞 L) _)
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i
    rw [Function.comp_apply, hg, hzy]
    field_simp
  have h1 : (1 : Submodule (𝓞 L) L) = Submodule.map g (Ideal.span {b}) := by
    change _ = Submodule.map g (Submodule.span (𝓞 L) _)
    rw [Submodule.map_span, Set.image_singleton, hg, inv_mul_cancel₀ hbL,
      Submodule.one_eq_span]
  have hmap : ∀ A : Ideal (𝓞 L), (Submodule.map g A).toAddSubgroup = A.toAddSubgroup.map g.toAddMonoidHom :=
    fun _ ↦ rfl
  have hz0 : z ≠ 0 := by
    intro h
    apply hy
    funext i
    have := hzy i
    rw [h, Pi.zero_apply] at this
    exact (mul_eq_zero.mp (by rw [← this]; rfl)).resolve_left hbL
  have hJ0 : J ≠ ⊥ := by
    obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hz0
    intro h
    exact hi0 ((Ideal.span_eq_bot.mp h) _ ⟨i0, rfl⟩)
  have hB0 : Ideal.span {b} ≠ ⊥ := by rw [Ne, Ideal.span_singleton_eq_bot]; exact hb0
  rw [hS, h1, hmap, hmap, genIndex, AddSubgroup.relIndex_map_map_of_injective _ _ hginj,
    AddSubgroup.relIndex_map_map_of_injective _ _ hginj, ← genIndex,
    IdealIndexPlaces.genIndex_ideal hJ0 hB0, Ideal.absNorm_span_singleton, Nat.cast_natAbs]

  have hprodz := absNorm_mul_finprod_finitePlace_eq_one hz0
  have hsup : ∀ w : FinitePlace L, ⨆ i, w (z i : L) = w (b : L) * ⨆ i, w (y i) := by
    intro w
    simp_rw [hzy, map_mul]
    exact (Real.mul_iSup_of_nonneg (apply_nonneg w _) _).symm
  simp_rw [hsup] at hprodz
  rw [finprod_mul_distrib (FinitePlace.hasFiniteMulSupport hbL) (hasFiniteMulSupport_iSup_place hy),
    FinitePlace.prod_eq_inv_abs_norm_int hb0] at hprodz
  rw [← hJdef] at hprodz
  set P := ∏ᶠ w : FinitePlace L, ⨆ i, w (y i)
  have hbn : |((Algebra.norm ℤ b : ℤ) : ℝ)| ≠ 0 := by
    rw [abs_ne_zero, Int.cast_ne_zero, Ne, Algebra.norm_eq_zero_iff]; exact hb0
  have hJn : (J.absNorm : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ0)
  have hinv := mul_inv_cancel₀ hbn
  push_cast
  rw [div_eq_iff hJn]
  linear_combination (-|((Algebra.norm ℤ b : ℤ) : ℝ)|) * hprodz + ((J.absNorm : ℝ) * P) * hinv

theorem dualPointCoord_ne_zero {K : Type} [Field K] [NumberField K] {i : ℕ} (F : HermLattice K i) {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) {K' : Type} [Field K'] [Algebra K K'] {v : Fin i → K'}
    (hv : v ≠ 0) : dualPointCoord b v ≠ 0 := by
  classical
  intro h0
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  obtain ⟨D, hD, hmem⟩ := exists_int_smul_mem_latticeDual F.lattice F.fg (Pi.single j (1 : K))
  have hmem' : D • (Pi.single j (1 : K) : Fin i → K) ∈ dualLattice F := fun x hx ↦ by
    obtain ⟨c, hc⟩ := hmem x hx
    exact ⟨c, hc⟩
  let Λ : dualLattice F →ₗ[ℤ] K' :=
    { toFun := fun ψ ↦ ∑ k, algebraMap K K' ((ψ : Fin i → K) k) * v k
      map_add' := fun ψ χ ↦ by
        simp only [Submodule.coe_add, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c ψ ↦ by
        simp only [Submodule.coe_smul, Pi.smul_apply, zsmul_eq_mul, map_mul, map_intCast,
          RingHom.id_apply, Finset.mul_sum, mul_assoc] }
  have hΛ : Λ = 0 := b.ext fun t ↦ by
    have := congrFun h0 ⟨(), t⟩
    simpa [Λ, dualPointCoord] using this
  have := congrArg (fun f : dualLattice F →ₗ[ℤ] K' ↦ f ⟨_, hmem'⟩) hΛ
  simp only [Λ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply,
    zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply, Pi.single_apply, mul_ite, mul_one, mul_zero,
    apply_ite (algebraMap K K'), map_intCast, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at this
  rcases mul_eq_zero.mp this with h | h
  · apply hD
    have h' : algebraMap K K' (D : K) = 0 := by rw [map_intCast]; exact h
    exact_mod_cast (map_eq_zero_iff _ (algebraMap K K').injective).mp h'
  · exact hj h

end DualLineIndexAlt

open DualLineIndexAlt in

theorem DualLineIndex.proof : DualLineIndex.Statement := by
  intro K _ _ i F T _ _ b K' _ _ _ v hv
  classical
  have hi : i ≠ 0 := by
    rintro rfl
    exact hv (Subsingleton.elim _ _)
  obtain ⟨r, rfl⟩ : ∃ r, i = r + 1 := ⟨i - 1, by omega⟩
  set y := dualPointCoord b v with hy
  have hy0 : y ≠ 0 := dualPointCoord_ne_zero F b hv
  have hT : Fintype.card T ≠ 0 := by
    obtain ⟨p, _⟩ := Function.ne_iff.mp hy0
    exact (Fintype.card_pos_iff.mpr ⟨p.2⟩).ne'
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card T = N + 1 := ⟨Fintype.card T - 1, by omega⟩
  let e : T ≃ Fin (N + 1) := Fintype.equivFinOfCardEq hN
  let φ : Fin (N + 1) → Fin (r + 1) → K := fun k ↦ (b (e.symm k) : Fin (r + 1) → K)
  have hφ : IsDualBasis F.lattice φ :=
    { independent :=
        (b.linearIndependent.map' (dualLattice F).subtype (Submodule.ker_subtype _)).comp e.symm
          e.symm.injective
      span_eq := by
        have hr : Set.range φ = (dualLattice F).subtype '' Set.range b := by
          rw [← Set.range_comp]
          exact EquivLike.range_comp (fun t ↦ (b t : Fin (r + 1) → K)) e.symm
        rw [hr, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
        ext ψ
        exact ⟨fun h x hx ↦ by obtain ⟨c, hc⟩ := h x hx; exact ⟨c, hc⟩,
          fun h x hx ↦ by obtain ⟨c, hc⟩ := h x hx; exact ⟨c, hc⟩⟩ }

  have hval : ∀ a : K', (∀ k, a * latticeValue φ v k ∈ Set.range (algebraMap (𝓞 K') K')) ↔
      a ∈ multiplierIdeal y := by
    intro a
    constructor
    · rintro h ⟨⟨⟩, t⟩
      have := h (e t)
      simpa [φ, latticeValue, hy, dualPointCoord] using this
    · intro h k
      exact h ⟨(), e.symm k⟩

  let f : K' →+ (Fin (r + 1) → K') :=
    { toFun := fun a ↦ a • v, map_zero' := zero_smul _ _, map_add' := fun a a' ↦ add_smul a a' v }
  have hf : Function.Injective f := smul_left_injective K' hv
  have e1 : (Submodule.span (𝓞 K')
        ((fun w : Fin (r + 1) → K ↦ fun j ↦ algebraMap K K' (w j)) '' F.lattice) ⊓
        (Submodule.span K' (Set.range fun _ : Fin 1 ↦ v)).restrictScalars (𝓞 K')).toAddSubgroup =
      (multiplierIdeal y).toAddSubgroup.map f := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, Submodule.mem_inf, Submodule.restrictScalars_mem,
      Set.range_const, Submodule.mem_span_singleton, AddSubgroup.mem_map]
    constructor
    · rintro ⟨hxL, a, rfl⟩
      exact ⟨a, (hval a).mp ((LineIdealDual.proof K r N F φ hφ K' v a).mp hxL), rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨(LineIdealDual.proof K r N F φ hφ K' v a).mpr ((hval a).mpr ha), a, rfl⟩
  have e2 : (Submodule.span (𝓞 K') (Set.range fun _ : Fin 1 ↦ v)).toAddSubgroup =
      (1 : Submodule (𝓞 K') K').toAddSubgroup.map f := by
    ext x
    simp only [Submodule.mem_toAddSubgroup, Set.range_const, Submodule.mem_span_singleton,
      AddSubgroup.mem_map, Submodule.mem_one]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨algebraMap (𝓞 K') K' c, ⟨c, rfl⟩, (algebraMap_smul K' c v)⟩
    · rintro ⟨a, ⟨c, rfl⟩, rfl⟩
      exact ⟨c, (algebraMap_smul K' c v).symm⟩
  rw [e1, e2, genIndex, AddSubgroup.relIndex_map_map_of_injective _ _ hf,
    AddSubgroup.relIndex_map_map_of_injective _ _ hf, ← genIndex, genIndex_span_eq_finprod hy0]
  exact IdealIndexPlaces.proof K' _ y hy0

end

end GroundTheory.Heights₂.Heights
