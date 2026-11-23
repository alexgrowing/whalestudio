import Mathlib
import GroundTheory.GlobalFields.KummerTheory.Degree
import GroundTheory.GlobalFields.KummerTheory.Splitting
import GroundTheory.GlobalFields.KummerTheory.SplittingInfinite

noncomputable section

namespace GroundTheory.Global

open IsDedekindDomain NumberField Module IntermediateField GroundTheory.ProfCoh
open scoped TensorProduct

section Local

variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
  {Ω : Type*} [Field Ω] [Algebra K Ω] {Δ : Subgroup Kˣ}
  {F E : Type*} [Field F] [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
  [IsScalarTower K F E]

omit [NeZero n] [HasEnoughRootsOfUnity K n] [IsScalarTower K F E] in

theorem kummerExtension_pow_eq {y : kummerExtension K n Ω Δ} {a : K}
    (hy : (y : Ω) ^ n = algebraMap K Ω a) :
    y ^ n = algebraMap K (kummerExtension K n Ω Δ) a :=
  Subtype.ext (by rw [IntermediateField.coe_pow, hy]; rfl)

theorem algHom_kummerExtension_mem_fieldRange (ι : kummerExtension K n Ω Δ →ₐ[K] E)
    (h : ∀ a ∈ Δ, ∃ x : F, x ^ n = algebraMap K F (a : K)) (m : kummerExtension K n Ω Δ) :
    ι m ∈ (algebraMap F E).fieldRange := by
  have key : ∀ (y : kummerExtension K n Ω Δ), ∀ a ∈ Δ, (y : Ω) ^ n = algebraMap K Ω (a : K) →
      ι y ∈ (algebraMap F E).fieldRange := by
    intro y a ha hy
    obtain ⟨x, hx⟩ := h a ha
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
    have hζ' : IsPrimitiveRoot (algebraMap K E ζ) n :=
      hζ.map_of_injective (algebraMap K E).injective
    have hx0 : algebraMap F E x ≠ 0 := by
      refine (map_ne_zero _).2 fun hx0 ↦ ?_
      rw [hx0, zero_pow (NeZero.ne n)] at hx
      exact a.ne_zero ((algebraMap K F).injective (by rw [← hx, map_zero]))
    have hpow : ι y ^ n = algebraMap F E x ^ n := by
      rw [← map_pow, kummerExtension_pow_eq hy, ι.commutes, ← map_pow, hx,
        ← IsScalarTower.algebraMap_apply]
    have hroot : (ι y / algebraMap F E x) ^ n = 1 := by
      rw [div_pow, hpow, div_self (pow_ne_zero _ hx0)]
    obtain ⟨k, -, hk⟩ := hζ'.eq_pow_of_pow_eq_one hroot
    refine ⟨algebraMap K F ζ ^ k * x, ?_⟩
    rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply, hk, div_mul_cancel₀ _ hx0]
  obtain ⟨m, hm⟩ := m
  induction hm using IntermediateField.adjoin_induction with
  | mem α hα =>
    obtain ⟨a, ha, hαa⟩ := id hα
    exact key _ a ha hαa
  | algebraMap x =>
    refine ⟨algebraMap K F x, ?_⟩
    rw [← IsScalarTower.algebraMap_apply]
    exact (ι.commutes x).symm
  | add x y hx hy ihx ihy =>
    show ι (⟨x, hx⟩ + ⟨y, hy⟩) ∈ _
    rw [map_add]
    exact add_mem ihx ihy
  | inv x hx ih =>
    show ι (⟨x, hx⟩⁻¹) ∈ _
    rw [map_inv₀]
    exact inv_mem ih
  | mul x y hx hy ihx ihy =>
    show ι (⟨x, hx⟩ * ⟨y, hy⟩) ∈ _
    rw [map_mul]
    exact mul_mem ihx ihy

omit [Algebra K E] [IsScalarTower K F E] in

theorem finrank_eq_one_of_tensor_surjective {A : Type*} [CommRing A] [Algebra K A]
    (g : F ⊗[K] A →ₐ[F] E) (hg : Function.Surjective g)
    (hA : ∀ m : A, g (1 ⊗ₜ m) ∈ (algebraMap F E).fieldRange) : finrank F E = 1 := by
  rw [← Subalgebra.bot_eq_top_iff_finrank_eq_one]
  refine eq_top_iff.2 fun e he ↦ ?_
  clear he
  obtain ⟨t, rfl⟩ := hg e
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul c m =>
    have : c ⊗ₜ[K] m = c • ((1 : F) ⊗ₜ[K] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Subalgebra.smul_mem _ (Algebra.mem_bot.2 (hA m)) c
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

theorem finrank_eq_one_iff_of_kummerExtension [IsSepClosed Ω]
    (g : F ⊗[K] kummerExtension K n Ω Δ →ₐ[F] E) (hg : Function.Surjective g) :
    finrank F E = 1 ↔ ∀ a ∈ Δ, ∃ x : F, x ^ n = algebraMap K F (a : K) := by
  let ι : kummerExtension K n Ω Δ →ₐ[K] E :=
    (g.restrictScalars K).comp Algebra.TensorProduct.includeRight
  constructor
  · intro h1 a ha
    have hsurj : Function.Surjective (algebraMap F E) :=
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1).2
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
    have hnK : NeZero ((n : ℕ) : K) := hζ.neZero'
    have hnΩ : NeZero ((n : ℕ) : Ω) :=
      ⟨by rw [← map_natCast (algebraMap K Ω)]; exact (map_ne_zero _).2 hnK.out⟩
    obtain ⟨α, hα⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap K Ω (a : K)) n
    let y : kummerExtension K n Ω Δ := ⟨α, subset_adjoin _ _ ⟨a, ha, hα⟩⟩
    obtain ⟨x, hx⟩ := hsurj (ι y)
    refine ⟨x, (algebraMap F E).injective ?_⟩
    rw [map_pow, hx, ← map_pow, kummerExtension_pow_eq (y := y) hα, ι.commutes,
      ← IsScalarTower.algebraMap_apply]
  · intro h
    exact finrank_eq_one_of_tensor_surjective g hg fun m ↦
      algHom_kummerExtension_mem_fieldRange ι h m

end Local

section Global

variable {K : Type*} [Field K] [NumberField K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
  {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosed Ω] {Δ : Subgroup Kˣ}
  [Finite (Δ ⧸ (unitsPow K n).subgroupOf Δ)]

instance numberField_kummerExtension : NumberField (kummerExtension K n Ω Δ) :=
  NumberField.of_module_finite K _

open SemiLocal in

theorem splitsCompletely_kummerExtension_iff (v : HeightOneSpectrum (𝓞 K)) :
    SplitsCompletely (kummerExtension K n Ω Δ) v ↔
      ∀ a ∈ Δ, ∃ x : v.adicCompletion K, x ^ n = algebraMap K (v.adicCompletion K) (a : K) := by
  have key (w : PlacesOver (kummerExtension K n Ω Δ) v) :=
    finrank_eq_one_iff_of_kummerExtension
      ((Pi.evalAlgHom (v.adicCompletion K) _ w).comp
        (tensorEquiv (kummerExtension K n Ω Δ) v).toAlgHom)
      ((Function.surjective_eval w).comp (tensorEquiv (kummerExtension K n Ω Δ) v).surjective)
  rw [splitsCompletely_iff_forall_finrank]
  refine ⟨fun h ↦ ?_, fun h w ↦ (key w).2 h⟩
  obtain ⟨w⟩ := nonempty_placesOver (kummerExtension K n Ω Δ) v
  exact (key w).1 (h w)

open scoped NumberField.LiesOver in

theorem InfinitePlace.splitsCompletely_kummerExtension_iff (v : NumberField.InfinitePlace K) :
    InfinitePlace.SplitsCompletely (kummerExtension K n Ω Δ) v ↔
      ∀ a ∈ Δ, ∃ x : v.Completion, x ^ n = algebraMap K v.Completion (a : K) := by
  have key (w : v.placesOver (kummerExtension K n Ω Δ)) :=
    finrank_eq_one_iff_of_kummerExtension
      ((Pi.evalAlgHom v.Completion _ w).comp
        (InfinitePlace.tensorPiHom (L := kummerExtension K n Ω Δ) v))
      ((Function.surjective_eval w).comp
        (InfinitePlace.tensorPiHom_surjective (L := kummerExtension K n Ω Δ) v))
  rw [InfinitePlace.splitsCompletely_iff_forall_finrank]
  refine ⟨fun h ↦ ?_, fun h w ↦ (key w).2 h⟩
  obtain ⟨w⟩ := InfinitePlace.nonempty_placesOver (kummerExtension K n Ω Δ) v
  exact (key w).1 (h w)

end Global

end GroundTheory.Global
