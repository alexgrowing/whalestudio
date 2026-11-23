import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.DifferentIdeal.LineR

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

private lemma algebraMap_ringOfIntegers_tower {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (x : 𝓞 E) : algebraMap (𝓞 F) F (algebraMap (𝓞 E) (𝓞 F) x) = algebraMap E F (algebraMap (𝓞 E) E x) := rfl

theorem map_mulLeft_den_span_image_eq_map_num {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) :
    Submodule.map (LinearMap.mulLeft (𝓞 F) ((algebraMap (𝓞 E) (𝓞 F) (J.den : 𝓞 E) : 𝓞 F) : F))
        (Submodule.span (𝓞 F) (algebraMap E F '' (J : Set E))) =
      Submodule.map (Algebra.linearMap (𝓞 F) F) (J.num.map (algebraMap (𝓞 E) (𝓞 F))) := by
  have hden := FractionalIdeal.den_mul_self_eq_num J
  rw [Submodule.map_span, Ideal.map, Ideal.span, Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    have h1 : J.den • j ∈ J.den • (J : Submodule (𝓞 E) E) :=
      Submodule.smul_mem_pointwise_smul j _ _ hj
    rw [hden] at h1
    obtain ⟨n, hn, hnj⟩ := Submodule.mem_map.mp h1
    refine ⟨algebraMap (𝓞 E) (𝓞 F) n, ⟨n, hn, rfl⟩, ?_⟩
    show algebraMap (𝓞 F) F (algebraMap (𝓞 E) (𝓞 F) n) =
      algebraMap (𝓞 F) F (algebraMap (𝓞 E) (𝓞 F) (J.den : 𝓞 E)) * algebraMap E F j
    rw [algebraMap_ringOfIntegers_tower, algebraMap_ringOfIntegers_tower, ← map_mul]
    congr 1
  · rintro ⟨_, ⟨n, hn, rfl⟩, rfl⟩
    have h1 : algebraMap (𝓞 E) E n ∈ Submodule.map (Algebra.linearMap (𝓞 E) E) J.num :=
      Submodule.mem_map_of_mem hn
    rw [← hden] at h1
    obtain ⟨j, hj, hjn⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
    refine ⟨algebraMap E F j, ⟨j, hj, rfl⟩, ?_⟩
    show algebraMap (𝓞 F) F (algebraMap (𝓞 E) (𝓞 F) (J.den : 𝓞 E)) * algebraMap E F j =
      algebraMap (𝓞 F) F (algebraMap (𝓞 E) (𝓞 F) n)
    rw [algebraMap_ringOfIntegers_tower, algebraMap_ringOfIntegers_tower, ← map_mul, ← Algebra.smul_def]
    exact congrArg (algebraMap E F) hjn

theorem index_image_ideal {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (s : F)
    (hs : s ∈ Submodule.span (𝓞 F) (algebraMap E F '' (J : Set E))) :
    ((((Submodule.span (𝓞 F) {s}).toAddSubgroup.addSubgroupOf
        (Submodule.span (𝓞 F) (algebraMap E F '' (J : Set E))).toAddSubgroup).index : ℕ) : ℚ) *
        (Ideal.absNorm J.num : ℚ) ^ Module.finrank E F =
      |Algebra.norm ℚ s| * |Algebra.norm ℚ ((J.den : 𝓞 E) : E)| ^ Module.finrank E F := by
  set A := Submodule.span (𝓞 F) (algebraMap E F '' (J : Set E)) with hA
  set c : 𝓞 F := algebraMap (𝓞 E) (𝓞 F) (J.den : 𝓞 E) with hcdef
  have hc : (c : F) = algebraMap E F ((J.den : 𝓞 E) : E) := rfl
  have hden0 : ((J.den : 𝓞 E) : E) ≠ 0 := by
    have := nonZeroDivisors.coe_ne_zero J.den
    exact_mod_cast this
  have hc0 : (c : F) ≠ 0 := by rw [hc]; exact (map_ne_zero _).mpr hden0
  set f := LinearMap.mulLeft (𝓞 F) (c : F) with hf
  have hfinj : Function.Injective f := fun x y h => mul_left_cancel₀ hc0 h
  set I2 : Ideal (𝓞 F) := J.num.map (algebraMap (𝓞 E) (𝓞 F)) with hI2
  have hmapA : Submodule.map f A = Submodule.map (Algebra.linearMap (𝓞 F) F) I2 := map_mulLeft_den_span_image_eq_map_num J
  have hcs : (c : F) * s ∈ Submodule.map (Algebra.linearMap (𝓞 F) F) I2 := by
    rw [← hmapA]; exact ⟨s, hs, rfl⟩
  obtain ⟨t, ht, hts⟩ := hcs
  simp only [Algebra.linearMap_apply] at hts
  have hmaps : Submodule.map f (Submodule.span (𝓞 F) {s}) =
      Submodule.map (Algebra.linearMap (𝓞 F) F) (Ideal.span {t}) := by
    rw [Ideal.span, Submodule.map_span, Submodule.map_span, Set.image_singleton, Set.image_singleton]
    simp only [Algebra.linearMap_apply, hts]
    rfl
  have hginj : Function.Injective (Algebra.linearMap (𝓞 F) F) := RingOfIntegers.coe_injective
  have hrel : (((Submodule.span (𝓞 F) {s}).toAddSubgroup.addSubgroupOf A.toAddSubgroup).index) =
      (Ideal.span {t}).toAddSubgroup.relIndex I2.toAddSubgroup := by
    change (Submodule.span (𝓞 F) {s}).toAddSubgroup.relIndex A.toAddSubgroup = _
    have h1 := AddSubgroup.relIndex_map_map_of_injective (f := (f : F →+ F))
      (Submodule.span (𝓞 F) {s}).toAddSubgroup A.toAddSubgroup hfinj
    rw [← h1, ← Submodule.map_toAddSubgroup, ← Submodule.map_toAddSubgroup, hmaps, hmapA,
      Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective
      (f := ((Algebra.linearMap (𝓞 F) F) : 𝓞 F →+ F)) _ _ hginj
  have hle : (Ideal.span {t}).toAddSubgroup ≤ I2.toAddSubgroup := by
    intro x hx
    exact (Ideal.span_singleton_le_iff_mem _).mpr ht hx
  have hmul := AddSubgroup.relIndex_mul_index hle
  rw [← Ideal.absNorm_eq_index, ← Ideal.absNorm_eq_index, Ideal.absNorm_span_singleton, hI2,
    Ideal.absNorm_algebraMap, ← IsFractionRing.finrank_eq (𝓞 E) E (𝓞 F) F] at hmul
  rw [hrel]
  have hnt : ((Algebra.norm ℤ t : ℤ) : ℚ) = Algebra.norm ℚ s * (Algebra.norm ℚ ((J.den : 𝓞 E) : E)) ^ Module.finrank E F := by
    rw [Algebra.coe_norm_int, show ((t : F)) = (c : F) * s from hts, map_mul, hc, mul_comm]
    congr 1
    rw [← Algebra.norm_norm (S := E), Algebra.norm_algebraMap, map_pow]
  have hq := congrArg (fun n : ℕ => (n : ℚ)) hmul
  simp only [Nat.cast_mul, Nat.cast_pow] at hq
  rw [hq, Nat.cast_natAbs, Int.cast_abs, hnt, abs_mul, abs_pow]

theorem index_imI_ext {E F : Type} [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F]
    (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (s : F)
    (hs : s ∈ Submodule.span (𝓞 F) (algebraMap E F '' (J : Set E))) :
    ((((Submodule.span (𝓞 F) {s}).toAddSubgroup.addSubgroupOf
        (Submodule.span (𝓞 F) (algebraMap E F '' (J : Set E))).toAddSubgroup).index : ℕ) : ℚ) ^
        Module.finrank ℚ E * (FractionalIdeal.absNorm J : ℚ) ^ Module.finrank ℚ F =
      |Algebra.norm ℚ s| ^ Module.finrank ℚ E := by
  have haux := index_image_ideal J s hs
  have hJ : (FractionalIdeal.absNorm J : ℚ) =
      (Ideal.absNorm J.num : ℚ) / |Algebra.norm ℚ ((J.den : 𝓞 E) : E)| := by
    rw [FractionalIdeal.absNorm_eq, Int.cast_abs, Algebra.coe_norm_int]
  have hD : |Algebra.norm ℚ ((J.den : 𝓞 E) : E)| ≠ 0 := by
    refine abs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr ?_)
    exact (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr (nonZeroDivisors.coe_ne_zero J.den)
  have hf : Module.finrank ℚ F = Module.finrank ℚ E * Module.finrank E F :=
    (Module.finrank_mul_finrank ℚ E F).symm
  rw [hJ, hf, div_pow, ← mul_div_assoc, div_eq_iff (pow_ne_zero _ hD),
    mul_comm (Module.finrank ℚ E) (Module.finrank E F), pow_mul, pow_mul, ← mul_pow, ← mul_pow, haux]

theorem index_imI {E : Type} [Field E] [NumberField E] (M : IntermediateField ℚ ℂ) [NumberField M]
    (σ : E →+* ℂ) (hσ : ∀ y, σ y ∈ M) (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hJ : J ≠ 0) (s : M) (hs0 : s ≠ 0)
    (hs : s ∈ imI M σ J) :
    ((((Submodule.span (𝓞 M) {s}).toAddSubgroup.addSubgroupOf
        (imI M σ J).toAddSubgroup).index : ℕ) : ℝ) ^ Module.finrank ℚ E *
      ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ Module.finrank ℚ M =
      |((Algebra.norm ℚ s : ℚ) : ℝ)| ^ Module.finrank ℚ E := by
  letI : Algebra E M := (σ.codRestrict M hσ).toAlgebra
  have hlift : ∀ a, algebraMap E M a = liftM M (σ a) := fun a =>
    Subtype.ext (by rw [show ((liftM M (σ a) : M) : ℂ) = σ a by simp [liftM, hσ a]]; rfl)
  have hI : imI M σ J = Submodule.span (𝓞 M) (algebraMap E M '' (J : Set E)) := by
    unfold imI
    congr 1
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, hlift a⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, hlift a⟩
  rw [hI] at hs ⊢
  have h := index_imI_ext (E := E) (F := M) J s hs
  exact_mod_cast h

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
