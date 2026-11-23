import Mathlib

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

open NumberField
open scoped nonZeroDivisors

theorem relIndex_eq_map_mul_ker {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) {A B : AddSubgroup G} (hAB : A ≤ B) :
    A.relIndex B = (A.map f).relIndex (B.map f) * (A ⊓ f.ker).relIndex (B ⊓ f.ker) := by
  have hN : A ⊓ (B ⊓ f.ker) = A ⊓ f.ker := by
    rw [← inf_assoc, inf_eq_left.mpr hAB]
  have hC : (A ⊔ f.ker) ⊓ B = A ⊔ (B ⊓ f.ker) := by
    ext x
    simp only [AddSubgroup.mem_inf, AddSubgroup.mem_sup]
    constructor
    · rintro ⟨⟨y, hy, z, hz, rfl⟩, hx⟩
      refine ⟨y, hy, z, ⟨?_, hz⟩, rfl⟩
      have := B.sub_mem hx (hAB hy)
      simpa using this
    · rintro ⟨y, hy, z, ⟨hzB, hz⟩, rfl⟩
      exact ⟨⟨y, hy, z, hz, rfl⟩, B.add_mem (hAB hy) hzB⟩
  have h1 : (A.map f).relIndex (B.map f) = (A ⊔ (B ⊓ f.ker)).relIndex B := by
    rw [← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq,
      ← AddSubgroup.inf_relIndex_right, hC]
  have h2 : (A ⊓ f.ker).relIndex (B ⊓ f.ker) = A.relIndex (A ⊔ (B ⊓ f.ker)) := by
    rw [sup_comm A, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right A (B ⊓ f.ker),
      hN]
  rw [h1, h2, mul_comm]
  exact (AddSubgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le hAB inf_le_left)).symm

def intVec (K : Type) [Field K] [NumberField K] (k : ℕ) : Submodule (𝓞 K) (Fin k → K) :=
  Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 K) K)

theorem mem_intVec {K : Type} [Field K] [NumberField K] {k : ℕ} {x : Fin k → K} :
    x ∈ intVec K k ↔ ∀ i, x i ∈ (1 : Submodule (𝓞 K) K) := by
  simp [intVec, Submodule.mem_pi]

theorem exists_section_of_image {K : Type} [Field K] [NumberField K] {V : Type*}
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (X : Submodule (𝓞 K) V) (f : V →ₗ[K] K) (hfg : (X.map (f.restrictScalars (𝓞 K))).FG)
    (h1 : (1 : Submodule (𝓞 K) K) ≤ X.map (f.restrictScalars (𝓞 K))) :
    ∃ v : V, f v = 1 ∧ ∀ t ∈ X.map (f.restrictScalars (𝓞 K)), t • v ∈ X := by
  classical
  let I : FractionalIdeal (𝓞 K)⁰ K :=
    ⟨X.map (f.restrictScalars (𝓞 K)), FractionalIdeal.isFractional_of_fg hfg⟩
  have hone : (1 : K) ∈ (1 : Submodule (𝓞 K) K) := Submodule.mem_one.mpr ⟨1, map_one _⟩
  have hI0 : I ≠ 0 := by
    intro h
    have h1I : (1 : K) ∈ (I : Submodule (𝓞 K) K) := h1 hone
    rw [h, FractionalIdeal.coe_zero, Submodule.mem_bot] at h1I
    exact one_ne_zero h1I
  have hII : (I : Submodule (𝓞 K) K) * ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) =
      1 := by
    rw [← FractionalIdeal.coe_mul, mul_inv_cancel₀ hI0, FractionalIdeal.coe_one]
  have key : ∀ w ∈ (I : Submodule (𝓞 K) K) * ((I⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K),
      ∃ u : V, f u = w ∧ ∀ t ∈ X.map (f.restrictScalars (𝓞 K)), t • u ∈ X := by
    intro w hw
    refine Submodule.mul_induction_on hw (fun c hc d hd => ?_) (fun a b ha hb => ?_)
    · obtain ⟨x, hx, hfx⟩ := Submodule.mem_map.mp hc
      rw [LinearMap.restrictScalars_apply] at hfx
      refine ⟨d • x, ?_, fun t ht => ?_⟩
      · rw [map_smul, smul_eq_mul, hfx, mul_comm]
      · have htd : t * d ∈ (1 : Submodule (𝓞 K) K) := by
          rw [← hII]
          exact Submodule.mul_mem_mul (show t ∈ (I : Submodule (𝓞 K) K) from ht) hd
        obtain ⟨r, hr⟩ := Submodule.mem_one.mp htd
        rw [smul_smul, ← hr, algebraMap_smul]
        exact X.smul_mem r hx
    · obtain ⟨u1, e1, h1'⟩ := ha
      obtain ⟨u2, e2, h2'⟩ := hb
      exact ⟨u1 + u2, by rw [map_add, e1, e2], fun t ht => by
        rw [smul_add]; exact X.add_mem (h1' t ht) (h2' t ht)⟩
  exact key 1 (by rw [hII]; exact hone)

theorem absNorm_mul_relIndex_one {K : Type} [Field K] [NumberField K] (C : Submodule (𝓞 K) K)
    (hC : C.FG) (h1 : 1 ≤ C) :
    FractionalIdeal.absNorm
        (⟨C, FractionalIdeal.isFractional_of_fg hC⟩ : FractionalIdeal (𝓞 K)⁰ K) *
      ((1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex C.toAddSubgroup : ℚ) = 1 := by
  classical
  set I : FractionalIdeal (𝓞 K)⁰ K := ⟨C, FractionalIdeal.isFractional_of_fg hC⟩ with hIdef
  have hden := FractionalIdeal.den_mul_self_eq_num I
  set d : 𝓞 K := (I.den : 𝓞 K) with hd
  set J : Ideal (𝓞 K) := I.num with hJ
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero I.den.2
  have hdK : algebraMap (𝓞 K) K d ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors I.den.2
  let ι : 𝓞 K →+ K := (algebraMap (𝓞 K) K).toAddMonoidHom
  have hι : Function.Injective ι := IsFractionRing.injective (𝓞 K) K
  let μ : K →+ K := AddMonoidHom.mulLeft (algebraMap (𝓞 K) K d)
  have hμ : Function.Injective μ := mul_right_injective₀ hdK
  have hsm : ∀ y : K, (I.den : 𝓞 K) • y = μ y := fun y => by
    rw [Algebra.smul_def]
    rfl
  have hone : AddSubgroup.map μ (1 : Submodule (𝓞 K) K).toAddSubgroup =
      AddSubgroup.map ι (Ideal.span {d}).toAddSubgroup := by
    ext x
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_one,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨y, ⟨r, rfl⟩, rfl⟩
      exact ⟨r * d, ⟨r, rfl⟩, by simp [μ, ι, mul_comm]⟩
    · rintro ⟨y, ⟨r, rfl⟩, rfl⟩
      exact ⟨algebraMap (𝓞 K) K r, ⟨r, rfl⟩, by simp [μ, ι, mul_comm]⟩
  have hCm : AddSubgroup.map μ C.toAddSubgroup = AddSubgroup.map ι J.toAddSubgroup := by
    ext x
    open Pointwise in
    have hx : x ∈ ((I.den : 𝓞 K) • (I : Submodule (𝓞 K) K)) ↔
        x ∈ Submodule.map (Algebra.linearMap (𝓞 K) K) I.num := by
      rw [← hden]
      exact Iff.rfl
    rw [Submodule.mem_map, Submodule.mem_smul_pointwise_iff_exists] at hx
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzx⟩ := hx.mp ⟨y, hy, hsm y⟩
      exact ⟨z, hz, hzx⟩
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨y, hy, hyx⟩ := hx.mpr ⟨z, hz, rfl⟩
      exact ⟨y, hy, by rw [← hsm]; exact hyx⟩
  have hidx : (1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex C.toAddSubgroup =
      (Ideal.span {d}).toAddSubgroup.relIndex J.toAddSubgroup := by
    rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hμ, hone, hCm,
      AddSubgroup.relIndex_map_map_of_injective _ _ hι]
  have hle : Ideal.span {d} ≤ J := by
    rw [Ideal.span_singleton_le_iff_mem]
    have h1C : (1 : K) ∈ C := h1 (Submodule.mem_one.mpr ⟨1, map_one _⟩)
    have hm : algebraMap (𝓞 K) K d ∈ Submodule.map (Algebra.linearMap (𝓞 K) K) I.num := by
      rw [← hden]
      open Pointwise in
      show _ ∈ ((I.den : 𝓞 K) • (I : Submodule (𝓞 K) K))
      exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
        ⟨1, h1C, by rw [hsm]; simp [μ]⟩
    obtain ⟨z, hz, hzd⟩ := Submodule.mem_map.mp hm
    have hzd' := hι hzd
    rw [hd, ← hzd']
    exact hz
  have htower := AddSubgroup.relIndex_mul_relIndex (Ideal.span {d}).toAddSubgroup
    J.toAddSubgroup ⊤ hle le_top
  rw [AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_top_right] at htower
  have hiJ : J.toAddSubgroup.index = Ideal.absNorm J := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, AddSubgroup.index_eq_card]
    rfl
  have hid : (Ideal.span {d}).toAddSubgroup.index = (Algebra.norm ℤ d).natAbs := by
    rw [← Ideal.absNorm_span_singleton, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      AddSubgroup.index_eq_card]
    rfl
  rw [hiJ, hid] at htower
  have hb : (Algebra.norm ℤ d).natAbs ≠ 0 := by
    rw [← Ideal.absNorm_span_singleton]
    intro h
    rw [Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] at h
    exact hd0 h
  have hbq : ((Algebra.norm ℤ d).natAbs : ℚ) ≠ 0 := by exact_mod_cast hb
  have hcast : ((|Algebra.norm ℤ d| : ℤ) : ℚ) = ((Algebra.norm ℤ d).natAbs : ℚ) := by
    simp [Nat.cast_natAbs, Int.cast_abs]
  rw [hidx, FractionalIdeal.absNorm_eq, hcast, div_mul_eq_mul_div, div_eq_one_iff_eq hbq]
  rw [mul_comm] at htower
  exact_mod_cast htower

end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
