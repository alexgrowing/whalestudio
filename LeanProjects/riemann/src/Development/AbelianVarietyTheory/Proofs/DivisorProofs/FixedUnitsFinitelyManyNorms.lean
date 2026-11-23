import Mathlib

open NumberField

namespace GlobalTheory

theorem units_ringOfIntegers_mod_sq (L : Type) [Field L] [NumberField L] :
    ∃ R : Finset (𝓞 L)ˣ, ∀ x : (𝓞 L)ˣ, ∃ ρ ∈ R, ∃ w : (𝓞 L)ˣ, x = ρ * w ^ 2 := by
  classical
  let N : Submodule ℤ (Additive (𝓞 L)ˣ) := LinearMap.range ((2 : ℤ) • LinearMap.id)
  haveI : Module.Finite ℤ (Additive (𝓞 L)ˣ) := inferInstance
  haveI : Finite (Additive (𝓞 L)ˣ ⧸ N) := by
    refine Module.finite_of_fg_torsion _ fun q => ⟨⟨2, mem_nonZeroDivisors_of_ne_zero two_ne_zero⟩, ?_⟩
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      show (2 : ℤ) • (Submodule.Quotient.mk (p := N) x) = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨x, rfl⟩
  haveI : Fintype (Additive (𝓞 L)ˣ ⧸ N) := Fintype.ofFinite _
  let rep := Function.surjInv (Submodule.Quotient.mk_surjective N)
  refine ⟨Finset.univ.image (fun q => Additive.toMul (rep q)), fun x => ?_⟩
  let q : Additive (𝓞 L)ˣ ⧸ N := Submodule.Quotient.mk (Additive.ofMul x)
  refine ⟨Additive.toMul (rep q), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  have hq : Submodule.Quotient.mk (p := N) (rep q) = q := Function.surjInv_eq _ q
  have hmem : Additive.ofMul x - rep q ∈ N := by
    rw [← Submodule.Quotient.eq]; exact hq.symm
  obtain ⟨y, hy⟩ := hmem
  refine ⟨Additive.toMul y, ?_⟩
  have h2 : Additive.toMul ((2 : ℤ) • y) = Additive.toMul (Additive.ofMul x - rep q) := by
    simpa using congrArg Additive.toMul hy
  rw [toMul_zsmul, toMul_sub, toMul_ofMul] at h2
  rw [eq_div_iff_mul_eq'] at h2
  rw [← h2]; exact mul_comm _ _

theorem units_fixed_eq_mul_mul_conj : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) →
    ∃ S : Finset L, ∀ ε : Lˣ, IsIntegral ℤ (ε : L) → IsIntegral ℤ ((ε⁻¹ : Lˣ) : L) → c ε = ε →
      ∃ f ∈ S, ∃ η : Lˣ, IsIntegral ℤ (η : L) ∧ IsIntegral ℤ ((η⁻¹ : Lˣ) : L) ∧ (ε : L) = f * ((η : L) * c η) := by
  intro L _ _ c _hc
  classical
  obtain ⟨R, hR⟩ := units_ringOfIntegers_mod_sq L
  let φ : 𝓞 L →* L := (algebraMap (𝓞 L) L : 𝓞 L →* L)
  have hA : ∀ ε : Lˣ, IsIntegral ℤ (ε : L) → IsIntegral ℤ ((ε⁻¹ : Lˣ) : L) →
      ∃ ρ ∈ R, ∃ w : (𝓞 L)ˣ, (ε : L) = φ (ρ : 𝓞 L) * (φ (w : 𝓞 L)) ^ 2 := by
    intro ε h1 h2
    let u : (𝓞 L)ˣ := ⟨⟨ε, h1⟩, ⟨((ε⁻¹ : Lˣ) : L), h2⟩,
      by apply RingOfIntegers.ext; exact ε.mul_inv, by apply RingOfIntegers.ext; exact ε.inv_mul⟩
    obtain ⟨ρ, hρ, w, hw⟩ := hR u
    refine ⟨ρ, hρ, w, ?_⟩
    calc (ε : L) = φ (u : 𝓞 L) := rfl
      _ = φ (ρ : 𝓞 L) * (φ (w : 𝓞 L)) ^ 2 := by rw [hw, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
  let P : (𝓞 L)ˣ → Prop := fun ρ => ∃ e : Lˣ, IsIntegral ℤ (e : L) ∧ IsIntegral ℤ ((e⁻¹ : Lˣ) : L) ∧
    c e = e ∧ ∃ w : (𝓞 L)ˣ, (e : L) = φ (ρ : 𝓞 L) * (φ (w : 𝓞 L)) ^ 2
  let pick : (𝓞 L)ˣ → Finset L := fun ρ =>
    if h : P ρ then {((Classical.choose h : Lˣ) : L), -((Classical.choose h : Lˣ) : L)} else ∅
  refine ⟨R.biUnion pick, ?_⟩
  intro ε h1 h2 hfix
  obtain ⟨ρ, hρ, w, hw⟩ := hA ε h1 h2
  have hP : P ρ := ⟨ε, h1, h2, hfix, w, hw⟩
  obtain ⟨_g1, _g2, gfix, w', hw'⟩ := Classical.choose_spec hP
  have hpick : pick ρ = {((Classical.choose hP : Lˣ) : L), -((Classical.choose hP : Lˣ) : L)} := by
    simp only [pick, dif_pos hP]
  set e : Lˣ := Classical.choose hP with he
  let W : Lˣ := Units.map φ (w * w'⁻¹)
  have hint : ∀ v : (𝓞 L)ˣ, IsIntegral ℤ (φ (v : 𝓞 L)) := fun v => RingOfIntegers.isIntegral_coe _
  have hWint : IsIntegral ℤ (W : L) := hint _
  have hWint' : IsIntegral ℤ ((W⁻¹ : Lˣ) : L) := by
    have : W⁻¹ = Units.map φ (w * w'⁻¹)⁻¹ := (map_inv _ _).symm
    rw [this]; exact hint _
  have hw'0 : φ (w' : 𝓞 L) ≠ 0 := (Units.map φ w').ne_zero
  have hWval : (W : L) = φ (w : 𝓞 L) * (φ (w' : 𝓞 L))⁻¹ := by
    have : W = Units.map φ w * (Units.map φ w')⁻¹ := by simp only [W, map_mul, map_inv]
    rw [this, Units.val_mul, Units.val_inv_eq_inv_val]; rfl
  have key : (ε : L) = (e : L) * (W : L) ^ 2 := by
    rw [hWval, hw', hw]; field_simp
  have he0 : (e : L) ≠ 0 := e.ne_zero
  have hsq : (c (W : L)) ^ 2 = (W : L) ^ 2 := by
    have h3 : c (ε : L) = c (e : L) * (c (W : L)) ^ 2 := by rw [key, map_mul, map_pow]
    rw [hfix, gfix, key] at h3
    exact (mul_left_cancel₀ he0 h3).symm
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · refine ⟨(e : L), Finset.mem_biUnion.mpr ⟨ρ, hρ, by rw [hpick]; simp⟩, W, hWint, hWint', ?_⟩
    rw [key, h]; ring
  · refine ⟨-(e : L), Finset.mem_biUnion.mpr ⟨ρ, hρ, by rw [hpick]; simp⟩, W, hWint, hWint', ?_⟩
    rw [key, h]; ring

end GlobalTheory
