import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroupFiltration

namespace GroundTheory.Arith.Abelian

noncomputable section

open IsLocalRing

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]

section Residue

theorem isUnit_of_residue_ne_zero {a : 𝒪} (h : residue 𝒪 a ≠ 0) : IsUnit a := by
  by_contra hu
  exact h ((residue_eq_zero_iff a).2 ((mem_maximalIdeal a).2 hu))

theorem residue_eq_zero_of_mem {a : 𝒪} (h : a ∈ maximalIdeal 𝒪) : residue 𝒪 a = 0 :=
  (residue_eq_zero_iff a).2 h

theorem one_notMem_maximalIdeal : (1 : 𝒪) ∉ maximalIdeal 𝒪 :=
  fun h => (maximalIdeal.isMaximal 𝒪).ne_top ((Ideal.eq_top_iff_one _).2 h)

end Residue

variable (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)

abbrev curveK : WeierstrassCurve.Affine K := (W.map (algebraMap 𝒪 K)).toAffine

abbrev curveRed : WeierstrassCurve.Affine (ResidueField 𝒪) := (W.map (residue 𝒪)).toAffine

section Integral

theorem exists_inv_mem_of_notMem_range {X : K} (hX : X ∉ Set.range (algebraMap 𝒪 K)) :
    ∃ t ∈ maximalIdeal 𝒪, algebraMap 𝒪 K t = X⁻¹ := by
  obtain ⟨t, ht⟩ : ∃ t, algebraMap 𝒪 K t = X⁻¹ := by
    rcases ValuationRing.isInteger_or_isInteger 𝒪 X with h | h
    · exact absurd h hX
    · exact h
  refine ⟨t, (mem_maximalIdeal _).2 fun hu => hX ⟨↑hu.unit⁻¹, ?_⟩, ht⟩
  rw [← inv_inv X, ← ht]
  exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, hu.val_inv_mul, map_one])

theorem exists_y_of_equation {x : 𝒪} {Y : K}
    (h : (W.map (algebraMap 𝒪 K)).toAffine.Equation (algebraMap 𝒪 K x) Y) :
    ∃ y, algebraMap 𝒪 K y = Y := by
  by_contra hY
  have hY' : Y ∉ Set.range (algebraMap 𝒪 K) := fun ⟨y, hy⟩ => hY ⟨y, hy⟩
  obtain ⟨t, ht, htY⟩ := exists_inv_mem_of_notMem_range K hY'
  have hY0 : Y ≠ 0 := fun h0 => hY ⟨0, by rw [h0, map_zero]⟩
  rw [WeierstrassCurve.Affine.equation_iff] at h
  have key : algebraMap 𝒪 K (1 + (W.a₁ * x + W.a₃) * t - (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) *
      t ^ 2) = 0 := by
    simp only [map_sub, map_add, map_mul, map_pow, map_one, htY]
    simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h
    field_simp
    linear_combination h
  have k2 := (map_eq_zero_iff _ (IsFractionRing.injective 𝒪 K)).1 key
  apply one_notMem_maximalIdeal (𝒪 := 𝒪)
  have e : (1 : 𝒪) = (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆) * t ^ 2 - (W.a₁ * x + W.a₃) * t := by
    linear_combination k2
  rw [e]
  exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ ht _ (by norm_num)))
    (Ideal.mul_mem_left _ _ ht)

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] in
theorem equation_of_map {x y : 𝒪}
    (h : (W.map (algebraMap 𝒪 K)).toAffine.Equation (algebraMap 𝒪 K x) (algebraMap 𝒪 K y)) :
    W.toAffine.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  apply IsFractionRing.injective 𝒪 K
  simpa using h

theorem equation_residue {x y : 𝒪} (h : W.toAffine.Equation x y) :
    (W.map (residue 𝒪)).toAffine.Equation (residue 𝒪 x) (residue 𝒪 y) := by
  rw [WeierstrassCurve.Affine.equation_iff] at h ⊢
  simpa using congrArg (residue 𝒪) h

end Integral

section Sum

variable [DecidableEq K] [DecidableEq (ResidueField 𝒪)]

local notation "ι" => algebraMap 𝒪 K
local notation "ρ" => residue 𝒪

omit [IsFractionRing 𝒪 K] in

theorem add_some_integral {x₁ y₁ x₂ y₂ ℓ : 𝒪} (h₁ : (curveK K W).Nonsingular (ι x₁) (ι y₁))
    (h₂ : (curveK K W).Nonsingular (ι x₂) (ι y₂)) (n₁ : (curveRed W).Nonsingular (ρ x₁) (ρ y₁))
    (n₂ : (curveRed W).Nonsingular (ρ x₂) (ρ y₂))
    (hxy : ¬(ι x₁ = ι x₂ ∧ ι y₁ = (curveK K W).negY (ι x₂) (ι y₂)))
    (hxy' : ¬(ρ x₁ = ρ x₂ ∧ ρ y₁ = (curveRed W).negY (ρ x₂) (ρ y₂)))
    (hs : (curveK K W).slope (ι x₁) (ι x₂) (ι y₁) (ι y₂) = ι ℓ)
    (hs' : (curveRed W).slope (ρ x₁) (ρ x₂) (ρ y₁) (ρ y₂) = ρ ℓ) :
    ∃ (h₃ : (curveK K W).Nonsingular (ι (W.toAffine.addX x₁ x₂ ℓ)) (ι (W.toAffine.addY x₁ x₂ y₁ ℓ)))
      (n₃ : (curveRed W).Nonsingular (ρ (W.toAffine.addX x₁ x₂ ℓ))
        (ρ (W.toAffine.addY x₁ x₂ y₁ ℓ))),
      WeierstrassCurve.Affine.Point.some _ _ h₁ + WeierstrassCurve.Affine.Point.some _ _ h₂ =
        WeierstrassCurve.Affine.Point.some _ _ h₃ ∧
      WeierstrassCurve.Affine.Point.some _ _ n₁ + WeierstrassCurve.Affine.Point.some _ _ n₂ =
        WeierstrassCurve.Affine.Point.some _ _ n₃ := by
  have hX : (curveK K W).addX (ι x₁) (ι x₂) ((curveK K W).slope (ι x₁) (ι x₂) (ι y₁) (ι y₂)) =
      ι (W.toAffine.addX x₁ x₂ ℓ) := by
    rw [hs]; exact WeierstrassCurve.Affine.map_addX _ _ _ _
  have hY : (curveK K W).addY (ι x₁) (ι x₂) (ι y₁)
      ((curveK K W).slope (ι x₁) (ι x₂) (ι y₁) (ι y₂)) =
      ι (W.toAffine.addY x₁ x₂ y₁ ℓ) := by
    rw [hs]; exact WeierstrassCurve.Affine.map_addY _ _ _ _ _
  have hX' : (curveRed W).addX (ρ x₁) (ρ x₂) ((curveRed W).slope (ρ x₁) (ρ x₂) (ρ y₁) (ρ y₂)) =
      ρ (W.toAffine.addX x₁ x₂ ℓ) := by
    rw [hs']; exact WeierstrassCurve.Affine.map_addX _ _ _ _
  have hY' : (curveRed W).addY (ρ x₁) (ρ x₂) (ρ y₁)
      ((curveRed W).slope (ρ x₁) (ρ x₂) (ρ y₁) (ρ y₂)) =
      ρ (W.toAffine.addY x₁ x₂ y₁ ℓ) := by
    rw [hs']; exact WeierstrassCurve.Affine.map_addY _ _ _ _ _
  have h₃ := WeierstrassCurve.Affine.nonsingular_add h₁ h₂ hxy
  rw [hX, hY] at h₃
  have n₃ := WeierstrassCurve.Affine.nonsingular_add n₁ n₂ hxy'
  rw [hX', hY'] at n₃
  refine ⟨h₃, n₃, ?_, ?_⟩
  · rw [WeierstrassCurve.Affine.Point.add_some hxy, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hX, hY⟩
  · rw [WeierstrassCurve.Affine.Point.add_some hxy', WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hX', hY'⟩

theorem add_of_residue_X_ne {x₁ y₁ x₂ y₂ : 𝒪} (h₁ : (curveK K W).Nonsingular (ι x₁) (ι y₁))
    (h₂ : (curveK K W).Nonsingular (ι x₂) (ι y₂)) (n₁ : (curveRed W).Nonsingular (ρ x₁) (ρ y₁))
    (n₂ : (curveRed W).Nonsingular (ρ x₂) (ρ y₂)) (hx : ρ x₁ ≠ ρ x₂) :
    ∃ (x₃ y₃ : 𝒪) (h₃ : (curveK K W).Nonsingular (ι x₃) (ι y₃))
      (n₃ : (curveRed W).Nonsingular (ρ x₃) (ρ y₃)),
      WeierstrassCurve.Affine.Point.some _ _ h₁ + WeierstrassCurve.Affine.Point.some _ _ h₂ =
        WeierstrassCurve.Affine.Point.some _ _ h₃ ∧
      WeierstrassCurve.Affine.Point.some _ _ n₁ + WeierstrassCurve.Affine.Point.some _ _ n₂ =
        WeierstrassCurve.Affine.Point.some _ _ n₃ := by
  have hu : IsUnit (x₁ - x₂) := isUnit_of_residue_ne_zero (by rw [map_sub]; exact sub_ne_zero.2 hx)
  set ℓ := (y₁ - y₂) * ↑hu.unit⁻¹ with hℓdef
  have hℓ : ℓ * (x₁ - x₂) = y₁ - y₂ := by rw [hℓdef, mul_assoc, hu.val_inv_mul, mul_one]
  have hxK : ι x₁ ≠ ι x₂ := fun h => hx (by rw [IsFractionRing.injective 𝒪 K h])
  obtain ⟨h₃, n₃, e, e'⟩ := add_some_integral K W h₁ h₂ n₁ n₂ (fun h => hxK h.1) (fun h => hx h.1)
    (by
      rw [WeierstrassCurve.Affine.slope_of_X_ne hxK, div_eq_iff (sub_ne_zero.2 hxK), ← map_sub,
        ← map_sub, ← map_mul, hℓ])
    (by
      rw [WeierstrassCurve.Affine.slope_of_X_ne hx, div_eq_iff (sub_ne_zero.2 hx), ← map_sub,
        ← map_sub, ← map_mul, hℓ])
  exact ⟨_, _, h₃, n₃, e, e'⟩

theorem slope_identity {A : Type*} [CommRing A] (V : WeierstrassCurve A) {x₁ y₁ x₂ y₂ : A}
    (e₁ : V.toAffine.Equation x₁ y₁) (e₂ : V.toAffine.Equation x₂ y₂) :
    (y₁ - y₂) * (y₁ + y₂ + V.a₁ * x₁ + V.a₃) =
      (x₁ - x₂) * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + V.a₂ * (x₁ + x₂) + V.a₄ - V.a₁ * y₂) := by
  rw [WeierstrassCurve.Affine.equation_iff] at e₁ e₂
  linear_combination e₁ - e₂

theorem add_of_residue_eq {x₁ y₁ x₂ y₂ : 𝒪} (h₁ : (curveK K W).Nonsingular (ι x₁) (ι y₁))
    (h₂ : (curveK K W).Nonsingular (ι x₂) (ι y₂)) (n₁ : (curveRed W).Nonsingular (ρ x₁) (ρ y₁))
    (n₂ : (curveRed W).Nonsingular (ρ x₂) (ρ y₂)) (hx : ρ x₁ = ρ x₂) (hy : ρ y₁ = ρ y₂)
    (hD : ρ (y₁ + y₂ + W.a₁ * x₁ + W.a₃) ≠ 0) :
    ∃ (x₃ y₃ : 𝒪) (h₃ : (curveK K W).Nonsingular (ι x₃) (ι y₃))
      (n₃ : (curveRed W).Nonsingular (ρ x₃) (ρ y₃)),
      WeierstrassCurve.Affine.Point.some _ _ h₁ + WeierstrassCurve.Affine.Point.some _ _ h₂ =
        WeierstrassCurve.Affine.Point.some _ _ h₃ ∧
      WeierstrassCurve.Affine.Point.some _ _ n₁ + WeierstrassCurve.Affine.Point.some _ _ n₂ =
        WeierstrassCurve.Affine.Point.some _ _ n₃ := by
  have hι := IsFractionRing.injective 𝒪 K
  set D := y₁ + y₂ + W.a₁ * x₁ + W.a₃ with hDdef
  set N := x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₂ with hNdef
  have hu : IsUnit D := isUnit_of_residue_ne_zero hD
  set ℓ := N * ↑hu.unit⁻¹ with hℓdef
  have hℓ : ℓ * D = N := by rw [hℓdef, mul_assoc, hu.val_inv_mul, mul_one]
  have e₁ := equation_of_map K W h₁.1
  have e₂ := equation_of_map K W h₂.1
  have hid := slope_identity W e₁ e₂
  have hDK : ι D ≠ 0 := (map_ne_zero_iff _ hι).2 hu.ne_zero
  have hxy : ¬(ι x₁ = ι x₂ ∧ ι y₁ = (curveK K W).negY (ι x₂) (ι y₂)) := by
    rintro ⟨h1, h2⟩
    apply hDK
    rw [WeierstrassCurve.Affine.map_negY] at h2
    have hD0 : D = 0 := by
      rw [hDdef, hι h2, hι h1]; simp only [WeierstrassCurve.Affine.negY]; ring
    rw [hD0, map_zero]
  have hxy' : ¬(ρ x₁ = ρ x₂ ∧ ρ y₁ = (curveRed W).negY (ρ x₂) (ρ y₂)) := by
    rintro ⟨h1, h2⟩
    apply hD
    rw [WeierstrassCurve.Affine.map_negY] at h2
    rw [hDdef, map_add, map_add, map_add, map_mul, h2, h1]
    simp only [WeierstrassCurve.Affine.negY, map_sub, map_neg, map_mul]
    ring
  have hs : (curveK K W).slope (ι x₁) (ι x₂) (ι y₁) (ι y₂) = ι ℓ := by
    by_cases hxK : ι x₁ = ι x₂
    · have hx' := hι hxK
      have hyK : ι y₁ ≠ (curveK K W).negY (ι x₂) (ι y₂) := fun h => hxy ⟨hxK, h⟩
      rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h₁.1 h₂.1 hxK with hy' | hy'
      · have hy'' := hι hy'
        subst hx' hy''
        rw [WeierstrassCurve.Affine.slope_of_Y_ne hxK hyK]
        have hne : ι y₁ - (curveK K W).negY (ι x₁) (ι y₁) = ι D := by
          simp only [WeierstrassCurve.Affine.negY, hDdef, map_add, map_mul,
            WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
          ring
        rw [hne, eq_comm, eq_div_iff hDK, ← map_mul, hℓ, hNdef]
        simp only [map_sub, map_add, map_mul, map_pow, WeierstrassCurve.map_a₁,
          WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄]
        ring
      · exact absurd hy' hyK
    · rw [WeierstrassCurve.Affine.slope_of_X_ne hxK, div_eq_iff (sub_ne_zero.2 hxK), ← map_sub,
        ← map_sub, ← map_mul]
      congr 1
      have : (ℓ * (x₁ - x₂) - (y₁ - y₂)) * D = 0 := by linear_combination (x₁ - x₂) * hℓ - hid
      exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hu.ne_zero)).symm
  have hs' : (curveRed W).slope (ρ x₁) (ρ x₂) (ρ y₁) (ρ y₂) = ρ ℓ := by
    have hyk : ρ y₁ ≠ (curveRed W).negY (ρ x₂) (ρ y₂) := fun h => hxy' ⟨hx, h⟩
    rw [WeierstrassCurve.Affine.slope_of_Y_ne hx hyk]
    have hne : ρ y₁ - (curveRed W).negY (ρ x₁) (ρ y₁) = ρ D := by
      simp only [WeierstrassCurve.Affine.negY, hDdef, map_add, map_mul, WeierstrassCurve.map_a₁,
        WeierstrassCurve.map_a₃, hy]
      ring
    rw [hne, eq_comm, eq_div_iff hD, ← map_mul, hℓ, hNdef]
    simp only [map_sub, map_add, map_mul, map_pow, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄, ← hx, ← hy]
    ring
  obtain ⟨h₃, n₃, e, e'⟩ := add_some_integral K W h₁ h₂ n₁ n₂ hxy hxy' hs hs'
  exact ⟨_, _, h₃, n₃, e, e'⟩

omit [DecidableEq K] [DecidableEq (ResidueField 𝒪)] in

theorem addX_notMem_range {x₁ x₂ s : 𝒪} (hs : s ∈ maximalIdeal 𝒪) (hs0 : s ≠ 0) :
    (curveK K W).addX (ι x₁) (ι x₂) (ι s)⁻¹ ∉ Set.range ι := by
  rintro ⟨r, hr⟩
  have hs0' : ι s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective 𝒪 K)).2 hs0
  have key : ι (s ^ 2 * r - (1 + W.a₁ * s - (W.a₂ + x₁ + x₂) * s ^ 2)) = 0 := by
    simp only [map_sub, map_add, map_mul, map_pow, map_one, hr, WeierstrassCurve.Affine.addX,
      WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂]
    field_simp
    ring
  have k2 := sub_eq_zero.1 ((map_eq_zero_iff _ (IsFractionRing.injective 𝒪 K)).1 key)
  apply one_notMem_maximalIdeal (𝒪 := 𝒪)
  have e : (1 : 𝒪) = s ^ 2 * r - W.a₁ * s + (W.a₂ + x₁ + x₂) * s ^ 2 := by linear_combination -k2
  rw [e]
  refine Ideal.add_mem _ (Ideal.sub_mem _ ?_ (Ideal.mul_mem_left _ _ hs))
    (Ideal.mul_mem_left _ _ ?_)
  · exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hs _ (by norm_num))
  · exact Ideal.pow_mem_of_mem _ hs _ (by norm_num)

omit [DecidableEq K] [DecidableEq (ResidueField 𝒪)] in
theorem nonsingular_residue_iff {x y : 𝒪} (n : (curveRed W).Nonsingular (ρ x) (ρ y)) :
    ρ (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) ≠ 0 ∨ ρ (2 * y + W.a₁ * x + W.a₃) ≠ 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff'] at n
  have h3 : ρ (3 : 𝒪) = 3 := map_ofNat ρ 3
  have h2 : ρ (2 : 𝒪) = 2 := map_ofNat ρ 2
  have e1 : ρ (W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) = (W.map ρ).a₁ * ρ y -
      (3 * ρ x ^ 2 + 2 * (W.map ρ).a₂ * ρ x + (W.map ρ).a₄) := by
    simp only [map_sub, map_add, map_mul, map_pow, h3, h2, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄]
  have e2 : ρ (2 * y + W.a₁ * x + W.a₃) = 2 * ρ y + (W.map ρ).a₁ * ρ x + (W.map ρ).a₃ := by
    simp only [map_add, map_mul, h2, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
  rw [e1, e2]
  exact n.2

theorem add_of_residue_neg {x₁ y₁ x₂ y₂ : 𝒪} (h₁ : (curveK K W).Nonsingular (ι x₁) (ι y₁))
    (h₂ : (curveK K W).Nonsingular (ι x₂) (ι y₂)) (n₁ : (curveRed W).Nonsingular (ρ x₁) (ρ y₁))
    (n₂ : (curveRed W).Nonsingular (ρ x₂) (ρ y₂)) (hx : ρ x₁ = ρ x₂)
    (hy : ρ y₁ = (curveRed W).negY (ρ x₂) (ρ y₂)) :
    WeierstrassCurve.Affine.Point.some _ _ h₁ + WeierstrassCurve.Affine.Point.some _ _ h₂ = 0 ∨
      ∃ (X Y : K) (h : (curveK K W).Nonsingular X Y),
        WeierstrassCurve.Affine.Point.some _ _ h₁ + WeierstrassCurve.Affine.Point.some _ _ h₂ =
          WeierstrassCurve.Affine.Point.some _ _ h ∧ X ∉ Set.range ι := by
  have hι := IsFractionRing.injective 𝒪 K
  by_cases hxy : ι x₁ = ι x₂ ∧ ι y₁ = (curveK K W).negY (ι x₂) (ι y₂)
  · exact Or.inl (WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 hxy.2)
  right
  have hxm : x₁ - x₂ ∈ maximalIdeal 𝒪 := by
    rw [← residue_eq_zero_iff, map_sub, hx, sub_self]
  have e₁ := equation_of_map K W h₁.1
  have e₂ := equation_of_map K W h₂.1
  have hneg : ρ y₂ - (curveRed W).negY (ρ x₂) (ρ y₂) = ρ (2 * y₂ + W.a₁ * x₂ + W.a₃) := by
    simp only [WeierstrassCurve.Affine.negY, map_add, map_mul, map_ofNat, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₃]
    ring
  obtain ⟨s, hs, hs0, hsl⟩ : ∃ s ∈ maximalIdeal 𝒪, s ≠ 0 ∧
      (curveK K W).slope (ι x₁) (ι x₂) (ι y₁) (ι y₂) = (ι s)⁻¹ := by
    by_cases hxK : ι x₁ = ι x₂
    · have hx' := hι hxK
      have hyK : ι y₁ ≠ (curveK K W).negY (ι x₂) (ι y₂) := fun h => hxy ⟨hxK, h⟩
      rcases WeierstrassCurve.Affine.Y_eq_of_X_eq h₁.1 h₂.1 hxK with hy' | hy'
      · have hy'' := hι hy'
        subst hx' hy''
        set D := 2 * y₁ + W.a₁ * x₁ + W.a₃ with hD
        set N := 3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ with hN
        have hDm : D ∈ maximalIdeal 𝒪 := by
          rw [← residue_eq_zero_iff, ← hneg, ← hy, sub_self]
        have hNu : IsUnit N := by
          refine isUnit_of_residue_ne_zero ?_
          rcases nonsingular_residue_iff W n₁ with h | h
          · intro h0; apply h
            rw [show W.a₁ * y₁ - (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄) = -N by rw [hN]; ring,
              map_neg, h0, neg_zero]
          · exact absurd ((residue_eq_zero_iff _).2 hDm) h
        have hDK : ι y₁ - (curveK K W).negY (ι x₁) (ι y₁) = ι D := by
          simp only [WeierstrassCurve.Affine.negY, hD, map_add, map_mul, map_ofNat,
            WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
          ring
        have hD0 : D ≠ 0 := by
          intro h0; apply hyK
          rw [← sub_eq_zero, hDK, h0, map_zero]
        refine ⟨D * ↑hNu.unit⁻¹, Ideal.mul_mem_right _ _ hDm,
          mul_ne_zero hD0 (Units.ne_zero _), ?_⟩
        rw [WeierstrassCurve.Affine.slope_of_Y_ne hxK hyK, hDK]
        have hN' : ι N * ι ↑hNu.unit⁻¹ = 1 := by rw [← map_mul, hNu.mul_val_inv, map_one]
        have hnum : 3 * ι x₁ ^ 2 + 2 * (curveK K W).a₂ * ι x₁ + (curveK K W).a₄ -
            (curveK K W).a₁ * ι y₁ = ι N := by
          rw [hN]
          simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, WeierstrassCurve.map_a₁,
            WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄]
        have hDK' : ι D ≠ 0 := (map_ne_zero_iff _ hι).2 hD0
        rw [hnum]
        refine eq_inv_of_mul_eq_one_left ?_
        rw [map_mul]
        field_simp
        linear_combination hN'
      · exact absurd hy' hyK
    · have hx0 : x₁ - x₂ ≠ 0 := sub_ne_zero.2 (fun h => hxK (by rw [h]))
      have hsK : ι x₁ - ι x₂ ≠ 0 := sub_ne_zero.2 hxK
      by_cases hyr : ρ y₁ = ρ y₂
      ·
        set D := y₁ + y₂ + W.a₁ * x₁ + W.a₃ with hD
        set N := x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₂ with hN
        have hid := slope_identity W e₁ e₂
        have hDm : D ∈ maximalIdeal 𝒪 := by
          rw [← residue_eq_zero_iff, hD]
          simp only [map_add, map_mul, hx, hy, WeierstrassCurve.Affine.negY,
            WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
          ring
        have hNu : IsUnit N := by
          refine isUnit_of_residue_ne_zero ?_
          have hNr : ρ N = -ρ (W.a₁ * y₂ - (3 * x₂ ^ 2 + 2 * W.a₂ * x₂ + W.a₄)) := by
            rw [hN]
            simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, hx]
            ring
          rcases nonsingular_residue_iff W n₂ with h | h
          · rw [hNr]; exact neg_ne_zero.2 h
          · refine absurd ?_ h
            rw [← hneg, sub_eq_zero]
            exact hyr.symm.trans hy
        have hid' : (y₁ - y₂) * D = (x₁ - x₂) * N := hid
        have hD0 : D ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hid'
          exact hx0 ((mul_eq_zero.1 hid'.symm).resolve_right hNu.ne_zero)
        refine ⟨D * ↑hNu.unit⁻¹, Ideal.mul_mem_right _ _ hDm,
          mul_ne_zero hD0 (Units.ne_zero _), ?_⟩
        rw [WeierstrassCurve.Affine.slope_of_X_ne hxK]
        have hN' : ι N * ι ↑hNu.unit⁻¹ = 1 := by rw [← map_mul, hNu.mul_val_inv, map_one]
        have hDK : ι D ≠ 0 := (map_ne_zero_iff _ hι).2 hD0
        have hidK := congrArg ι hid'
        rw [map_mul, map_mul, map_sub, map_sub] at hidK
        refine eq_inv_of_mul_eq_one_left ?_
        rw [map_mul]
        field_simp
        linear_combination (ι ↑hNu.unit⁻¹) * hidK + (ι x₁ - ι x₂) * hN'
      · have hyu : IsUnit (y₁ - y₂) :=
          isUnit_of_residue_ne_zero (by rw [map_sub]; exact sub_ne_zero.2 hyr)
        refine ⟨(x₁ - x₂) * ↑hyu.unit⁻¹, Ideal.mul_mem_right _ _ hxm,
          mul_ne_zero hx0 (Units.ne_zero _), ?_⟩
        rw [WeierstrassCurve.Affine.slope_of_X_ne hxK, ← map_sub, ← map_sub]
        have hy' : ι (y₁ - y₂) * ι ↑hyu.unit⁻¹ = 1 := by rw [← map_mul, hyu.mul_val_inv, map_one]
        have hxK' : ι (x₁ - x₂) ≠ 0 := by rw [map_sub]; exact hsK
        refine eq_inv_of_mul_eq_one_left ?_
        rw [map_mul]
        field_simp
        linear_combination hy'
  refine ⟨_, _, WeierstrassCurve.Affine.nonsingular_add h₁ h₂ hxy,
    WeierstrassCurve.Affine.Point.add_some hxy, ?_⟩
  rw [hsl]
  exact addX_notMem_range K W hs hs0

omit [DecidableEq (ResidueField 𝒪)] in
theorem residue_vVal [IsAdicComplete (maximalIdeal 𝒪) 𝒪] {z : 𝒪} (hz : z ∈ maximalIdeal 𝒪) :
    ρ (vVal W z) = 1 := by
  have h : vVal W z - 1 ∈ maximalIdeal 𝒪 := by
    have := psEvalAt_mem (f := formalV W - 1) (by
      rw [map_sub, map_one, show MvPowerSeries.constantCoeff (formalV W) = 1 from
        constantCoeff_formalV W, sub_self]; exact zero_mem _) (a := fun _ : Unit => z) (fun _ => hz)
    rwa [← evAlgHom_apply _ (fun _ => hz), map_sub, map_one, evAlgHom_apply] at this
  rw [← sub_eq_zero, ← map_one ρ, ← map_sub]
  exact (residue_eq_zero_iff _).2 h

omit [DecidableEq (ResidueField 𝒪)] in

theorem add_of_notMem_range [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [(W.map ι).IsElliptic]
    {X₁ Y₁ : K} (h₁ : (curveK K W).Nonsingular X₁ Y₁) (hX : X₁ ∉ Set.range ι) {x₂ y₂ : 𝒪}
    (h₂ : (curveK K W).Nonsingular (ι x₂) (ι y₂)) :
    ∃ (x₃ y₃ : 𝒪) (h₃ : (curveK K W).Nonsingular (ι x₃) (ι y₃)),
      WeierstrassCurve.Affine.Point.some _ _ h₁ + WeierstrassCurve.Affine.Point.some _ _ h₂ =
        WeierstrassCurve.Affine.Point.some _ _ h₃ ∧ ρ x₃ = ρ x₂ ∧ ρ y₃ = ρ y₂ := by
  have hι := IsFractionRing.injective 𝒪 K

  obtain ⟨z, hzP⟩ : WeierstrassCurve.Affine.Point.some _ _ h₁ ∈ Set.range (pointE K W) := by
    rw [mem_range_pointE_iff]
    intro x y h hP
    rw [WeierstrassCurve.Affine.Point.some.injEq] at hP
    rw [← hP.1]; exact hX
  have hz0 : z.val ≠ 0 := by
    intro h0
    have : z = 0 := MaxIdealPoint.ext h0
    rw [this, pointE_zero] at hzP
    exact WeierstrassCurve.Affine.Point.some_ne_zero h₁ hzP.symm
  rw [pointE_of_ne_zero K W hz0] at hzP
  simp only [WeierstrassCurve.Affine.Point.mk, WeierstrassCurve.Affine.Point.some.injEq] at hzP
  obtain ⟨hX₁, hY₁⟩ := hzP
  set z' := z.val with hz'
  have hzm : z' ∈ maximalIdeal 𝒪 := z.val_mem
  set v := vVal W z' with hv
  set w := wVal W z' with hw
  have hwv : w = z' ^ 3 * v := wVal_eq W hzm
  have hvu : IsUnit v := isUnit_vVal W hzm
  have hwm : w ∈ maximalIdeal 𝒪 := wVal_mem W hzm

  have heu : IsUnit (1 + y₂ * w) := isUnit_of_residue_ne_zero (by
    rw [map_add, map_one, map_mul, residue_eq_zero_of_mem hwm, mul_zero, add_zero]
    exact one_ne_zero)
  have hdu : IsUnit (1 - x₂ * z' ^ 2 * v) := isUnit_of_residue_ne_zero (by
    rw [map_sub, map_one, map_mul, map_mul, map_pow, residue_eq_zero_of_mem hzm]
    simp)
  set e := 1 + y₂ * w with he
  set d := 1 - x₂ * z' ^ 2 * v with hd
  set e' := (↑heu.unit⁻¹ : 𝒪) with he'
  set d' := (↑hdu.unit⁻¹ : 𝒪) with hd'
  have hee : e * e' = 1 := heu.mul_val_inv
  have hdd : d * d' = 1 := hdu.mul_val_inv
  set s := -(z' * d) * e' with hs
  set Fy := 2 * y₂ + W.a₁ * x₂ + W.a₃ with hFy
  set Fx := 3 * x₂ ^ 2 + 2 * W.a₂ * x₂ + W.a₄ - W.a₁ * y₂ with hFx
  set u₃ := (Fy - s * Fx) * z' * v * e * d' ^ 2 with hu₃
  set t₃ := -(Fy - s * Fx) * v * e ^ 2 * d' ^ 3 with ht₃

  have hw0 : ι w ≠ 0 := (map_ne_zero_iff _ hι).2 (wVal_ne_zero W hzm hz0)
  have hz0K : ι z' ≠ 0 := (map_ne_zero_iff _ hι).2 hz0
  have hv0 : ι v ≠ 0 := (map_ne_zero_iff _ hι).2 hvu.ne_zero
  have he0 : ι e ≠ 0 := (map_ne_zero_iff _ hι).2 heu.ne_zero
  have hd0 : ι d ≠ 0 := (map_ne_zero_iff _ hι).2 hdu.ne_zero
  have heeK : ι e * ι e' = 1 := by rw [← map_mul, hee, map_one]
  have hddK : ι d * ι d' = 1 := by rw [← map_mul, hdd, map_one]
  have hwK : ι w = ι z' ^ 3 * ι v := by rw [hwv, map_mul, map_pow]
  have hX₂ : X₁ ≠ ι x₂ := fun h => hX ⟨x₂, h.symm⟩
  have hs0 : ι s ≠ 0 := by
    rw [hs, map_mul, map_neg, map_mul]
    exact mul_ne_zero (neg_ne_zero.2 (mul_ne_zero hz0K hd0)) (fun h => by
      rw [h, mul_zero] at heeK; exact zero_ne_one heeK)
  have hu₁ : X₁ - ι x₂ = ι (z' * d) / ι w := by
    rw [← hX₁, map_mul, hd, map_sub, map_one, map_mul, map_mul, map_pow, hwK]
    field_simp
  have hslope : (curveK K W).slope X₁ (ι x₂) Y₁ (ι y₂) = (ι s)⁻¹ := by
    rw [WeierstrassCurve.Affine.slope_of_X_ne hX₂, hu₁, ← hY₁]
    have hnum : -1 / ι w - ι y₂ = -ι e / ι w := by
      rw [he, map_add, map_one, map_mul]; field_simp; ring
    rw [hnum]
    refine eq_inv_of_mul_eq_one_left ?_
    simp only [hs, map_mul, map_neg]
    field_simp
    linear_combination heeK
  set ℓ := (ι s)⁻¹ with hℓ
  have hline : Y₁ = ι y₂ + ℓ * (X₁ - ι x₂) := by
    have := hslope
    rw [WeierstrassCurve.Affine.slope_of_X_ne hX₂, div_eq_iff (sub_ne_zero.2 hX₂)] at this
    linear_combination this
  have hE₁ := h₁.1
  have hE₂ := h₂.1
  rw [WeierstrassCurve.Affine.equation_iff] at hE₁ hE₂
  rw [hline] at hE₁
  set B := ℓ ^ 2 + (curveK K W).a₁ * ℓ - 3 * ι x₂ - (curveK K W).a₂ with hB
  set C := ℓ * ι Fy - ι Fx with hC
  have hι2 : ι (2 : 𝒪) = 2 := map_ofNat _ 2
  have hι3 : ι (3 : 𝒪) = 3 := map_ofNat _ 3
  have hFyK : ι Fy = 2 * ι y₂ + (curveK K W).a₁ * ι x₂ + (curveK K W).a₃ := by
    rw [hFy]
    simp only [map_add, map_mul, hι2, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
  have hFxK : ι Fx = 3 * ι x₂ ^ 2 + 2 * (curveK K W).a₂ * ι x₂ + (curveK K W).a₄ -
      (curveK K W).a₁ * ι y₂ := by
    rw [hFx]
    simp only [map_add, map_sub, map_mul, map_pow, hι2, hι3, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄]
  have R : (X₁ - ι x₂) * (-(X₁ - ι x₂) ^ 2 + B * (X₁ - ι x₂) + C) = 0 := by
    rw [hC, hFyK, hFxK, hB]
    linear_combination hE₁ - hE₂
  have R' := (mul_eq_zero.1 R).resolve_left (sub_ne_zero.2 hX₂)
  have he'K : ι e' = (ι e)⁻¹ := eq_inv_of_mul_eq_one_right heeK
  have hd'K : ι d' = (ι d)⁻¹ := eq_inv_of_mul_eq_one_right hddK
  have hsK : ι s = -(ι z' * ι d) * (ι e)⁻¹ := by rw [hs, map_mul, map_neg, map_mul, he'K]
  have E : C + (X₁ - ι x₂) * ι u₃ = 0 := by
    rw [hC, hℓ, hu₁, hu₃, hwK]
    simp only [map_mul, map_sub, map_pow, hd'K, hsK]
    rw [hsK] at hs0
    field_simp
    ring
  have hx₃ : (curveK K W).addX X₁ (ι x₂) ℓ = ι (x₂ + u₃) := by
    have h3 : (X₁ - ι x₂) * (B - (X₁ - ι x₂) - ι u₃) = 0 := by linear_combination R' - E
    have h4 := sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hX₂))
    rw [WeierstrassCurve.Affine.addX, map_add]
    rw [hB] at h4
    linear_combination h4
  have ht : ℓ * ι u₃ = ι t₃ := by
    rw [hℓ, hu₃, ht₃]
    simp only [map_mul, map_sub, map_pow, map_neg, hd'K, hsK]
    rw [hsK] at hs0
    field_simp
  have hy₃ : (curveK K W).addY X₁ (ι x₂) Y₁ ℓ =
      ι (-(y₂ + t₃) - W.a₁ * (x₂ + u₃) - W.a₃) := by
    rw [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY, hx₃,
      WeierstrassCurve.Affine.negY, hline]
    simp only [map_sub, map_neg, map_add, map_mul, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
    rw [← ht]
    ring
  have h₃ := WeierstrassCurve.Affine.nonsingular_add h₁ h₂ (fun h => hX₂ h.1)
  rw [hslope, hx₃, hy₃] at h₃
  refine ⟨x₂ + u₃, -(y₂ + t₃) - W.a₁ * (x₂ + u₃) - W.a₃, h₃, ?_, ?_, ?_⟩
  · rw [WeierstrassCurve.Affine.Point.add_of_X_ne hX₂, WeierstrassCurve.Affine.Point.some.injEq,
      hslope]
    exact ⟨hx₃, hy₃⟩
  · have hu₃m : u₃ ∈ maximalIdeal 𝒪 := by
      rw [hu₃]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
        (Ideal.mul_mem_left _ _ hzm)))
    rw [map_add, residue_eq_zero_of_mem hu₃m, add_zero]
  · have hu₃m : u₃ ∈ maximalIdeal 𝒪 := by
      rw [hu₃]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
        (Ideal.mul_mem_left _ _ hzm)))
    have hsm : s ∈ maximalIdeal 𝒪 := by
      rw [hs]; exact Ideal.mul_mem_right _ _ ((Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ hzm))
    have hρe : ρ e = 1 := by
      rw [he, map_add, map_one, map_mul, residue_eq_zero_of_mem hwm, mul_zero, add_zero]
    have hρd : ρ d = 1 := by
      rw [hd, map_sub, map_one, map_mul, map_mul, map_pow, residue_eq_zero_of_mem hzm]
      simp
    have hρd' : ρ d' = 1 := by
      have := congrArg ρ hdd
      rwa [map_mul, hρd, one_mul, map_one] at this
    have hρv : ρ v = 1 := residue_vVal W hzm
    have hρt : ρ t₃ = -ρ Fy := by
      rw [ht₃]
      simp only [map_mul, map_neg, map_sub, map_pow, residue_eq_zero_of_mem hsm, hρv, hρe, hρd']
      ring
    rw [map_sub, map_sub, map_neg, map_add, hρt, hFy]
    have h2ρ : ρ (2 : 𝒪) = 2 := map_ofNat _ 2
    simp only [map_add, map_mul, h2ρ, residue_eq_zero_of_mem hu₃m, add_zero]
    ring

end Sum

section Reduction

variable [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [(W.map (algebraMap 𝒪 K)).IsElliptic]

open Classical in

def intPart (X : K) : 𝒪 := if h : X ∈ Set.range (algebraMap 𝒪 K) then h.choose else 0

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  [(W.map (algebraMap 𝒪 K)).IsElliptic] in
theorem intPart_algebraMap (x : 𝒪) : intPart K (algebraMap 𝒪 K x) = x := by
  have h : algebraMap 𝒪 K x ∈ Set.range (algebraMap 𝒪 K) := ⟨x, rfl⟩
  rw [intPart, dif_pos h]
  exact IsFractionRing.injective 𝒪 K h.choose_spec

open Classical in

def reducePoint : (curveK K W).Point → (curveRed W).Point
  | .zero => 0
  | @WeierstrassCurve.Affine.Point.some _ _ _ X Y _ =>
    if h : X ∈ Set.range (algebraMap 𝒪 K) ∧
        (curveRed W).Nonsingular (residue 𝒪 (intPart K X)) (residue 𝒪 (intPart K Y)) then
      .some _ _ h.2
    else 0

omit [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [(W.map (algebraMap 𝒪 K)).IsElliptic]
  [IsFractionRing 𝒪 K] in
theorem reducePoint_zero : reducePoint K W 0 = 0 := rfl

omit [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [(W.map (algebraMap 𝒪 K)).IsElliptic] in
theorem reducePoint_some_integral {x y : 𝒪}
    (h : (curveK K W).Nonsingular (algebraMap 𝒪 K x) (algebraMap 𝒪 K y))
    (n : (curveRed W).Nonsingular (residue 𝒪 x) (residue 𝒪 y)) :
    reducePoint K W (.some _ _ h) = .some _ _ n := by
  have hn : (curveRed W).Nonsingular (residue 𝒪 (intPart K (algebraMap 𝒪 K x)))
      (residue 𝒪 (intPart K (algebraMap 𝒪 K y))) := by
    rwa [intPart_algebraMap, intPart_algebraMap]
  rw [reducePoint, dif_pos ⟨⟨x, rfl⟩, hn⟩, WeierstrassCurve.Affine.Point.some.injEq,
    intPart_algebraMap, intPart_algebraMap]
  exact ⟨rfl, rfl⟩

omit [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [(W.map (algebraMap 𝒪 K)).IsElliptic]
  [IsFractionRing 𝒪 K] in
theorem reducePoint_some_notMem {X Y : K} (h : (curveK K W).Nonsingular X Y)
    (hX : X ∉ Set.range (algebraMap 𝒪 K)) : reducePoint K W (.some _ _ h) = 0 := by
  rw [reducePoint, dif_neg (fun h' => hX h'.1)]

omit [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [(W.map (algebraMap 𝒪 K)).IsElliptic] in

theorem point_cases (P : (curveK K W).Point) :
    P = 0 ∨ (∃ (X Y : K) (h : (curveK K W).Nonsingular X Y), P = .some _ _ h ∧
      X ∉ Set.range (algebraMap 𝒪 K)) ∨
    ∃ (x y : 𝒪) (h : (curveK K W).Nonsingular (algebraMap 𝒪 K x) (algebraMap 𝒪 K y)),
      P = .some _ _ h := by
  cases P with
  | zero => exact Or.inl rfl
  | @some X Y h =>
    by_cases hX : X ∈ Set.range (algebraMap 𝒪 K)
    · obtain ⟨x, rfl⟩ := hX
      obtain ⟨y, rfl⟩ := exists_y_of_equation K W h.1
      exact Or.inr (Or.inr ⟨x, y, h, rfl⟩)
    · exact Or.inr (Or.inl ⟨X, Y, h, rfl, hX⟩)

def E0Set : Set (curveK K W).Point :=
  {P | ∀ (x y : 𝒪) (h : (curveK K W).Nonsingular (algebraMap 𝒪 K x) (algebraMap 𝒪 K y)),
    P = .some _ _ h → (curveRed W).Nonsingular (residue 𝒪 x) (residue 𝒪 y)}

omit [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [(W.map (algebraMap 𝒪 K)).IsElliptic] in
theorem mem_E0Set_some_integral {x y : 𝒪}
    (h : (curveK K W).Nonsingular (algebraMap 𝒪 K x) (algebraMap 𝒪 K y))
    (n : (curveRed W).Nonsingular (residue 𝒪 x) (residue 𝒪 y)) :
    WeierstrassCurve.Affine.Point.some _ _ h ∈ E0Set K W := by
  intro x' y' h' hP
  rw [WeierstrassCurve.Affine.Point.some.injEq] at hP
  rw [← IsFractionRing.injective 𝒪 K hP.1, ← IsFractionRing.injective 𝒪 K hP.2]
  exact n

omit [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [(W.map (algebraMap 𝒪 K)).IsElliptic]
  [IsFractionRing 𝒪 K] in
theorem mem_E0Set_some_notMem {X Y : K} (h : (curveK K W).Nonsingular X Y)
    (hX : X ∉ Set.range (algebraMap 𝒪 K)) :
    WeierstrassCurve.Affine.Point.some _ _ h ∈ E0Set K W := by
  intro x y h' hP
  rw [WeierstrassCurve.Affine.Point.some.injEq] at hP
  exact absurd ⟨x, hP.1.symm⟩ hX

omit [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [(W.map (algebraMap 𝒪 K)).IsElliptic]
  [IsFractionRing 𝒪 K] in
theorem zero_mem_E0Set : (0 : (curveK K W).Point) ∈ E0Set K W := by
  intro x y h hP
  exact absurd hP.symm (WeierstrassCurve.Affine.Point.some_ne_zero h)

variable [DecidableEq K] [DecidableEq (ResidueField 𝒪)]

omit [IsAdicComplete (maximalIdeal 𝒪) 𝒪] [(W.map (algebraMap 𝒪 K)).IsElliptic] in

theorem add_mem_and_reduce_of_exists {P Q : (curveK K W).Point}
    (H : ∃ (x₃ y₃ : 𝒪) (h₃ : (curveK K W).Nonsingular (algebraMap 𝒪 K x₃) (algebraMap 𝒪 K y₃))
      (n₃ : (curveRed W).Nonsingular (residue 𝒪 x₃) (residue 𝒪 y₃)),
      P + Q = .some _ _ h₃ ∧ reducePoint K W P + reducePoint K W Q = .some _ _ n₃) :
    P + Q ∈ E0Set K W ∧ reducePoint K W (P + Q) = reducePoint K W P + reducePoint K W Q := by
  obtain ⟨x₃, y₃, h₃, n₃, e, e'⟩ := H
  rw [e, e', reducePoint_some_integral K W h₃ n₃]
  exact ⟨mem_E0Set_some_integral K W h₃ n₃, rfl⟩

theorem add_mem_and_reduce {P Q : (curveK K W).Point} (hP : P ∈ E0Set K W)
    (hQ : Q ∈ E0Set K W) :
    P + Q ∈ E0Set K W ∧ reducePoint K W (P + Q) = reducePoint K W P + reducePoint K W Q := by
  rcases point_cases K W P with rfl | ⟨X₁, Y₁, h₁, rfl, hX₁⟩ | ⟨x₁, y₁, h₁, rfl⟩
  · rw [zero_add, reducePoint_zero, zero_add]; exact ⟨hQ, rfl⟩
  ·
    rcases point_cases K W Q with rfl | ⟨X₂, Y₂, h₂, rfl, hX₂⟩ | ⟨x₂, y₂, h₂, rfl⟩
    · rw [add_zero, reducePoint_zero, add_zero]; exact ⟨hP, rfl⟩
    · have h1 : WeierstrassCurve.Affine.Point.some _ _ h₁ ∈ E1 K W := by
        intro x y h hP'
        rw [WeierstrassCurve.Affine.Point.some.injEq] at hP'
        rw [← hP'.1]; exact hX₁
      have h2 : WeierstrassCurve.Affine.Point.some _ _ h₂ ∈ E1 K W := by
        intro x y h hP'
        rw [WeierstrassCurve.Affine.Point.some.injEq] at hP'
        rw [← hP'.1]; exact hX₂
      have h12 := (E1 K W).add_mem h1 h2
      rw [reducePoint_some_notMem K W h₁ hX₁, reducePoint_some_notMem K W h₂ hX₂, add_zero]
      rcases point_cases K W (WeierstrassCurve.Affine.Point.some _ _ h₁ +
          WeierstrassCurve.Affine.Point.some _ _ h₂) with h0 | ⟨X, Y, h, hS, hX⟩ | ⟨x, y, h, hS⟩
      · rw [h0]; exact ⟨zero_mem_E0Set K W, rfl⟩
      · rw [hS]; exact ⟨mem_E0Set_some_notMem K W h hX, reducePoint_some_notMem K W h hX⟩
      · rw [hS] at h12
        exact absurd ⟨x, rfl⟩ (h12 _ _ h rfl)
    · have n₂ := hQ x₂ y₂ h₂ rfl
      obtain ⟨x₃, y₃, h₃, e, hx, hy⟩ := add_of_notMem_range K W h₁ hX₁ h₂
      refine add_mem_and_reduce_of_exists K W ⟨x₃, y₃, h₃, hx ▸ hy ▸ n₂, e, ?_⟩
      rw [reducePoint_some_notMem K W h₁ hX₁, zero_add, reducePoint_some_integral K W h₂ n₂,
        WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hx.symm, hy.symm⟩
  · have n₁ := hP x₁ y₁ h₁ rfl
    rcases point_cases K W Q with rfl | ⟨X₂, Y₂, h₂, rfl, hX₂⟩ | ⟨x₂, y₂, h₂, rfl⟩
    · rw [add_zero, reducePoint_zero, add_zero]; exact ⟨hP, rfl⟩
    · obtain ⟨x₃, y₃, h₃, e, hx, hy⟩ := add_of_notMem_range K W h₂ hX₂ h₁
      rw [add_comm] at e
      refine add_mem_and_reduce_of_exists K W ⟨x₃, y₃, h₃, hx ▸ hy ▸ n₁, e, ?_⟩
      rw [reducePoint_some_notMem K W h₂ hX₂, add_zero, reducePoint_some_integral K W h₁ n₁,
        WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨hx.symm, hy.symm⟩
    · have n₂ := hQ x₂ y₂ h₂ rfl
      rw [reducePoint_some_integral K W h₁ n₁, reducePoint_some_integral K W h₂ n₂]
      by_cases hx : residue 𝒪 x₁ = residue 𝒪 x₂
      · by_cases hy : residue 𝒪 y₁ = (curveRed W).negY (residue 𝒪 x₂) (residue 𝒪 y₂)
        · rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hx hy]
          rcases add_of_residue_neg K W h₁ h₂ n₁ n₂ hx hy with h0 | ⟨X, Y, h, hS, hX⟩
          · rw [h0]; exact ⟨zero_mem_E0Set K W, rfl⟩
          · rw [hS]; exact ⟨mem_E0Set_some_notMem K W h hX, reducePoint_some_notMem K W h hX⟩
        · have hy' : residue 𝒪 y₁ = residue 𝒪 y₂ := by
            rcases WeierstrassCurve.Affine.Y_eq_of_X_eq n₁.1 n₂.1 hx with h | h
            · exact h
            · exact absurd h hy
          have hD : residue 𝒪 (y₁ + y₂ + W.a₁ * x₁ + W.a₃) ≠ 0 := by
            intro h0; apply hy
            rw [map_add, map_add, map_add, map_mul] at h0
            simp only [WeierstrassCurve.Affine.negY, WeierstrassCurve.map_a₁,
              WeierstrassCurve.map_a₃, ← hx]
            linear_combination h0
          obtain ⟨x₃, y₃, h₃, n₃, e, e'⟩ := add_of_residue_eq K W h₁ h₂ n₁ n₂ hx hy' hD
          rw [e, e', reducePoint_some_integral K W h₃ n₃]
          exact ⟨mem_E0Set_some_integral K W h₃ n₃, rfl⟩
      · obtain ⟨x₃, y₃, h₃, n₃, e, e'⟩ := add_of_residue_X_ne K W h₁ h₂ n₁ n₂ hx
        rw [e, e', reducePoint_some_integral K W h₃ n₃]
        exact ⟨mem_E0Set_some_integral K W h₃ n₃, rfl⟩

omit [DecidableEq K] [DecidableEq (ResidueField 𝒪)] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  [(W.map (algebraMap 𝒪 K)).IsElliptic] in

theorem neg_mem_and_reduce {P : (curveK K W).Point} (hP : P ∈ E0Set K W) :
    -P ∈ E0Set K W ∧ reducePoint K W (-P) = -reducePoint K W P := by
  rcases point_cases K W P with rfl | ⟨X, Y, h, rfl, hX⟩ | ⟨x, y, h, rfl⟩
  · exact ⟨zero_mem_E0Set K W, rfl⟩
  · rw [WeierstrassCurve.Affine.Point.neg_some, reducePoint_some_notMem K W h hX,
      reducePoint_some_notMem K W _ hX]
    exact ⟨mem_E0Set_some_notMem K W _ hX, rfl⟩
  · have n := hP x y h rfl
    have hyK : (curveK K W).negY (algebraMap 𝒪 K x) (algebraMap 𝒪 K y) =
        algebraMap 𝒪 K (W.toAffine.negY x y) := WeierstrassCurve.Affine.map_negY _ _ _
    have hyk : (curveRed W).negY (residue 𝒪 x) (residue 𝒪 y) =
        residue 𝒪 (W.toAffine.negY x y) := WeierstrassCurve.Affine.map_negY _ _ _
    have h' : (curveK K W).Nonsingular (algebraMap 𝒪 K x)
        (algebraMap 𝒪 K (W.toAffine.negY x y)) :=
      hyK ▸ (WeierstrassCurve.Affine.nonsingular_neg _ _).2 h
    have n' : (curveRed W).Nonsingular (residue 𝒪 x) (residue 𝒪 (W.toAffine.negY x y)) :=
      hyk ▸ (WeierstrassCurve.Affine.nonsingular_neg _ _).2 n
    have e : -WeierstrassCurve.Affine.Point.some _ _ h =
        WeierstrassCurve.Affine.Point.some _ _ h' := by
      rw [WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
      exact ⟨rfl, hyK⟩
    rw [e, reducePoint_some_integral K W h' n', reducePoint_some_integral K W h n,
      WeierstrassCurve.Affine.Point.neg_some, WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨mem_E0Set_some_integral K W h' n', rfl, hyk.symm⟩

def E0 : AddSubgroup (curveK K W).Point where
  carrier := E0Set K W
  zero_mem' := zero_mem_E0Set K W
  add_mem' hP hQ := (add_mem_and_reduce K W hP hQ).1
  neg_mem' hP := (neg_mem_and_reduce K W hP).1

theorem mem_E0_iff (P : (curveK K W).Point) : P ∈ E0 K W ↔ P ∈ E0Set K W := Iff.rfl

def reduceHom : E0 K W →+ (curveRed W).Point where
  toFun P := reducePoint K W P
  map_zero' := reducePoint_zero K W
  map_add' P Q := (add_mem_and_reduce K W P.2 Q.2).2

theorem reduceHom_apply (P : E0 K W) : reduceHom K W P = reducePoint K W P := rfl

theorem E1_le_E0 : E1 K W ≤ E0 K W := by
  intro P hP x y h hP'
  rw [hP'] at hP
  exact absurd ⟨x, rfl⟩ (hP _ _ h rfl)

theorem reduceHom_eq_zero_iff (P : E0 K W) :
    reduceHom K W P = 0 ↔ (P : (curveK K W).Point) ∈ E1 K W := by
  obtain ⟨P, hP⟩ := P
  rw [reduceHom_apply]
  rcases point_cases K W P with rfl | ⟨X, Y, h, rfl, hX⟩ | ⟨x, y, h, rfl⟩
  · exact ⟨fun _ => (E1 K W).zero_mem, fun _ => rfl⟩
  · refine ⟨fun _ => ?_, fun _ => reducePoint_some_notMem K W h hX⟩
    intro x y h' hP'
    rw [WeierstrassCurve.Affine.Point.some.injEq] at hP'
    rw [← hP'.1]; exact hX
  · have n := hP x y h rfl
    rw [reducePoint_some_integral K W h n]
    refine ⟨fun h0 => absurd h0 (WeierstrassCurve.Affine.Point.some_ne_zero n), fun h1 => ?_⟩
    exact absurd ⟨x, rfl⟩ (h1 _ _ h rfl)

theorem ker_reduceHom : (reduceHom K W).ker = (E1 K W).addSubgroupOf (E0 K W) := by
  ext P
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, reduceHom_eq_zero_iff]

theorem reduceHom_surjective : Function.Surjective (reduceHom K W) := by
  intro Q
  cases Q with
  | zero => exact ⟨0, (reduceHom K W).map_zero⟩
  | @some xr yr n =>
  obtain ⟨x₀, rfl⟩ := residue_surjective xr
  obtain ⟨y₀, rfl⟩ := residue_surjective yr
  have hE := n.1
  rw [WeierstrassCurve.Affine.equation_iff] at hE
  simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at hE
  have hE0 : y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ - (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) ∈
      maximalIdeal 𝒪 := by
    rw [← residue_eq_zero_iff]
    simp only [map_sub, map_add, map_mul, map_pow]
    rw [hE, sub_self]
  have hmk : ∀ a : 𝒪, IsUnit a → IsUnit (Ideal.Quotient.mk (maximalIdeal 𝒪) a) :=
    fun a ha => ha.map _

  obtain ⟨x, y, hxy, hx, hy⟩ : ∃ x y : 𝒪, W.toAffine.Equation x y ∧ residue 𝒪 x = residue 𝒪 x₀ ∧
      residue 𝒪 y = residue 𝒪 y₀ := by
    rcases nonsingular_residue_iff W n with hFx | hFy
    ·
      set g : Polynomial 𝒪 := Polynomial.X ^ 3 + Polynomial.C W.a₂ * Polynomial.X ^ 2 +
        Polynomial.C (W.a₄ - W.a₁ * y₀) * Polynomial.X +
        Polynomial.C (W.a₆ - y₀ ^ 2 - W.a₃ * y₀) with hg
      have hgm : g.Monic := by rw [hg]; monicity!
      have hg0 : g.eval x₀ ∈ maximalIdeal 𝒪 := by
        have : g.eval x₀ = -(y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ -
            (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆)) := by
          rw [hg]; simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
            Polynomial.eval_C, Polynomial.eval_X]; ring
        rw [this]; exact (Ideal.neg_mem_iff _).2 hE0
      have hg1 : IsUnit (g.derivative.eval x₀) := by
        have : g.derivative.eval x₀ = -(W.a₁ * y₀ - (3 * x₀ ^ 2 + 2 * W.a₂ * x₀ + W.a₄)) := by
          rw [hg]
          simp only [Polynomial.derivative_add, Polynomial.derivative_mul, Polynomial.derivative_C,
            Polynomial.derivative_X_pow, Polynomial.derivative_X, Polynomial.eval_add,
            Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
            Polynomial.eval_zero, Polynomial.eval_one]
          push_cast; ring
        rw [this]; exact (isUnit_of_residue_ne_zero hFx).neg
      obtain ⟨x, hxr, hxm⟩ := HenselianRing.is_henselian g hgm x₀ hg0 (hmk _ hg1)
      refine ⟨x, y₀, ?_, ?_, rfl⟩
      · rw [WeierstrassCurve.Affine.equation_iff]
        have := hxr.eq_zero
        rw [hg] at this
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_C, Polynomial.eval_X] at this
        linear_combination -this
      · rw [← sub_eq_zero, ← map_sub]; exact (residue_eq_zero_iff _).2 hxm
    ·
      set f : Polynomial 𝒪 := Polynomial.X ^ 2 + Polynomial.C (W.a₁ * x₀ + W.a₃) * Polynomial.X -
        Polynomial.C (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) with hf
      have hfm : f.Monic := by rw [hf]; monicity!
      have hf0 : f.eval y₀ ∈ maximalIdeal 𝒪 := by
        have : f.eval y₀ = y₀ ^ 2 + W.a₁ * x₀ * y₀ + W.a₃ * y₀ -
            (x₀ ^ 3 + W.a₂ * x₀ ^ 2 + W.a₄ * x₀ + W.a₆) := by
          rw [hf]; simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]; ring
        rw [this]; exact hE0
      have hf1 : IsUnit (f.derivative.eval y₀) := by
        have : f.derivative.eval y₀ = 2 * y₀ + W.a₁ * x₀ + W.a₃ := by
          rw [hf]
          simp only [Polynomial.derivative_sub, Polynomial.derivative_add,
            Polynomial.derivative_mul,
            Polynomial.derivative_C, Polynomial.derivative_X_pow, Polynomial.derivative_X,
            Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
            Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero, Polynomial.eval_one]
          push_cast; ring
        rw [this]; exact isUnit_of_residue_ne_zero hFy
      obtain ⟨y, hyr, hym⟩ := HenselianRing.is_henselian f hfm y₀ hf0 (hmk _ hf1)
      refine ⟨x₀, y, ?_, rfl, ?_⟩
      · rw [WeierstrassCurve.Affine.equation_iff]
        have := hyr.eq_zero
        rw [hf] at this
        simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X] at this
        linear_combination this
      · rw [← sub_eq_zero, ← map_sub]; exact (residue_eq_zero_iff _).2 hym
  have hK : (curveK K W).Equation (algebraMap 𝒪 K x) (algebraMap 𝒪 K y) := by
    rw [WeierstrassCurve.Affine.equation_iff] at hxy ⊢
    have := congrArg (algebraMap 𝒪 K) hxy
    simpa using this
  have h := WeierstrassCurve.Affine.equation_iff_nonsingular.mp hK
  have n' : (curveRed W).Nonsingular (residue 𝒪 x) (residue 𝒪 y) := by rw [hx, hy]; exact n
  refine ⟨⟨_, mem_E0Set_some_integral K W h n'⟩, ?_⟩
  rw [reduceHom_apply, reducePoint_some_integral K W h n', WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨hx, hy⟩

def e0QuotientEquiv : E0 K W ⧸ (E1 K W).addSubgroupOf (E0 K W) ≃+ (curveRed W).Point :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_reduceHom K W).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (reduceHom_surjective K W))

end Reduction

end

end GroundTheory.Arith.Abelian
