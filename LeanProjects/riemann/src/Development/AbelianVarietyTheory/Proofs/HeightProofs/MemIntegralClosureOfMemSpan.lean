import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement

open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

namespace PlaceExt

theorem wt_eq_of_min {a p : WithTop ℤ} (h : ∀ m : ℕ, min a (m : ℤ) = min p (m : ℤ)) : a = p := by
  have h' := h ((a.untopD 0).natAbs + (p.untopD 0).natAbs + 1)
  induction a using WithTop.recTopCoe <;> induction p using WithTop.recTopCoe <;>
    simp only [WithTop.untopD_top, WithTop.untopD_coe, le_top, min_eq_right, ← WithTop.coe_min,
      WithTop.coe_inj] at h' ⊢ <;> omega

theorem wt_add_of_min {a b c : WithTop ℤ} (h : ∀ m : ℕ, ∃ p q r : WithTop ℤ,
    min a (m : ℤ) = min p (m : ℤ) ∧ min b (m : ℤ) = min q (m : ℤ) ∧
      min c (m : ℤ) = min r (m : ℤ) ∧ min p q ≤ r) : min a b ≤ c := by
  obtain ⟨p, q, r, h1, h2, h3, h4⟩ := h ((c.untopD 0).natAbs + 1)
  induction c using WithTop.recTopCoe with
  | top => exact le_top
  | coe c =>
    have hc : (c : WithTop ℤ) < ((((c.natAbs + 1 : ℕ) : ℤ)) : WithTop ℤ) := by
      rw [WithTop.coe_lt_coe]; omega
    simp only [WithTop.untopD_coe] at h1 h2 h3
    generalize ((((c.natAbs + 1 : ℕ) : ℤ)) : WithTop ℤ) = M at *
    generalize (c : WithTop ℤ) = c' at *
    grind

theorem wt_mul_of_min {a b c : WithTop ℤ} (n : ℕ) (h : ∀ m : ℕ, ∃ p q : WithTop ℤ,
    min a ((m + n : ℕ) : ℤ) = min p ((m + n : ℕ) : ℤ) ∧
      min b ((m + n : ℕ) : ℤ) = min q ((m + n : ℕ) : ℤ) ∧
      min c (m : ℤ) = min (p + q) (m : ℤ)) : c = a + b := by
  obtain ⟨p, q, h1, h2, h3⟩ :=
    h ((a.untopD 0).natAbs + (b.untopD 0).natAbs + (c.untopD 0).natAbs + 1)
  induction a using WithTop.recTopCoe <;> induction b using WithTop.recTopCoe <;>
    induction c using WithTop.recTopCoe <;> induction p using WithTop.recTopCoe <;>
    induction q using WithTop.recTopCoe <;>
    simp only [WithTop.untopD_top, WithTop.untopD_coe, le_top, min_eq_right, ← WithTop.coe_min,
      WithTop.coe_inj, top_add, add_top, ← WithTop.coe_add, WithTop.top_ne_coe,
      WithTop.coe_ne_top] at h1 h2 h3 ⊢ <;> omega

section Abstract

variable {L A : Type*} [Field L] [CommRing A]

theorem le_val_pow_mul (u : AddValuation A (WithTop ℤ)) {t b : A} (ht : 1 ≤ u t) (hb : 0 ≤ u b)
    (m : ℕ) : ((m : ℤ) : WithTop ℤ) ≤ u (t ^ m * b) := by
  induction m with
  | zero => simpa using hb
  | succ m ih =>
    rw [pow_succ', mul_assoc, AddValuation.map_mul]
    calc (((m + 1 : ℕ) : ℤ) : WithTop ℤ) = 1 + ((m : ℤ) : WithTop ℤ) := by
          push_cast; exact add_comm _ _
      _ ≤ _ := add_le_add ht ih

theorem min_eq_of_le_sub (u : AddValuation A (WithTop ℤ)) {x y : A} {M : WithTop ℤ}
    (h : M ≤ u (x - y)) : min (u x) M = min (u y) M := by
  have h1 : min (u (x - y)) (u y) ≤ u x := by simpa using u.map_add (x - y) y
  have h2 : min (u (x - y)) (u x) ≤ u y := by
    have := u.map_add (y - x) x
    rw [u.map_sub_swap y x] at this
    simpa using this
  grind

variable (ι : L →+* A) (S : Subring A) (π : L) (w : AddValuation L (WithTop ℤ))

theorem ext_unique (hw : 1 ≤ w π)
    (happ : ∀ (x : A) (m : ℕ), ∃ l, ∃ b ∈ S, x - ι l = ι π ^ m * b)
    (u u' : AddValuation A (WithTop ℤ)) (hu : ∀ l, u (ι l) = w l) (hu' : ∀ l, u' (ι l) = w l)
    (h0 : ∀ b ∈ S, 0 ≤ u b) (h0' : ∀ b ∈ S, 0 ≤ u' b) : u = u' := by
  apply AddValuation.ext
  intro x
  apply wt_eq_of_min
  intro m
  obtain ⟨l, b, hb, hx⟩ := happ x m
  rw [min_eq_of_le_sub u (y := ι l), min_eq_of_le_sub u' (y := ι l), hu, hu']
  · rw [hx]; exact le_val_pow_mul u' (by rwa [hu']) (h0' b hb) m
  · rw [hx]; exact le_val_pow_mul u (by rwa [hu]) (h0 b hb) m

theorem exists_ext (hπ0 : π ≠ 0) (hπS : ι π ∈ S) (hw : 1 ≤ w π)
    (hS : ∀ l, ι l ∈ S → 0 ≤ w l)
    (happ : ∀ (x : A) (m : ℕ), ∃ l, ∃ b ∈ S, x - ι l = ι π ^ m * b)
    (hden : ∀ x : A, ∃ n : ℕ, ι π ^ n * x ∈ S) :
    ∃ u : AddValuation A (WithTop ℤ), (∀ l, u (ι l) = w l) ∧ ∀ b ∈ S, 0 ≤ u b := by
  classical
  let C : A → ℕ → L → Prop := fun x m l => ∃ b ∈ S, x - ι l = ι π ^ m * b
  have hmono : ∀ x m m' l, m ≤ m' → C x m' l → C x m l := by
    rintro x m m' l hm ⟨b, hb, h⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    exact ⟨ι π ^ k * b, S.mul_mem (S.pow_mem hπS k) hb, by rw [h]; ring⟩
  have hcl : ∀ x m l l', C x m l → C x m l' → min (w l) (m : ℤ) = min (w l') (m : ℤ) := by
    rintro x m l l' ⟨b, hb, h⟩ ⟨b', hb', h'⟩
    apply min_eq_of_le_sub
    have hp : π ^ m ≠ 0 := pow_ne_zero _ hπ0
    have e1 : l - l' = π ^ m * ((π ^ m)⁻¹ * (l - l')) := by field_simp
    rw [e1]
    apply le_val_pow_mul w hw
    apply hS
    have e2 : ι ((π ^ m)⁻¹ * (l - l')) = b' - b := by
      have : ι (l - l') = ι (π ^ m) * (b' - b) := by
        rw [map_sub, map_pow]; linear_combination h' - h
      rw [map_mul, this, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hp, map_one, one_mul]
    rw [e2]
    exact S.sub_mem hb' hb
  let f : A → WithTop ℤ := fun x =>
    if h : ∃ ml : ℕ × L, C x ml.1 ml.2 ∧ w ml.2 < (ml.1 : ℤ) then w h.choose.2 else ⊤
  have hf : ∀ x m l, C x m l → min (f x) (m : ℤ) = min (w l) (m : ℤ) := by
    intro x m l hC
    by_cases h : ∃ ml : ℕ × L, C x ml.1 ml.2 ∧ w ml.2 < (ml.1 : ℤ)
    · have e : f x = w h.choose.2 := dif_pos h
      obtain ⟨h1, h2⟩ := h.choose_spec
      rw [e]
      generalize h.choose = ml at h1 h2
      obtain ⟨m', l'⟩ := ml
      rcases le_total m m' with hm | hm
      · exact hcl x m _ _ (hmono x m m' l' hm h1) hC
      · have h3 := hcl x m' _ _ h1 (hmono x m' m l hm hC)
        dsimp only at h2 ⊢
        have : w l' = w l := by grind
        rw [this]
    · have e : f x = ⊤ := dif_neg h
      have : ¬ w l < (m : ℤ) := fun h' => h ⟨(m, l), hC, h'⟩
      rw [e, min_eq_right le_top, min_eq_right (not_lt.1 this)]
  have hι : ∀ l, f (ι l) = w l := fun l =>
    wt_eq_of_min fun m => hf _ m l ⟨0, S.zero_mem, by simp⟩
  refine ⟨AddValuation.of f ?_ ?_ ?_ ?_, hι, ?_⟩
  · simpa using hι 0
  · simpa using hι 1
  · intro x y
    apply wt_add_of_min
    intro m
    obtain ⟨l, b, hb, h⟩ := happ x m
    obtain ⟨l', b', hb', h'⟩ := happ y m
    refine ⟨w l, w l', w (l + l'), hf x m l ⟨b, hb, h⟩, hf y m l' ⟨b', hb', h'⟩,
      hf _ m _ ⟨b + b', S.add_mem hb hb', ?_⟩, w.map_add _ _⟩
    rw [map_add]; linear_combination h + h'
  · intro x y
    obtain ⟨n1, hx⟩ := hden x
    obtain ⟨n2, hy⟩ := hden y
    apply wt_mul_of_min (n1 + n2)
    intro m
    obtain ⟨l, b, hb, h⟩ := happ x (m + (n1 + n2))
    obtain ⟨l', b', hb', h'⟩ := happ y (m + (n1 + n2))
    refine ⟨w l, w l', hf x _ l ⟨b, hb, h⟩, hf y _ l' ⟨b', hb', h'⟩, ?_⟩
    rw [← w.map_mul]
    refine hf _ m _ ⟨ι π ^ n1 * b * (ι π ^ n2 * y) + ι π ^ n2 * b' * (ι π ^ n1 * x)
      - ι π ^ (m + 2 * (n1 + n2)) * b * b', ?_, ?_⟩
    · exact S.sub_mem (S.add_mem (S.mul_mem (S.mul_mem (S.pow_mem hπS _) hb) hy)
        (S.mul_mem (S.mul_mem (S.pow_mem hπS _) hb') hx))
        (S.mul_mem (S.mul_mem (S.pow_mem hπS _) hb) hb')
    · have e1 : ι l = x - ι π ^ (m + (n1 + n2)) * b := by linear_combination -h
      have e2 : ι l' = y - ι π ^ (m + (n1 + n2)) * b' := by linear_combination -h'
      rw [map_mul, e1, e2]; ring
  · intro b hb
    have := hf b 0 0 ⟨b, hb, by simp⟩
    simp only [AddValuation.map_zero, le_top, min_eq_right, min_eq_right_iff] at this
    simpa using this

end Abstract

section Rings

variable {R R' : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R']
  [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]

omit [IsLocalHom (algebraMap R R')] in
theorem maximalIdeal_eq_span
    (hmax : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R')
    {ϖ : R} (hϖ : Irreducible ϖ) :
    IsLocalRing.maximalIdeal R' = Ideal.span {algebraMap R R' ϖ} := by
  rw [← hmax, (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
    Set.image_singleton]

theorem exists_approx_base
    (hmax : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R')
    (hres : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')))
    {ϖ : R} (hϖ : Irreducible ϖ) (m : ℕ) (r : R') :
    ∃ (r₀ : R) (r₁ : R'), r = algebraMap R R' r₀ + algebraMap R R' ϖ ^ m * r₁ := by
  induction m with
  | zero => exact ⟨0, r, by simp⟩
  | succ m ih =>
    obtain ⟨r₀, r₁, h⟩ := ih
    obtain ⟨s, hs⟩ := hres (IsLocalRing.residue R' r₁)
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective s
    rw [IsLocalRing.ResidueField.map_residue] at hs
    have hm : r₁ - algebraMap R R' s ∈ IsLocalRing.maximalIdeal R' := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hs, sub_self]
    rw [maximalIdeal_eq_span hmax hϖ, Ideal.mem_span_singleton'] at hm
    obtain ⟨c, hc⟩ := hm
    refine ⟨r₀ + ϖ ^ m * s, c, ?_⟩
    rw [h, map_add, map_mul, map_pow]
    linear_combination (-(algebraMap R R' ϖ) ^ m) * hc

variable {F F' : Type} [Field F] [Algebra R F] [IsFractionRing R F] [Field F'] [Algebra R' F']
  [IsFractionRing R' F'] [Algebra F F'] [Algebra R F'] [IsScalarTower R F F']
  [IsScalarTower R R' F']

theorem isInteger_of_map {f : F} (r' : R') (h : algebraMap R' F' r' = algebraMap F F' f) :
    ∃ r : R, algebraMap R F r = f := by
  rcases ValuationRing.isInteger_or_isInteger R f with hf | ⟨r, hr⟩
  · exact hf
  by_cases hf0 : f = 0
  · exact ⟨0, by simp [hf0]⟩
  have h1 : algebraMap R R' r * r' = 1 := by
    apply IsFractionRing.injective R' F'
    rw [map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R F F', hr, h,
      ← map_mul, inv_mul_cancel₀ hf0, map_one, map_one]
  have hu : IsUnit r := isUnit_of_map_unit (algebraMap R R') r (IsUnit.of_mul_eq_one _ h1)
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  refine ⟨v, ?_⟩
  have h2 := congrArg (algebraMap R F) hv
  rw [map_mul, hr, map_one] at h2
  field_simp at h2
  exact h2

variable {L : Type} [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
  [Algebra R L] [IsScalarTower R F L]

theorem mem_integralClosure_of_mem_span (l : L)
    (hl : (1 : F') ⊗ₜ[F] l ∈ Submodule.span R'
      ((fun b : L => (1 : F') ⊗ₜ[F] b) '' (integralClosure R L : Set L))) :
    l ∈ integralClosure R L := by
  classical
  haveI := integralClosure.isDedekindDomain R F L
  haveI := integralClosure.isFractionRing_of_finite_extension (A := R) F L
  haveI : FaithfulSMul R L :=
    (faithfulSMul_iff_algebraMap_injective R L).2 (ValPl.algebraMap_OL_injective (F := F))
  haveI := IsIntegralClosure.module_free R F L (integralClosure R L)
  haveI := IsIntegralClosure.isLocalization R F L (integralClosure R L)
  let b := Module.Free.chooseBasis R (integralClosure R L)
  let bL := b.localizationLocalization F (nonZeroDivisors R) L
  let bA := Algebra.TensorProduct.basis F' bL
  have key : ∀ x ∈ Submodule.span R'
      ((fun b : L => (1 : F') ⊗ₜ[F] b) '' (integralClosure R L : Set L)),
      ∀ i, ∃ r' : R', algebraMap R' F' r' = bA.repr x i := by
    intro x hx i
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨algebraMap R R' (b.repr ⟨y, hy⟩ i), ?_⟩
      have := b.localizationLocalization_repr_algebraMap F (nonZeroDivisors R) L ⟨y, hy⟩ i
      simp only [bA, Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R F F', ← this]
      rfl
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨r, hr⟩ := hx
      obtain ⟨s, hs⟩ := hy
      exact ⟨r + s, by simp [hr, hs]⟩
    | smul a x _ hx =>
      obtain ⟨r, hr⟩ := hx
      refine ⟨a * r, ?_⟩
      rw [← IsScalarTower.algebraMap_smul F' a x, map_smul, Finsupp.smul_apply, map_mul, hr,
        smul_eq_mul]
  have hc : ∀ i, ∃ r : R, algebraMap R F r = bL.repr l i := by
    intro i
    obtain ⟨r', hr'⟩ := key _ hl i
    apply isInteger_of_map (F' := F') r'
    simpa only [bA, Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply]
      using hr'
  rw [← bL.linearCombination_repr l, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  obtain ⟨r, hr⟩ := hc i
  rw [← hr, IsScalarTower.algebraMap_smul]
  refine Subalgebra.smul_mem _ ?_ _
  simp only [bL, Module.Basis.localizationLocalization_apply]
  exact (b i).2

omit [IsDomain R] [IsDiscreteValuationRing R] [IsDomain R'] [IsDiscreteValuationRing R']
  [IsLocalHom (algebraMap R R')] [IsFractionRing R F] [IsFractionRing R' F']
  [FiniteDimensional F L] [Algebra.IsSeparable F L] in
theorem algebraMap_eq_one_tmul (r : R) :
    algebraMap R' (F' ⊗[F] L) (algebraMap R R' r) = (1 : F') ⊗ₜ[F] algebraMap R L r := by
  rw [Algebra.TensorProduct.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply R F F', IsScalarTower.algebraMap_apply R F L,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one (A := L),
    TensorProduct.smul_tmul]

end Rings

end PlaceExt

open PlaceExt in

theorem exists_unique_place_baseChange : ∀ (R R' F F' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [Module.Flat R R'] [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F] [Field F'] [Algebra R' F'] [IsFractionRing R' F'] [Algebra F F'] [Algebra R F'] [IsScalarTower R F F'] [IsScalarTower R R' F'], Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' → Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')) → ∀ (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] [Algebra.IsSeparable F L] [Algebra R L] [IsScalarTower R F L], (∀ x : F' ⊗[F] L, IsIntegral R' x ↔ x ∈ Submodule.span R' ((fun b : L => (1 : F') ⊗ₜ[F] b) '' (integralClosure R L : Set L))) → ∃ w' : ValPl.PlacesOver R L → AddValuation (F' ⊗[F] L) (WithTop ℤ), (∀ w (g : L), w' w ((1 : F') ⊗ₜ[F] g) = w.1 g) ∧ (∀ x : F' ⊗[F] L, IsIntegral R' x ↔ ∀ w, 0 ≤ w' w x) ∧ (∀ w (x : F' ⊗[F] L), 0 ≤ w' w x → ∃ g : L, 0 ≤ w.1 g ∧ 0 < w' w (x - (1 : F') ⊗ₜ[F] g)) ∧ ∀ (w : ValPl.PlacesOver R L) (u : AddValuation (F' ⊗[F] L) (WithTop ℤ)), (∀ g : L, u ((1 : F') ⊗ₜ[F] g) = w.1 g) → (∀ r : R', 0 ≤ u (algebraMap R' F' r ⊗ₜ[F] (1 : L))) → u = w' w := by
  intro R R' F F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmax hres L _ _ _ _ _ _ hB
  haveI := integralClosure.isDedekindDomain R F L
  haveI := integralClosure.isFractionRing_of_finite_extension (A := R) F L
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hϖ' : Irreducible (algebraMap R R' ϖ) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 (maximalIdeal_eq_span hmax hϖ)
  let ι : L →+* F' ⊗[F] L :=
    (Algebra.TensorProduct.includeRight : L →ₐ[F] F' ⊗[F] L).toRingHom
  have hι : ∀ l, ι l = (1 : F') ⊗ₜ[F] l := fun _ => rfl
  let S : Subring (F' ⊗[F] L) := (integralClosure R' (F' ⊗[F] L)).toSubring
  let π : L := algebraMap R L ϖ
  have halg : ∀ r : R, algebraMap R' (F' ⊗[F] L) (algebraMap R R' r) = ι (algebraMap R L r) :=
    fun r => algebraMap_eq_one_tmul r
  have hR'S : ∀ r : R', algebraMap R' (F' ⊗[F] L) r ∈ S := fun r => isIntegral_algebraMap
  have hπ0 : π ≠ 0 := fun h =>
    hϖ.ne_zero (ValPl.algebraMap_OL_injective (F := F) (L := L) (by rw [map_zero]; exact h))
  have hπS : ι π ∈ S := halg ϖ ▸ hR'S _
  have hw1 : ∀ w : ValPl.PlacesOver R L, 1 ≤ w.1 π := by
    intro w
    have h : 0 < w.1 π := ((w.2.2 ϖ).2).2 hϖ.not_isUnit
    generalize w.1 π = a at h
    induction a using WithTop.recTopCoe with
    | top => exact le_top
    | coe a =>
      have : 0 < a := by exact_mod_cast h
      exact_mod_cast (show (1 : ℤ) ≤ a by omega)
  have hS : ∀ (w : ValPl.PlacesOver R L) l, ι l ∈ S → 0 ≤ w.1 l := fun w l hl =>
    (HDiscVal.mem_integralClosure_iff R F l).1
      (mem_integralClosure_of_mem_span (R' := R') (F' := F') l ((hB _).1 hl)) w.1 w.2
  have hden : ∀ x, ∃ n : ℕ, ι π ^ n * x ∈ S := by
    intro x
    obtain ⟨⟨d, hd⟩, hx⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (nonZeroDivisors R') (Rₘ := F') x (Algebra.IsIntegral.isIntegral x)
    obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero hd) hϖ'
    refine ⟨n, ?_⟩
    have hx' : algebraMap R' _ d * x ∈ S := by
      rw [← Algebra.smul_def]; exact hx
    have := S.mul_mem (hR'S (v⁻¹ : R'ˣ)) hx'
    rwa [← mul_assoc, ← map_mul, hv, Units.inv_mul_cancel_left, map_pow, halg] at this
  have happS : ∀ (m : ℕ), ∀ x ∈ S, ∃ l, ∃ b ∈ S, x - ι l = ι π ^ m * b := by
    intro m x hx
    have hx' := (hB x).1 hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, -, rfl⟩ := hx
      exact ⟨y, 0, S.zero_mem, by simp [hι]⟩
    | zero => exact ⟨0, 0, S.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨l, b, hb, h⟩ := hx
      obtain ⟨l', b', hb', h'⟩ := hy
      refine ⟨l + l', b + b', S.add_mem hb hb', ?_⟩
      rw [map_add]; linear_combination h + h'
    | smul a x hxs hx =>
      obtain ⟨l, b, hb, h⟩ := hx
      obtain ⟨r₀, r₁, hr⟩ := exists_approx_base hmax hres hϖ m a
      refine ⟨algebraMap R L r₀ * l, ι (algebraMap R L r₀) * b + algebraMap R' _ r₁ * x,
        S.add_mem (S.mul_mem (halg r₀ ▸ hR'S _) hb) (S.mul_mem (hR'S _) ((hB x).2 hxs)), ?_⟩
      rw [Algebra.smul_def, hr, map_add, map_mul, map_pow, halg, halg, map_mul]
      linear_combination ι (algebraMap R L r₀) * h
  have happ : ∀ x (m : ℕ), ∃ l, ∃ b ∈ S, x - ι l = ι π ^ m * b := by
    intro x m
    obtain ⟨n, hn⟩ := hden x
    obtain ⟨l, b, hb, h⟩ := happS (n + m) _ hn
    refine ⟨(π ^ n)⁻¹ * l, b, hb, ?_⟩
    have h1 : ι ((π ^ n)⁻¹) * ι π ^ n = 1 := by
      rw [← map_pow ι, ← map_mul, inv_mul_cancel₀ (pow_ne_zero _ hπ0), map_one]
    rw [map_mul]
    linear_combination ι ((π ^ n)⁻¹) * h + (ι π ^ m * b - x) * h1
  choose w' hw' hw0 using fun w : ValPl.PlacesOver R L =>
    exists_ext ι S π w.1 hπ0 hπS (hw1 w) (hS w) happ hden
  have hnear : ∀ w x l (m : ℕ) b, b ∈ S → x - ι l = ι π ^ m * b → 0 ≤ w' w x → 0 ≤ w.1 l := by
    intro w x l m b hb h hx
    have h1 : 0 ≤ w' w (x - ι l) := h ▸ hw0 w _ (S.mul_mem (S.pow_mem hπS m) hb)
    have h2 := min_eq_of_le_sub (w' w) h1
    rw [min_eq_right hx, hw', eq_comm, min_eq_right_iff] at h2
    exact h2
  refine ⟨w', hw', fun x => ⟨fun hx w => hw0 w x hx, fun hx => ?_⟩, fun w x hx => ?_,
    fun w u hu hu0 => ?_⟩
  · obtain ⟨l, b, hb, h⟩ := happ x 0
    have hl : l ∈ integralClosure R L := (HDiscVal.mem_integralClosure_iff R F l).2
      fun w hw => hnear ⟨w, hw⟩ x l 0 b hb h (hx _)
    have hlS : ι l ∈ S := (hB _).2 (Submodule.subset_span ⟨l, hl, rfl⟩)
    have : x = ι l + b := by linear_combination h
    rw [this]
    exact S.add_mem hlS hb
  · obtain ⟨l, b, hb, h⟩ := happ x 1
    refine ⟨l, hnear w x l 1 b hb h hx, ?_⟩
    have := le_val_pow_mul (w' w) (t := ι π) (by rw [hw']; exact hw1 w) (hw0 w b hb) 1
    rw [← h] at this
    exact lt_of_lt_of_le (by norm_num) this
  · refine ext_unique ι S π w.1 (hw1 w) happ u (w' w) hu (hw' w) ?_ (hw0 w)
    intro x hx
    have hx' := (hB x).1 hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      rw [hu]
      exact (HDiscVal.mem_integralClosure_iff R F y).1 hy w.1 w.2
    | zero => simp
    | add x y _ _ hx hy => exact le_trans (le_min hx hy) (u.map_add x y)
    | smul a x _ hx =>
      rw [Algebra.smul_def, u.map_mul]
      exact add_nonneg (hu0 a) hx

end GlobalTheory
