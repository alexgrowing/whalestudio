import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.SmallExt
import Mathlib.RingTheory.Valuation.RankOne

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem dvd_pow_of {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {a b : A}
    (ha : ¬ IsUnit a) (hb : b ≠ 0) : ∃ n : ℕ, b ∣ a ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  by_cases ha0 : a = 0
  · exact ⟨1, by simp [ha0]⟩
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨m, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  have hk : k ≠ 0 := by
    rintro rfl
    exact ha (by simp)
  refine ⟨m, ?_⟩
  rw [Units.mul_left_dvd, mul_pow, ← pow_mul]
  exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (Nat.le_mul_of_pos_left m (Nat.pos_of_ne_zero hk))) _

private theorem arch {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (f : A →+* 𝔞.V) (hf : 𝔞.IsDvr f) : MulArchimedean 𝔞.V.ValueGroup := by
  classical
  refine ⟨fun x y hy => ?_⟩
  obtain ⟨a, rfl⟩ := 𝔞.V.valuation_surjective x
  obtain ⟨b, rfl⟩ := 𝔞.V.valuation_surjective y
  by_cases ha : 𝔞.V.valuation a ≤ 1
  · exact ⟨0, by simpa using ha⟩
  push_neg at ha
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  have hb0 : b ≠ 0 := by
    rintro rfl
    simp at hy
  have hai : 𝔞.V.valuation a⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ ha
  have hbi : 𝔞.V.valuation b⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hy
  have haV : a⁻¹ ∈ 𝔞.V := (𝔞.V.valuation_le_one_iff _).1 hai.le
  have hbV : b⁻¹ ∈ 𝔞.V := (𝔞.V.valuation_le_one_iff _).1 hbi.le
  obtain ⟨A', _, _, _, f', g, hf', hcomp, hcl⟩ := smallExt 𝔞 A f hf {a⁻¹, b⁻¹}
  obtain ⟨c, hc⟩ := hcl ⟨a⁻¹, haV⟩ (Subfield.subset_closure (Or.inr (by simp)))
  obtain ⟨d, hd⟩ := hcl ⟨b⁻¹, hbV⟩ (Subfield.subset_closure (Or.inr (by simp)))
  have hdu : ¬ IsUnit d := by
    intro h
    have h2 := h.map f'
    rw [hd] at h2
    have h3 : (⟨b⁻¹, hbV⟩ : 𝔞.V) ∈ maximalIdeal 𝔞.V := (𝔞.V.valuation_lt_one_iff _).2 hbi
    exact ((mem_maximalIdeal _).1 h3) h2
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact inv_ne_zero ha0 (congrArg Subtype.val hc).symm
  obtain ⟨n, hn⟩ := dvd_pow_of hdu hc0
  obtain ⟨e, he⟩ := map_dvd f' hn
  rw [map_pow, hc, hd] at he
  have he' : (b⁻¹) ^ n = a⁻¹ * (e : 𝔞.K) := congrArg Subtype.val he
  have hae : a = (e : 𝔞.K) * b ^ n := by
    calc a = a * (b⁻¹ ^ n * b ^ n) := by rw [← mul_pow, inv_mul_cancel₀ hb0, one_pow, mul_one]
      _ = a * (a⁻¹ * (e * b ^ n)) := by rw [he', mul_assoc]
      _ = e * b ^ n := mul_inv_cancel_left₀ ha0 _
  refine ⟨n, ?_⟩
  rw [hae, map_mul, map_pow]
  calc 𝔞.V.valuation (e : 𝔞.K) * 𝔞.V.valuation b ^ n ≤ 1 * 𝔞.V.valuation b ^ n :=
        mul_le_mul_left (𝔞.V.valuation_le_one e) _
    _ = 𝔞.V.valuation b ^ n := one_mul _

theorem UpperTheory.V.Ws.Po.ambAbs :
    ∀ {l : ℕ} [Fact l.Prime] (𝔞 : Amb l) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (f : A →+* 𝔞.V), 𝔞.IsDvr f →
      ∃ w : AbsoluteValue 𝔞.K ℝ, (∀ x, w x < 1 ↔ 𝔞.V.valuation x < 1) ∧ ∃ p, p ≠ 0 ∧ w p ≠ 1 := by
  intro l _ 𝔞 A _ _ _ f hf
  haveI := arch 𝔞 A f hf
  haveI : MulArchimedean (𝔞.V.ValueGroup)ˣ := ⟨fun x y hy => by
    obtain ⟨n, hn⟩ := MulArchimedean.arch (x : 𝔞.V.ValueGroup) (y := (y : 𝔞.V.ValueGroup)) hy
    refine ⟨n, ?_⟩
    show (x : 𝔞.V.ValueGroup) ≤ ((y ^ n : (𝔞.V.ValueGroup)ˣ) : 𝔞.V.ValueGroup)
    rw [Units.val_pow_eq_pow_val]
    exact hn⟩
  obtain ⟨φ, hφ⟩ := Archimedean.exists_orderAddMonoidHom_real_injective (Additive (𝔞.V.ValueGroup)ˣ)
  have hφm : StrictMono φ := φ.monotone'.strictMono_of_injective hφ
  let gg : 𝔞.V.ValueGroup → ℝ := fun γ =>
    if h : γ = 0 then 0 else Real.exp (φ (Additive.ofMul (Units.mk0 γ h)))
  have g0 : gg 0 = 0 := by simp [gg]
  have gpos : ∀ γ, γ ≠ 0 → 0 < gg γ := fun γ h => by
    simp only [gg, dif_neg h]
    exact Real.exp_pos _
  have gmono : StrictMono gg := by
    intro γ δ h
    have hδ : δ ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' h)
    by_cases hγ : γ = 0
    · rw [hγ, g0]
      exact gpos δ hδ
    · simp only [gg, dif_neg hγ, dif_neg hδ]
      apply Real.exp_lt_exp.2
      apply hφm
      exact (show Units.mk0 γ hγ < Units.mk0 δ hδ from h)
  have gnn : ∀ γ, 0 ≤ gg γ := fun γ => by
    rw [← g0]
    exact gmono.monotone zero_le'
  have gmul : ∀ γ δ, gg (γ * δ) = gg γ * gg δ := by
    intro γ δ
    by_cases hγ : γ = 0
    · simp [hγ, g0]
    by_cases hδ : δ = 0
    · simp [hδ, g0]
    have hγδ : γ * δ ≠ 0 := mul_ne_zero hγ hδ
    simp only [gg, dif_neg hγ, dif_neg hδ, dif_neg hγδ, ← Real.exp_add, ← map_add]
    congr 2
    rw [← ofMul_mul, Units.mk0_mul]
  have g1 : gg 1 = 1 := by
    have h1 : (1 : 𝔞.V.ValueGroup) ≠ 0 := one_ne_zero
    simp only [gg, dif_neg h1, Units.mk0_one, ofMul_one, map_zero, Real.exp_zero]
  let w : AbsoluteValue 𝔞.K ℝ :=
    { toFun := fun x => gg (𝔞.V.valuation x)
      map_mul' := fun x y => by
        change gg (𝔞.V.valuation (x * y)) = gg (𝔞.V.valuation x) * gg (𝔞.V.valuation y)
        rw [Valuation.map_mul, gmul]
      nonneg' := fun x => gnn _
      eq_zero' := fun x => ⟨fun h => by
          by_contra hx
          exact (gpos _ ((Valuation.ne_zero_iff _).2 hx)).ne' h,
        fun h => by rw [h, Valuation.map_zero, g0]⟩
      add_le' := fun x y => by
        have hle := gmono.monotone (𝔞.V.valuation.map_add x y)
        have hx := gnn (𝔞.V.valuation x)
        have hy := gnn (𝔞.V.valuation y)
        rcases le_total (𝔞.V.valuation x) (𝔞.V.valuation y) with h | h
        · rw [max_eq_right h] at hle
          linarith
        · rw [max_eq_left h] at hle
          linarith }
  refine ⟨w, fun x => ?_, ?_⟩
  · change gg (𝔞.V.valuation x) < 1 ↔ 𝔞.V.valuation x < 1
    rw [← g1]
    exact gmono.lt_iff_lt
  · obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
    refine ⟨𝔞.toK (f ϖ), ?_, ?_⟩
    · intro h
      apply hϖ.ne_zero
      apply hf.inj
      rw [map_zero]
      exact Subtype.val_injective h
    · have hlt : 𝔞.V.valuation (𝔞.toK (f ϖ)) < 1 := by
        have := Amb.IsDvr.loc hf
        have hnu : ¬ IsUnit (f ϖ) := fun h => hϖ.not_isUnit (isUnit_of_map_unit f ϖ h)
        exact (𝔞.V.valuation_lt_one_iff (f ϖ)).1 ((mem_maximalIdeal _).2 hnu)
      change gg _ ≠ 1
      rw [← g1]
      exact (gmono hlt).ne
