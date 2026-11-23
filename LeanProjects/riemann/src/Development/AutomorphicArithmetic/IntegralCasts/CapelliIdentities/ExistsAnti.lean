import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh37.Lp :
    (L : Type) → [Field L] → Type :=
    fun (L : Type) [Field L] ↦ ↥(NumberField.maximalRealSubfield L)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh37.Lsq :
    (R : Type) → [CommRing R] → R → Type :=
    fun (R : Type) [CommRing R] (Δ : R) ↦ QuadraticAlgebra R Δ (0 : R)

open NumberField NumberField.IsCMField in

private theorem UpperTheory.Reformulated.B.Qh37.exists_anti (L : Type) [Field L] [NumberField L] [IsCMField L] :
    ∃ δ : L, δ ≠ 0 ∧ complexConj L δ = -δ := by
  have h : ∃ x : L, complexConj L x ≠ x := by
    by_contra h
    push Not at h
    exact complexConj_ne_one L (AlgEquiv.ext h)
  obtain ⟨x, hx⟩ := h
  refine ⟨x - complexConj L x, sub_ne_zero.mpr hx.symm, ?_⟩
  rw [map_sub, complexConj_apply_apply, neg_sub]

theorem UpperTheory.Reformulated.B.Qh37.globEx :
    ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L] [inst_2 : NumberField.IsCMField L],
      ∃ (Δ : UpperTheory.Reformulated.B.Qh37.Lp L) (e : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ ≃+* L),
        (∀ (x : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ),
            (e : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ → L) (Star.star x) =
              (NumberField.IsCMField.complexConj L : L → L) ((e : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ → L) x)) ∧
          (∀ (a : UpperTheory.Reformulated.B.Qh37.Lp L),
              (e : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ → L)
                  ((Algebra.algebraMap (UpperTheory.Reformulated.B.Qh37.Lp L) (UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ) :
                      UpperTheory.Reformulated.B.Qh37.Lp L → UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ)
                    a) =
                (Algebra.algebraMap (UpperTheory.Reformulated.B.Qh37.Lp L) L : UpperTheory.Reformulated.B.Qh37.Lp L → L) a) ∧
            ∀ (σ : UpperTheory.Reformulated.B.Qh37.Lp L →+* ℝ), (σ : UpperTheory.Reformulated.B.Qh37.Lp L → ℝ) Δ < (0 : ℝ) := by
  intro L _ _ _
  obtain ⟨δ, hδ0, hδ⟩ := UpperTheory.Reformulated.B.Qh37.exists_anti L
  have hmem : δ * δ ∈ NumberField.maximalRealSubfield L := by
    rw [← NumberField.IsCMField.complexConj_eq_self_iff, map_mul, hδ, neg_mul_neg]
  let Δ : NumberField.maximalRealSubfield L := ⟨δ * δ, hmem⟩
  have hΔ : algebraMap (NumberField.maximalRealSubfield L) L Δ = δ * δ := rfl
  let f : QuadraticAlgebra (NumberField.maximalRealSubfield L) Δ 0 →ₐ[NumberField.maximalRealSubfield L] L :=
    QuadraticAlgebra.lift ⟨δ, by rw [zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one, hΔ]⟩
  have hω : f QuadraticAlgebra.omega = δ := by
    have := (QuadraticAlgebra.lift (R := NumberField.maximalRealSubfield L) (a := Δ) (b := 0)
      (A := L)).symm_apply_apply ⟨δ, by rw [zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one, hΔ]⟩
    exact congrArg Subtype.val this
  have hf : ∀ x y, f ⟨x, y⟩ = algebraMap _ L x + algebraMap _ L y * δ := by
    intro x y
    rw [QuadraticAlgebra.mk_eq_add_smul_omega, map_add, map_smul, AlgHom.commutes, hω,
      Algebra.smul_def]
  have hstar : ∀ z, f (star z) = NumberField.IsCMField.complexConj L (f z) := by
    rintro ⟨x, y⟩
    rw [QuadraticAlgebra.star_mk, hf, hf, map_add, map_add, map_mul, map_mul,
      AlgEquiv.commutes, AlgEquiv.commutes, hδ, map_neg, map_zero]
    ring
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, y⟩ h
    have h' := hstar ⟨x, y⟩
    rw [h, map_zero, QuadraticAlgebra.star_mk, hf, map_add, map_mul, map_neg, map_zero] at h'
    rw [hf] at h
    have hx : algebraMap _ L x = 0 := by linear_combination (h + h') / 2
    have hy : algebraMap _ L y * δ = 0 := by linear_combination (h - h') / 2
    have hy' := (mul_eq_zero.mp hy).resolve_right hδ0
    rw [map_eq_zero] at hx hy'
    subst hx hy'
    rfl
  have hsurj : Function.Surjective f := by
    intro z
    have h1 : (z + NumberField.IsCMField.complexConj L z) / 2 ∈
        NumberField.maximalRealSubfield L := by
      rw [← NumberField.IsCMField.complexConj_eq_self_iff, map_div₀, map_add, map_ofNat,
        NumberField.IsCMField.complexConj_apply_apply, add_comm]
    have h2 : (z - NumberField.IsCMField.complexConj L z) / (2 * δ) ∈
        NumberField.maximalRealSubfield L := by
      rw [← NumberField.IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul, map_ofNat,
        NumberField.IsCMField.complexConj_apply_apply, hδ]
      field_simp
      ring
    refine ⟨⟨⟨_, h1⟩, ⟨_, h2⟩⟩, ?_⟩
    rw [hf]
    change (z + NumberField.IsCMField.complexConj L z) / 2 +
      (z - NumberField.IsCMField.complexConj L z) / (2 * δ) * δ = z
    field_simp
    ring
  refine ⟨Δ, RingEquiv.ofBijective f.toRingHom ⟨hinj, hsurj⟩, hstar, f.commutes, fun σ ↦ ?_⟩
  let φ : L →+* ℂ := NumberField.ComplexEmbedding.lift L (Complex.ofRealHom.comp σ)
  have h1 : φ δ * φ δ = (σ Δ : ℂ) := by
    rw [← map_mul, ← hΔ]
    exact NumberField.ComplexEmbedding.lift_algebraMap_apply L (Complex.ofRealHom.comp σ) Δ
  have h2 : (starRingEnd ℂ) (φ δ) = -φ δ := by
    rw [← NumberField.IsCMField.complexEmbedding_complexConj, hδ, map_neg]
  have h3 : ((Complex.normSq (φ δ) : ℝ) : ℂ) = ((-σ Δ : ℝ) : ℂ) := by
    rw [← Complex.mul_conj, h2, mul_neg, h1, Complex.ofReal_neg]
  have h4 : 0 < Complex.normSq (φ δ) := Complex.normSq_pos.mpr ((map_ne_zero φ).mpr hδ0)
  rw [Complex.ofReal_injective h3] at h4
  exact neg_pos.mp h4
