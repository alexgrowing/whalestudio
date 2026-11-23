import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphTheta.InertRw

open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open Ad3.K.GL2LocalData (nsg rW)

section Nsg

variable {F : Type} [Field F] {E : Type} [Field E] [Algebra F E]

theorem nsg_norm (t : Eˣ) : nsg E (Algebra.norm F (t : E)) = 1 := by
  unfold nsg
  exact if_pos ⟨t, rfl⟩

theorem nsg_one : nsg E (1 : F) = 1 := by
  simpa using nsg_norm (F := F) (1 : Eˣ)

theorem nsg_inv (hm : ∀ x y : F, x ≠ 0 → y ≠ 0 → nsg E (x * y) = nsg E x * nsg E y)
    (hs : ∀ x : F, x ≠ 0 → nsg E x * nsg E x = 1) {x : F} (hx : x ≠ 0) :
    nsg E x⁻¹ = nsg E x := by
  have h1 : nsg E x⁻¹ * nsg E x = 1 := by
    rw [← hm _ _ (inv_ne_zero hx) hx, inv_mul_cancel₀ hx, nsg_one]
  calc nsg E x⁻¹ = nsg E x⁻¹ * (nsg E x * nsg E x) := by rw [hs x hx, mul_one]
    _ = nsg E x := by rw [← mul_assoc, h1, one_mul]

end Nsg

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)]

theorem intInd_conj (x : E) : intInd (conj F E x) = intInd x := by
  unfold intInd
  simp only [← modulus_le_one_iff, modulus_conj]

variable [MeasurableSpace E] [BorelSpace E]

theorem integral_subst (μ : Measure E) [μ.IsAddHaarMeasure] (χ : AddChar F Circle)
    (σ : E ≃ₐ[F] E) (a c d : F) (hc : c ≠ 0) (t : Eˣ) :
    ∫ u : E, (χ ((a / Algebra.norm F (t : E) * Algebra.norm F (1 : E) + d * Algebra.norm F u
        - Algebra.trace F E (σ 1 * u)) / (c / Algebra.norm F (t : E))) : ℂ) * intInd (u * (t : E)) ∂μ
      = (((modulus (t : E) : ℝ)⁻¹ : ℝ) : ℂ) * ((χ (a / c) : ℂ) *
        ∫ u : E, (χ (d / c * Algebra.norm F u
          - Algebra.trace F E (conj F E (t : E) * algebraMap F E c⁻¹ * u)) : ℂ) * intInd u ∂μ) := by
  have hD : Algebra.norm F (t : E) ≠ 0 := Algebra.norm_ne_zero_iff.2 t.ne_zero
  set f : E → ℂ := fun u => (χ (d / c * Algebra.norm F u
    - Algebra.trace F E (conj F E (t : E) * algebraMap F E c⁻¹ * u)) : ℂ) * intInd u with hf
  have key : ∀ u : E, (χ ((a / Algebra.norm F (t : E) * Algebra.norm F (1 : E) + d * Algebra.norm F u
        - Algebra.trace F E (σ 1 * u)) / (c / Algebra.norm F (t : E))) : ℂ) * intInd (u * (t : E))
      = (χ (a / c) : ℂ) * f ((t : E) * u) := by
    intro u
    have hy : conj F E (t : E) * algebraMap F E c⁻¹ * ((t : E) * u)
        = algebraMap F E (Algebra.norm F (t : E) * c⁻¹) * u := by
      rw [map_mul, algebraMap_norm_eq_mul_conj]
      ring
    have harg : (a / Algebra.norm F (t : E) * Algebra.norm F (1 : E) + d * Algebra.norm F u
        - Algebra.trace F E (σ 1 * u)) / (c / Algebra.norm F (t : E))
        = a / c + (d / c * Algebra.norm F ((t : E) * u)
          - Algebra.trace F E (conj F E (t : E) * algebraMap F E c⁻¹ * ((t : E) * u))) := by
      have hN1 : Algebra.norm F (1 : E) = 1 := map_one _
      have hNtu : Algebra.norm F ((t : E) * u) = Algebra.norm F (t : E) * Algebra.norm F u :=
        map_mul _ _ _
      have hs1 : σ (1 : E) = 1 := map_one σ
      rw [hy, ← Algebra.smul_def, map_smul, smul_eq_mul, hNtu, hN1, hs1, one_mul]
      field_simp
      ring
    simp only [hf]
    rw [harg, AddChar.map_add_eq_mul, Circle.coe_mul, mul_comm u, mul_assoc]
  rw [integral_congr_ae (Filter.Eventually.of_forall key), integral_const_mul,
    integral_comp_mul_left μ t.ne_zero f]
  rw [Complex.real_smul]
  push_cast
  ring

variable (μ : Measure E) [μ.IsAddHaarMeasure] (χ : AddChar F Circle) (σ : E ≃ₐ[F] E)

theorem rW_of_ne (hm : ∀ x y : F, x ≠ 0 → y ≠ 0 → nsg E (x * y) = nsg E x * nsg E y)
    (hs : ∀ x : F, x ≠ 0 → nsg E x * nsg E x = 1) (hn1 : nsg E (-1 : F) = 1)
    (a b c d : F) (hc : c ≠ 0) (t : Eˣ) :
    rW χ σ μ 1 (a / Algebra.norm F (t : E)) b (c / Algebra.norm F (t : E)) d
        (fun x => intInd (x * (t : E))) 1
      = nsg E c * (((modulus c : ℝ)⁻¹ : ℝ) : ℂ) * ((χ (a / c) : ℂ) *
        ∫ u : E, (χ (d / c * Algebra.norm F u
          - Algebra.trace F E (conj F E (t : E) * algebraMap F E c⁻¹ * u)) : ℂ) * intInd u ∂μ) := by
  have hD : Algebra.norm F (t : E) ≠ 0 := Algebra.norm_ne_zero_iff.2 t.ne_zero
  have hC : c / Algebra.norm F (t : E) ≠ 0 := div_ne_zero hc hD
  have hnsg : nsg E (-(c / Algebra.norm F (t : E))) = nsg E c := by
    have h : -(c / Algebra.norm F (t : E)) = (-1) * (c * (Algebra.norm F (t : E))⁻¹) := by ring
    rw [h, hm _ _ (by norm_num) (mul_ne_zero hc (inv_ne_zero hD)), hm _ _ hc (inv_ne_zero hD), hn1,
      nsg_inv hm hs hD, nsg_norm, one_mul, mul_one]
  have hDr : (modulus (Algebra.norm F (t : E)) : ℝ) ≠ 0 := by
    exact_mod_cast modulus_ne_zero hD
  have hcr : (modulus c : ℝ) ≠ 0 := by exact_mod_cast modulus_ne_zero hc
  have hconst : (((modulus (c / Algebra.norm F (t : E)) : ℝ)⁻¹ : ℝ) : ℂ)
      * (((modulus (t : E) : ℝ)⁻¹ : ℝ) : ℂ) = (((modulus c : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [← modulus_norm (K := F) (t : E), div_eq_mul_inv, modulus_mul, modulus_inv]
    push_cast
    field_simp
  unfold rW
  rw [if_neg hC]
  beta_reduce
  rw [integral_subst μ χ σ a c d hc t, hnsg, one_mul]
  linear_combination (nsg E c * ((χ (a / c) : ℂ) *
        ∫ u : E, (χ (d / c * Algebra.norm F u
          - Algebra.trace F E (conj F E (t : E) * algebraMap F E c⁻¹ * u)) : ℂ) * intInd u ∂μ)) * hconst

theorem rW_of_eq (hm : ∀ x y : F, x ≠ 0 → y ≠ 0 → nsg E (x * y) = nsg E x * nsg E y)
    (hs : ∀ x : F, x ≠ 0 → nsg E x * nsg E x = 1)
    (a b d : F) (ha : a ≠ 0) (hd : d ≠ 0) (t : Eˣ) (hdet : Algebra.norm F (t : E) = a * d) :
    rW χ σ μ 1 (a / Algebra.norm F (t : E)) b (0 / Algebra.norm F (t : E)) d
        (fun x => intInd (x * (t : E))) 1
      = (((modulus d : ℝ)⁻¹ : ℝ) : ℂ) * nsg E d * (χ (b / d) : ℂ)
        * intInd ((t : E) * algebraMap F E d⁻¹) := by
  have hA : a / Algebra.norm F (t : E) = d⁻¹ := by
    rw [hdet]
    field_simp
  have hN1 : Algebra.norm F (1 : E) = 1 := map_one _
  have hb : d⁻¹ * b * 1 = b / d := by
    rw [mul_one, div_eq_mul_inv, mul_comm]
  unfold rW
  rw [zero_div, if_pos rfl, hA, nsg_inv hm hs hd, modulus_inv, hN1, hb]
  beta_reduce
  rw [mul_one, mul_comm (algebraMap F E d⁻¹)]
  push_cast
  ring

theorem rW_row (hm : ∀ x y : F, x ≠ 0 → y ≠ 0 → nsg E (x * y) = nsg E x * nsg E y)
    (hs : ∀ x : F, x ≠ 0 → nsg E x * nsg E x = 1) (hn1 : nsg E (-1 : F) = 1)
    (hint : ∀ (δ : F) (y : E),
      (δ ∈ 𝒪[F] → ∫ u : E, (χ (δ * Algebra.norm F u - Algebra.trace F E (y * u)) : ℂ) * intInd u ∂μ
        = intInd y) ∧
      (δ ∉ 𝒪[F] → ∫ u : E, (χ (δ * Algebra.norm F u - Algebra.trace F E (y * u)) : ℂ) * intInd u ∂μ
        = nsg E δ * (((modulus δ : ℝ)⁻¹ : ℝ) : ℂ) * (χ (-(Algebra.norm F y) / δ) : ℂ)
          * intInd (y * algebraMap F E δ⁻¹)))
    (g : GL (Fin 2) F) (t : Eˣ) (hdet : Algebra.norm F (t : E) = (g.val).det) :
    rW χ σ μ 1 (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1)
        (fun x => intInd (x * (t : E))) 1
      = (((modulus (mRow g) : ℝ)⁻¹ : ℝ) : ℂ) * nsg E (mRow g) * (χ (xRow g) : ℂ)
        * intInd ((t : E) * algebraMap F E (mRow g)⁻¹) := by
  have hD : Algebra.norm F (t : E) ≠ 0 := Algebra.norm_ne_zero_iff.2 t.ne_zero
  have hdet2 : Algebra.norm F (t : E)
      = g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 := by
    rw [hdet, Matrix.det_fin_two]
  rw [← hdet]
  unfold mRow xRow
  generalize g.val 0 0 = a at *
  generalize g.val 0 1 = b at *
  generalize g.val 1 0 = c at *
  generalize g.val 1 1 = d at *
  by_cases hc : c = 0
  · subst hc
    have hdet3 : Algebra.norm F (t : E) = a * d := by rw [hdet2]; ring
    have ha : a ≠ 0 := fun h => hD (by rw [hdet3, h, zero_mul])
    have hd : d ≠ 0 := fun h => hD (by rw [hdet3, h, mul_zero])
    have hlt : modulus (0 : F) < modulus d := by
      rw [modulus_zero]
      exact modulus_pos hd
    rw [if_pos hlt, if_pos hlt]
    exact rW_of_eq μ χ σ hm hs a b d ha hd t hdet3
  rw [rW_of_ne μ χ σ hm hs hn1 a b c d hc t]
  have hcr : (modulus c : ℝ) ≠ 0 := by exact_mod_cast modulus_ne_zero hc
  by_cases hlt : modulus c < modulus d
  · have hd : d ≠ 0 := by
      rintro rfl
      rw [modulus_zero] at hlt
      exact not_lt_zero hlt
    have hdr : (modulus d : ℝ) ≠ 0 := by exact_mod_cast modulus_ne_zero hd
    have hδ : d / c ∉ 𝒪[F] := by
      rw [← modulus_le_one_iff, div_eq_mul_inv, modulus_mul, modulus_inv, not_le]
      rw [← div_eq_mul_inv]
      exact (one_lt_div (modulus_pos hc)).2 hlt
    have hδ0 : d / c ≠ 0 := div_ne_zero hd hc
    rw [if_pos hlt, if_pos hlt, (hint _ _).2 hδ]
    have hNy : Algebra.norm F (conj F E (t : E) * algebraMap F E c⁻¹)
        = Algebra.norm F (t : E) * c⁻¹ ^ 2 := by
      rw [map_mul, norm_conj, norm_algebraMap_eq_sq]
    have hyδ : conj F E (t : E) * algebraMap F E c⁻¹ * algebraMap F E (d / c)⁻¹
        = conj F E ((t : E) * algebraMap F E d⁻¹) := by
      have h : algebraMap F E c⁻¹ * algebraMap F E (d / c)⁻¹ = algebraMap F E d⁻¹ := by
        rw [← map_mul]
        congr 1
        field_simp
      rw [mul_assoc, h, map_mul, conj_algebraMap]
    have hχ : (χ (a / c) : ℂ) * (χ (-(Algebra.norm F (conj F E (t : E) * algebraMap F E c⁻¹)) / (d / c)) : ℂ)
        = (χ (b / d) : ℂ) := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      rw [hNy, hdet2]
      field_simp
      ring
    have hnsg : nsg E c * nsg E (d / c) = nsg E d := by
      rw [← hm _ _ hc hδ0]
      congr 1
      field_simp
    have hmod : (((modulus c : ℝ)⁻¹ : ℝ) : ℂ) * (((modulus (d / c) : ℝ)⁻¹ : ℝ) : ℂ)
        = (((modulus d : ℝ)⁻¹ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
      congr 1
      rw [div_eq_mul_inv, modulus_mul, modulus_inv]
      push_cast
      field_simp
    rw [hyδ, intInd_conj, ← hχ, ← hnsg, ← hmod]
    ring
  · have hδ : d / c ∈ 𝒪[F] := by
      rw [← modulus_le_one_iff, div_eq_mul_inv, modulus_mul, modulus_inv, ← div_eq_mul_inv]
      exact (div_le_one (modulus_pos hc)).2 (not_lt.1 hlt)
    rw [if_neg hlt, if_neg hlt, (hint _ _).1 hδ]
    have hy : conj F E (t : E) * algebraMap F E c⁻¹ = conj F E ((t : E) * algebraMap F E c⁻¹) := by
      rw [map_mul, conj_algebraMap]
    rw [hy, intInd_conj]
    ring

end Local

end GlobalTheory.CompanionTheory.SphTheta.InertRw

namespace GlobalTheory.CompanionTheory.SphTheta

open GlobalTheory.CompanionTheory.SphTheta.InertRw in

theorem inert_rw : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] [CharZero F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E], Module.finrank F E = 2 → Continuous (algebraMap F E) → GroundTheory.LocalField.ord (algebraMap F E (unifUnit F : F)) = 1 → ∀ (χ : AddChar F Circle) (η : Fˣ →* ℂˣ) (σ : E ≃ₐ[F] E), σ ≠ AlgEquiv.refl → Ad3.IsStd χ → Ad3.IsStd (Ad3.K.GL2LocalData.chE E χ) → ((∀ a, ((η a : ℂˣ) : ℂ) = Ad3.K.GL2LocalData.nsg E (a : F)) ∧ IsUnramifiedChar η ∧ η * η = 1 ∧ Ad3.K.GL2LocalData.nsg E (-1 : F) = 1) → (∀ (δ : F) (y : E), (δ ∈ 𝒪[F] → ∫ u : E, (χ (δ * Algebra.norm F u - Algebra.trace F E (y * u)) : ℂ) * intInd u ∂selfDualMeasure (Ad3.K.GL2LocalData.chE E χ) = intInd y) ∧ (δ ∉ 𝒪[F] → ∫ u : E, (χ (δ * Algebra.norm F u - Algebra.trace F E (y * u)) : ℂ) * intInd u ∂selfDualMeasure (Ad3.K.GL2LocalData.chE E χ) = Ad3.K.GL2LocalData.nsg E δ * (((modulus δ : ℝ)⁻¹ : ℝ) : ℂ) * (χ (-(Algebra.norm F y) / δ) : ℂ) * intInd (y * algebraMap F E δ⁻¹))) → ∀ (g : GL (Fin 2) F) (t : Eˣ), Algebra.norm F (t : E) = (g.val).det → Ad3.K.GL2LocalData.rW χ σ (selfDualMeasure (Ad3.K.GL2LocalData.chE E χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => intInd (x * (t : E))) 1 = (((modulus (mRow g) : ℝ)⁻¹ : ℝ) : ℂ) * Ad3.K.GL2LocalData.nsg E (mRow g) * (χ (xRow g) : ℂ) * intInd ((t : E) * algebraMap F E (mRow g)⁻¹) := by
  intro F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ _ hfin _ _ χ η σ _ _ _ hη hint g t hdet
  obtain ⟨hval, -, hsq, hn1⟩ := hη
  have : Fact (Module.finrank F E = 2) := ⟨hfin⟩
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hm : ∀ x y : F, x ≠ 0 → y ≠ 0 →
      Ad3.K.GL2LocalData.nsg E (x * y) = Ad3.K.GL2LocalData.nsg E x * Ad3.K.GL2LocalData.nsg E y := by
    intro x y hx hy
    have h := hval (Units.mk0 x hx * Units.mk0 y hy)
    rw [map_mul, Units.val_mul, hval, hval] at h
    simpa using h.symm
  have hs : ∀ x : F, x ≠ 0 → Ad3.K.GL2LocalData.nsg E x * Ad3.K.GL2LocalData.nsg E x = 1 := by
    intro x hx
    have h := congrArg (fun f : Fˣ →* ℂˣ => ((f (Units.mk0 x hx) : ℂˣ) : ℂ)) hsq
    simp only [MonoidHom.mul_apply, Units.val_mul, hval, MonoidHom.one_apply, Units.val_one] at h
    simpa using h
  exact rW_row _ χ σ hm hs hn1 hint g t hdet

end GlobalTheory.CompanionTheory.SphTheta
