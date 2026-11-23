import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultHaarConstToRealNeZero

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphTheta.SplitRW

section Alg

variable {F : Type} [Field F]

theorem norm_pair (x : F × F) : Algebra.norm F x = x.1 * x.2 := by
  rw [Algebra.norm_eq_matrix_det (Module.Basis.finTwoProd F), Matrix.det_fin_two]
  simp [Algebra.leftMulMatrix_eq_repr_mul, Module.Basis.finTwoProd]

theorem trace_pair (x : F × F) : Algebra.trace F (F × F) x = x.1 + x.2 := by
  simp [Algebra.trace_prod_apply]

theorem nsg_pair {a : F} (ha : a ≠ 0) : Ad3.K.GL2LocalData.nsg (F × F) a = 1 := by
  rw [Ad3.K.GL2LocalData.nsg, if_pos]
  refine ⟨⟨(a, 1), (a⁻¹, 1), by simp [ha], by simp [ha]⟩, ?_⟩
  simp [norm_pair]

end Alg

section Int

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem intInd_of_mem {x : F} (hx : x ∈ 𝒪[F]) : intInd x = 1 := by
  simp [intInd, hx]

theorem intInd_of_notMem {x : F} (hx : x ∉ 𝒪[F]) : intInd x = 0 := by
  simp [intInd, hx]

theorem intInd_neg (x : F) : intInd (-x) = intInd x := by
  by_cases hx : x ∈ 𝒪[F]
  · rw [intInd_of_mem hx, intInd_of_mem (neg_mem hx)]
  · rw [intInd_of_notMem hx, intInd_of_notMem (fun h => hx (by simpa using neg_mem h))]

theorem intInd_eq_indicator (x : F) :
    intInd x = (valBall F 0 : Set F).indicator (fun _ => (1 : ℂ)) x := by
  by_cases hx : x ∈ 𝒪[F]
  · rw [intInd_of_mem hx, Set.indicator_of_mem (show x ∈ (valBall F 0 : Set F) from mem_valBall_zero_iff.2 hx)]
  · rw [intInd_of_notMem hx, Set.indicator_of_notMem (show x ∉ (valBall F 0 : Set F) from fun h => hx (mem_valBall_zero_iff.1 h))]

end Int

section Meas

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {χ : AddChar F Circle}

theorem orth (hχ : IsStd χ) (y : F) :
    ∫ p, intInd p * (χ (y * p) : ℂ) ∂(haarIntegers F) = intInd y := by
  have key := localFourier_indicator_valBall (haarIntegers F) hχ.1 hχ.2.1 0 y
  rw [hχ.2.2, sub_zero] at key
  have hreal : (haarIntegers F).real (valBall F 0 : Set F) = 1 := by
    rw [measureReal_def, coe_valBall_zero, haarIntegers_integers]; simp
  rw [hreal, ← intInd_eq_indicator] at key
  unfold localFourier at key
  simp only [Complex.ofReal_one, one_mul] at key
  rw [← key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [mul_comm y p, intInd_eq_indicator]

theorem orth_scaled (hχ : IsStd χ) {D : F} (hD : D ≠ 0) (t : F) :
    ∫ p, intInd (p * D) * (χ (t * p) : ℂ) ∂(haarIntegers F) =
      (((modulus D : ℝ)⁻¹ : ℝ) : ℂ) * intInd (t / D) := by
  have h := integral_comp_mul_left (haarIntegers F) hD
    (fun x => intInd x * (χ (t / D * x) : ℂ))
  rw [orth hχ, Complex.real_smul] at h
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only []
  rw [mul_comm D p, show t / D * (p * D) = t * p by field_simp]

def J (χ : AddChar F Circle) (δ y₁ y₂ : F) : ℂ :=
  ∫ q, intInd q * (χ (-(y₂ * q)) : ℂ) * intInd (δ * q - y₁) ∂(haarIntegers F)

theorem J_of_mem (hχ : IsStd χ) {δ : F} (hδ : δ ∈ 𝒪[F]) (y₁ y₂ : F) :
    J χ δ y₁ y₂ = intInd y₁ * intInd y₂ := by
  have h := orth hχ (-y₂)
  rw [intInd_neg] at h
  rw [← h, J, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only []
  by_cases hq : q ∈ 𝒪[F]
  · have e : intInd (δ * q - y₁) = intInd y₁ := by
      by_cases hy : y₁ ∈ 𝒪[F]
      · rw [intInd_of_mem hy, intInd_of_mem (sub_mem (mul_mem hδ hq) hy)]
      · rw [intInd_of_notMem hy, intInd_of_notMem fun h' => hy (by
          have := sub_mem (mul_mem hδ hq) h'
          simpa using this)]
    rw [e, neg_mul]
    ring
  · rw [intInd_of_notMem hq]; simp

theorem inv_mem_of_notMem {δ : F} (hδ : δ ∉ 𝒪[F]) : δ ≠ 0 ∧ δ⁻¹ ∈ 𝒪[F] := by
  have h0 : δ ≠ 0 := fun h => hδ (h ▸ zero_mem _)
  refine ⟨h0, ?_⟩
  rw [← modulus_le_one_iff, modulus_inv]
  have : 1 < modulus δ := not_le.1 fun h => hδ (modulus_le_one_iff.1 h)
  exact inv_le_one_of_one_le₀ this.le

theorem J_of_notMem (hχ : IsStd χ) {δ : F} (hδ : δ ∉ 𝒪[F]) (y₁ y₂ : F) :
    J χ δ y₁ y₂ = (((modulus δ : ℝ)⁻¹ : ℝ) : ℂ) * (χ (-(y₁ * y₂ / δ)) : ℂ) *
      intInd (y₁ / δ) * intInd (y₂ / δ) := by
  obtain ⟨h0, hinv⟩ := inv_mem_of_notMem hδ
  have hpt : ∀ q : F, intInd q * intInd (δ * q - y₁) = intInd (y₁ / δ) * intInd (δ * q - y₁) := by
    intro q
    by_cases hs : δ * q - y₁ ∈ 𝒪[F]
    · have e : q = y₁ / δ + (δ * q - y₁) * δ⁻¹ := by field_simp; ring
      have hm := mul_mem hs hinv
      have hiff : q ∈ 𝒪[F] ↔ y₁ / δ ∈ 𝒪[F] := by
        constructor
        · intro h
          have := sub_mem h hm
          rwa [show q - (δ * q - y₁) * δ⁻¹ = y₁ / δ by field_simp; ring] at this
        · intro h
          rw [e]
          exact add_mem h hm
      by_cases hq : q ∈ 𝒪[F]
      · rw [intInd_of_mem hq, intInd_of_mem (hiff.1 hq)]
      · rw [intInd_of_notMem hq, intInd_of_notMem (fun h => hq (hiff.2 h))]
    · rw [intInd_of_notMem hs]; simp
  let h : F → ℂ := fun s => (χ (-(y₂ * ((s + y₁) / δ))) : ℂ) * intInd s
  have h1 : J χ δ y₁ y₂ = intInd (y₁ / δ) * ∫ q, h (δ * q - y₁) ∂(haarIntegers F) := by
    rw [J, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [h]
    rw [show (δ * q - y₁ + y₁) / δ = q by field_simp; ring]
    calc _ = (χ (-(y₂ * q)) : ℂ) * (intInd q * intInd (δ * q - y₁)) := by ring
      _ = _ := by rw [hpt]; ring
  have h2 : ∫ q, h (δ * q - y₁) ∂(haarIntegers F) =
      ((modulus δ : ℝ))⁻¹ • ∫ s, h s ∂(haarIntegers F) := by
    have := integral_comp_mul_left (haarIntegers F) h0 (fun x => h (x - y₁))
    rw [integral_sub_right_eq_self h y₁] at this
    exact this
  have h3 : ∫ s, h s ∂(haarIntegers F) = (χ (-(y₁ * y₂ / δ)) : ℂ) * intInd (y₂ / δ) := by
    have ho := orth hχ (-(y₂ / δ))
    rw [intInd_neg] at ho
    rw [← ho, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [h]
    rw [show -(y₂ * ((s + y₁) / δ)) = -(y₁ * y₂ / δ) + -(y₂ / δ) * s by field_simp; ring,
      AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  rw [h1, h2, h3, Complex.real_smul]
  ring

end Meas

section Main

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {χ : AddChar F Circle}

theorem integrable_intInd_mul {D : F} (hD : D ≠ 0) :
    Integrable (fun p : F => intInd (p * D)) (haarIntegers F) := by
  have hc : IsCompact ((fun p : F => p * D) ⁻¹' (valBall F 0 : Set F)) :=
    (Homeomorph.mulRight₀ D hD).isCompact_preimage.2 (isCompact_valBall 0)
  have e : (fun p : F => intInd (p * D)) =
      ((fun p : F => p * D) ⁻¹' (valBall F 0 : Set F)).indicator (fun _ => (1 : ℂ)) := by
    funext p
    rw [intInd_eq_indicator]
    rfl
  rw [e]
  exact (integrable_indicator_iff hc.measurableSet).2 (integrableOn_const hc.measure_lt_top.ne)

theorem integrable_kernel {D : F} (hD : D ≠ 0) {K : F × F → Circle} (hK : Continuous K) :
    Integrable (fun w : F × F => (K w : ℂ) * phiS (w * (D, 1)))
      ((haarIntegers F).prod (haarIntegers F)) := by
  have h1 : Integrable (fun w : F × F => intInd (w.1 * D) * intInd w.2)
      ((haarIntegers F).prod (haarIntegers F)) := by
    have h2 := integrable_intInd_mul (F := F) one_ne_zero
    simp only [mul_one] at h2
    exact Integrable.mul_prod (integrable_intInd_mul hD) h2
  have hm : AEStronglyMeasurable (fun w : F × F => (K w : ℂ))
      ((haarIntegers F).prod (haarIntegers F)) :=
    (continuous_subtype_val.comp hK).aestronglyMeasurable
  have hphi : ∀ w : F × F, phiS (w * (D, 1)) = intInd (w.1 * D) * intInd w.2 := by
    intro w
    simp [phiS]
  simp only [hphi]
  refine h1.mono (hm.mul h1.1) (Filter.Eventually.of_forall fun w => ?_)
  rw [norm_mul, Circle.norm_coe, one_mul]

theorem rW_ne (hχ : IsStd χ) {a b c d D : F} (hD : D ≠ 0) (hc : c ≠ 0) (u : Fˣ) :
    Ad3.K.GL2LocalData.rW χ Ad3.K.GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 (a / D) b
        (c / D) d (fun x => phiS (x * (D, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) =
      (((modulus c : ℝ)⁻¹ : ℝ) : ℂ) * (χ (a / c) : ℂ) *
        J χ (d / c) (((u⁻¹ : Fˣ) : F) / c) (D * u / c) := by
  have hu : (u : F) ≠ 0 := u.ne_zero
  have hC : c / D ≠ 0 := div_ne_zero hc hD
  have hN : Algebra.norm F (((u : F), ((u⁻¹ : Fˣ) : F)) : F × F) = 1 := by
    simp [norm_pair, hu]
  rw [Ad3.K.GL2LocalData.rW, if_neg hC, nsg_pair (neg_ne_zero.2 hC), GlobalTheory.CompanionTheory.GJOne.selfDualMeasure_eq_of_isStd hχ, hN]
  set E : F × F → F := fun w => (a / D * 1 + d * (w.1 * w.2) -
      (((u⁻¹ : Fˣ) : F) * w.1 + (u : F) * w.2)) / (c / D) with hE
  have hEc : Continuous E := by
    simp only [hE]
    fun_prop
  have hKc : Continuous (fun w => χ (E w)) := hχ.1.comp hEc
  have hint : ∀ w : F × F, (χ ((a / D * 1 + d * Algebra.norm F w -
      Algebra.trace F (F × F) (Ad3.K.GL2LocalData.swapE ((u : F), ((u⁻¹ : Fˣ) : F)) * w)) / (c / D)) : ℂ) *
        phiS (w * (D, 1)) = (χ (E w) : ℂ) * phiS (w * (D, 1)) := by
    intro w
    have : Ad3.K.GL2LocalData.swapE (((u : F), ((u⁻¹ : Fˣ) : F)) : F × F) = (((u⁻¹ : Fˣ) : F), (u : F)) := rfl
    rw [this, norm_pair, trace_pair]
    rfl
  simp only [hint]
  rw [integral_prod_symm _ (integrable_kernel hD hKc)]
  have hinner : ∀ q : F, ∫ p, (χ (E (p, q)) : ℂ) * phiS ((p, q) * (D, 1)) ∂(haarIntegers F) =
      (χ (a / c) : ℂ) * ((((modulus D : ℝ)⁻¹ : ℝ) : ℂ) *
        (intInd q * (χ (-(D * u / c * q)) : ℂ) * intInd (d / c * q - ((u⁻¹ : Fˣ) : F) / c))) := by
    intro q
    have ho := orth_scaled hχ hD ((d * q - ((u⁻¹ : Fˣ) : F)) * D / c)
    rw [show (d * q - ((u⁻¹ : Fˣ) : F)) * D / c / D = d / c * q - ((u⁻¹ : Fˣ) : F) / c by
      field_simp] at ho
    have : ∀ p : F, (χ (E (p, q)) : ℂ) * phiS ((p, q) * (D, 1)) =
        ((χ (a / c) : ℂ) * (χ (-(D * u / c * q)) : ℂ) * intInd q) *
          (intInd (p * D) * (χ ((d * q - ((u⁻¹ : Fˣ) : F)) * D / c * p) : ℂ)) := by
      intro p
      have e : E (p, q) = a / c + -(D * u / c * q) + (d * q - ((u⁻¹ : Fˣ) : F)) * D / c * p := by
        simp only [hE]
        field_simp
        ring
      rw [e, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, Circle.coe_mul, Circle.coe_mul]
      simp only [phiS, Prod.mk_mul_mk, mul_one]
      ring
    simp only [this]
    rw [integral_const_mul, ho]
    ring
  simp only [hinner]
  rw [integral_const_mul, integral_const_mul, J]
  have hm : (((modulus (c / D) : ℝ)⁻¹ : ℝ) : ℂ) * (((modulus D : ℝ)⁻¹ : ℝ) : ℂ) =
      (((modulus c : ℝ)⁻¹ : ℝ) : ℂ) := by
    have hDp : (modulus D : ℝ) ≠ 0 := by exact_mod_cast modulus_ne_zero hD
    have hcp : (modulus c : ℝ) ≠ 0 := by exact_mod_cast modulus_ne_zero hc
    rw [div_eq_mul_inv, modulus_mul, modulus_inv]
    rw [← Complex.ofReal_mul]
    congr 1
    push_cast
    field_simp
  simp only [one_mul]
  rw [← hm]
  ring

theorem rW_zero (hχ : IsStd χ) {a b d D : F} (hd : d ≠ 0) (ha : a ≠ 0) (hDe : D = a * d) (u : Fˣ) :
    Ad3.K.GL2LocalData.rW χ Ad3.K.GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 (a / D) b
        (0 / D) d (fun x => phiS (x * (D, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) =
      (((modulus d : ℝ)⁻¹ : ℝ) : ℂ) * (χ (b / d) : ℂ) * intInd (d * u)⁻¹ * intInd (D * u / d) := by
  have hu : (u : F) ≠ 0 := u.ne_zero
  have hN : Algebra.norm F (((u : F), ((u⁻¹ : Fˣ) : F)) : F × F) = 1 := by
    simp [norm_pair, hu]
  have hA : a / D = d⁻¹ := by rw [hDe]; field_simp
  rw [Ad3.K.GL2LocalData.rW, if_pos (zero_div D), hN, hA, nsg_pair (inv_ne_zero hd), modulus_inv]
  have e1 : d⁻¹ * b * 1 = b / d := by field_simp
  have e2 : (algebraMap F (F × F) d⁻¹ * ((u : F), ((u⁻¹ : Fˣ) : F))) * (D, 1) =
      (D * u / d, (d * u)⁻¹) := by
    ext
    · simp [Prod.algebraMap_apply]; field_simp
    · simp [Prod.algebraMap_apply]; field_simp
  rw [e1]
  simp only [e2, phiS]
  push_cast
  ring

end Main

theorem rW_phiS : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), Ad3.IsStd χ → ∀ (g : GL (Fin 2) F) (u : Fˣ), Ad3.K.GL2LocalData.rW χ Ad3.K.GL2LocalData.swapE ((selfDualMeasure χ).prod (selfDualMeasure χ)) 1 (g.val 0 0 / (g.val).det) (g.val 0 1) (g.val 1 0 / (g.val).det) (g.val 1 1) (fun x => phiS (x * ((g.val).det, 1))) ((u : F), ((u⁻¹ : Fˣ) : F)) = (((modulus (mRow g) : ℝ)⁻¹ : ℝ) : ℂ) * (χ (xRow g) : ℂ) * intInd (mRow g * u)⁻¹ * intInd ((g.val).det * u / mRow g) := by
  intro F _ _ _ _ _ _ χ hχ g u
  have hD : (g.val).det ≠ 0 := (Matrix.GeneralLinearGroup.det g).ne_zero
  have hdet : (g.val).det = g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 := Matrix.det_fin_two _
  have hu : (u : F) ≠ 0 := u.ne_zero
  unfold mRow xRow
  generalize hDdef : (g.val).det = D at *
  generalize g.val 0 0 = a at *
  generalize g.val 0 1 = b at *
  generalize g.val 1 0 = c at *
  generalize g.val 1 1 = d at *
  by_cases hlt : modulus c < modulus d
  · simp only [if_pos hlt]
    have hd : d ≠ 0 := fun h => by
      rw [h, modulus_zero] at hlt
      exact absurd hlt (by simp)
    by_cases hc : c = 0
    · subst hc
      have ha : a ≠ 0 := fun h => hD (by rw [hdet, h]; ring)
      exact rW_zero hχ hd ha (by rw [hdet]; ring) u
    · rw [rW_ne hχ hD hc u]
      have hδ : d / c ∉ 𝒪[F] := fun h => by
        have h1 := modulus_le_one_iff.2 h
        rw [div_eq_mul_inv, modulus_mul, modulus_inv] at h1
        have hp := modulus_pos hc
        have := (mul_inv_le_iff₀ hp).1 h1
        rw [one_mul] at this
        exact absurd hlt (not_lt.2 this)
      rw [J_of_notMem hχ hδ]
      have e1 : ((u⁻¹ : Fˣ) : F) / c / (d / c) = (d * u)⁻¹ := by
        simp only [Units.val_inv_eq_inv_val]
        field_simp
      have e2 : D * u / c / (d / c) = D * u / d := by field_simp
      have e3 : a / c + -(((u⁻¹ : Fˣ) : F) / c * (D * u / c) / (d / c)) = b / d := by
        simp only [Units.val_inv_eq_inv_val]
        rw [hdet]
        field_simp
        ring
      have e4 : (((modulus c : ℝ)⁻¹ : ℝ) : ℂ) * (((modulus (d / c) : ℝ)⁻¹ : ℝ) : ℂ) =
          (((modulus d : ℝ)⁻¹ : ℝ) : ℂ) := by
        have hdp : (modulus d : ℝ) ≠ 0 := by exact_mod_cast modulus_ne_zero hd
        have hcp : (modulus c : ℝ) ≠ 0 := by exact_mod_cast modulus_ne_zero hc
        rw [div_eq_mul_inv, modulus_mul, modulus_inv, ← Complex.ofReal_mul]
        congr 1
        push_cast
        field_simp
      rw [e1, e2, ← e3, AddChar.map_add_eq_mul, Circle.coe_mul, ← e4]
      ring
  · simp only [if_neg hlt]
    have hle := not_lt.1 hlt
    have hc : c ≠ 0 := fun h => by
      rw [h, modulus_zero] at hle
      have hd0 : d = 0 := by
        by_contra hd
        exact absurd (modulus_pos hd) (not_lt.2 hle)
      exact hD (by rw [hdet, h, hd0]; ring)
    rw [rW_ne hχ hD hc u]
    have hδ : d / c ∈ 𝒪[F] := by
      rw [← modulus_le_one_iff, div_eq_mul_inv, modulus_mul, modulus_inv]
      exact mul_inv_le_one_of_le₀ hle (le_of_lt (modulus_pos hc))
    rw [J_of_mem hχ hδ]
    have e1 : ((u⁻¹ : Fˣ) : F) / c = (c * u)⁻¹ := by
      simp only [Units.val_inv_eq_inv_val]
      field_simp
    rw [e1]
    ring

end GlobalTheory.CompanionTheory.SphTheta.SplitRW
