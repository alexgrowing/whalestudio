import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StWWFibrePoly
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PDiagFibreMoment
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace DiagonalFibreFubini

def wordCoef (i : ℕ) : ℕ → Fin 2 → ℝ := fun n =>
  if n = 0 then ![1, -1] else if n = 1 then ![0, 1] else if n < 2 + 2 * i then ![1, 0] else ![0, 1]

def topCoef : ℕ → Fin 2 → ℝ := fun n => if n = 0 then ![1, 0] else ![0, 1]

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem cons_pot_word (D k i : ℕ) (hik : i < k) (X₀ X₁ A₀ : HermLine ι) :
    (Fin.cons (α := fun _ => ((Σ k, ι k) → ℂ) → ℝ) (fun z => Real.log (X₀.h z) - Real.log (X₁.h z))
        (pot (word D k i X₀ X₁ A₀)) : Fin (D + 1) → ((Σ k, ι k) → ℂ) → ℝ) =
      wwLinPot X₀ X₁ A₀ k (wordCoef i) := by
  funext j z
  refine Fin.cases ?_ (fun j => ?_) j
  · have h0 : (0 : ℕ) < 2 * k := by omega
    simp [wwLinPot, wordCoef, h0]
    ring
  · simp only [Fin.cons_succ, pot, word, wwLinPot, wordCoef, Fin.val_succ]
    split_ifs <;> first | contradiction | omega | simp

theorem linProd_word (k i : ℕ) (hik : i < k) :
    wwLinProd k (wordCoef i) = (X 0 - X 1) * X 0 ^ (2 * i) * X 1 ^ (2 * k - 1 - 2 * i) := by
  obtain ⟨r, hr⟩ : ∃ r, 2 * k = 2 + 2 * i + r := ⟨2 * k - 2 - 2 * i, by omega⟩
  rw [wwLinProd, hr, Finset.prod_range_add, Finset.prod_range_add]
  have h1 : ∏ x ∈ Finset.range 2, (C (wordCoef i x 0) * X 0 + C (wordCoef i x 1) * X 1 : MvPolynomial (Fin 2) ℝ) =
      (X 0 - X 1) * X 1 := by
    simp [Finset.prod_range_succ, wordCoef]
    ring
  have h2 : ∏ x ∈ Finset.range (2 * i),
      (C (wordCoef i (2 + x) 0) * X 0 + C (wordCoef i (2 + x) 1) * X 1 : MvPolynomial (Fin 2) ℝ) = X 0 ^ (2 * i) := by
    rw [← Finset.card_range (2 * i), ← Finset.prod_const]
    refine Finset.prod_congr (by rw [Finset.card_range]) fun x hx => ?_
    have hx' : x < 2 * i := Finset.mem_range.1 hx
    simp [wordCoef, show 2 + x ≠ 1 by omega, show 2 + x < 2 + 2 * i by omega]
  have h3 : ∏ x ∈ Finset.range r,
      (C (wordCoef i (2 + 2 * i + x) 0) * X 0 + C (wordCoef i (2 + 2 * i + x) 1) * X 1 : MvPolynomial (Fin 2) ℝ) =
        X 1 ^ r := by
    rw [← Finset.card_range r, ← Finset.prod_const]
    refine Finset.prod_congr (by rw [Finset.card_range]) fun x _ => ?_
    simp [wordCoef, show 2 + 2 * i + x ≠ 1 by omega,
      show ¬ 2 + 2 * i + x < 2 + 2 * i by omega]
  rw [h1, h2, h3, show 2 + 2 * i + r - 1 - 2 * i = r + 1 by omega, pow_succ]
  ring

theorem cons_pot_top (D k : ℕ) (hk : 1 ≤ k) (X₀ X₁ A₀ : HermLine ι) :
    pot (Fin.cons X₀ (mix (2 * k - 1) X₁ A₀ : Fin D → HermLine ι) : Fin (D + 1) → HermLine ι) =
      wwLinPot X₀ X₁ A₀ k topCoef := by
  funext j z
  refine Fin.cases ?_ (fun j => ?_) j
  · have h0 : (0 : ℕ) < 2 * k := by omega
    simp [pot, wwLinPot, topCoef, h0]
  · simp only [pot, Fin.cons_succ, mix, wwLinPot, topCoef, Fin.val_succ]
    split_ifs <;> first | contradiction | omega | simp

theorem linProd_top (k : ℕ) (hk : 1 ≤ k) : wwLinProd k topCoef = X 0 * X 1 ^ (2 * k - 1) := by
  obtain ⟨r, hr⟩ : ∃ r, 2 * k = 1 + r := ⟨2 * k - 1, by omega⟩
  rw [wwLinProd, hr, Finset.prod_range_add, show 1 + r - 1 = r by omega]
  have h1 : ∏ x ∈ Finset.range 1, (C (topCoef x 0) * X 0 + C (topCoef x 1) * X 1 : MvPolynomial (Fin 2) ℝ) = X 0 := by
    simp [topCoef]
  have h2 : ∏ x ∈ Finset.range r, (C (topCoef (1 + x) 0) * X 0 + C (topCoef (1 + x) 1) * X 1 : MvPolynomial (Fin 2) ℝ) =
      X 1 ^ r := by
    rw [← Finset.card_range r, ← Finset.prod_const]
    refine Finset.prod_congr (by rw [Finset.card_range]) fun x _ => ?_
    simp [topCoef]
  rw [h1, h2]

theorem pderiv_top (N : ℕ) :
    pderiv 0 (pderiv 1 (X 0 * X 1 ^ (N + 1) : MvPolynomial (Fin 2) ℝ)) = C ((N + 1 : ℕ) : ℝ) * X 1 ^ N := by
  simp [Derivation.leibniz, Derivation.leibniz_pow]

def sndHom : (S2 → ℝ) →+* (S2 × S2 → ℝ) :=
  RingHom.pi fun p => Pi.evalRingHom (fun _ : S2 => ℝ) p.2

theorem dotPoly_snd : dotPoly (Prod.snd : S2 × S2 → S2) = map sndHom (dotPoly (id : S2 → S2)) := by
  simp only [dotPoly, map_sum, map_mul, map_X, map_C]
  rfl

theorem moment_top (k : ℕ) (hk : 1 ≤ k) :
    wwFibreMoment (fun _ => 1) (X 0 * X 1 ^ (2 * k - 1)) = -pushMomentPoly k := by
  have := FibreLocal.isProbabilityMeasure_sphere
  obtain ⟨N, hN⟩ : ∃ N, 2 * k - 1 = N + 1 := ⟨2 * k - 2, by omega⟩
  have hN2 : 2 * k - 2 = N := by omega
  have hc : ((N + 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 1 := by
    have h2 : ((N + 1 + 1 : ℕ) : ℝ) = ((2 * k : ℕ) : ℝ) := by rw [show N + 1 + 1 = 2 * k by omega]
    push_cast at h2 ⊢
    linarith
  rw [wwFibreMoment, hN, pderiv_top, pushMomentPoly, hN2]
  ext m
  rw [DiagFibreMoment.coeff_momentPoly, coeff_neg, coeff_smul, DiagFibreMoment.coeff_momentPoly]
  have hpt : ∀ p : S2 × S2,
      coeff m (aeval ![dotPoly (Prod.fst : S2 × S2 → S2), dotPoly Prod.snd]
        (C ((N + 1 : ℕ) : ℝ) * X 1 ^ N : MvPolynomial (Fin 2) ℝ)) p =
        ((N + 1 : ℕ) : ℝ) * coeff m (dotPoly (id : S2 → S2) ^ N) p.2 := by
    intro p
    rw [map_mul, aeval_C, map_pow, aeval_X, Matrix.cons_val_one, Matrix.cons_val_fin_one, dotPoly_snd, ← map_pow,
      MvPolynomial.algebraMap_apply, coeff_C_mul, coeff_map]
    rfl
  simp_rw [hpt]
  have hsnd := integral_fun_snd (μ := sphereMeasure) (ν := sphereMeasure)
    (fun y : S2 => (1 : ℝ) * (((N + 1 : ℕ) : ℝ) * coeff m (dotPoly (id : S2 → S2) ^ N) y))
  rw [hsnd, probReal_univ, one_smul]
  simp only [one_mul, smul_eq_mul]
  rw [integral_const_mul, hc]
  ring

end DiagonalFibreFubini

open DiagonalFibreFubini in

theorem DiagFibreFubini.proof (h : WWFibrePoly.Statement) : DiagFibreFubini.Statement := by
  intro D S X A X₀ X₁ A₀ hX hA hAb p0 p1 pA k hk hkD
  obtain ⟨Λ, hΛ⟩ := h D S X A X₀ X₁ A₀ hX hA hAb p0 p1 pA k hk hkD
  refine ⟨Λ, fun i hi => ?_, ?_⟩
  · rw [diagInt, cons_pot_word D k i hi, (hΛ _).1, linProd_word k i hi]
    rfl
  · rw [cons_pot_top D k hk, (hΛ _).2, linProd_top k hk, moment_top k hk, map_neg]
    ring

end

end GroundTheory.Heights₂.Heights.Inter
