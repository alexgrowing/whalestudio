import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.AbsPInfModuleSection
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.PFinInvModuleSectionMul

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.eisensteinGrowth

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem arch_part (ξ : Fin 2 → F) (z : Ideles F) (M M' : Matrix (Fin 2) (Fin 2) (Ad F)) (hM : M * M' = 1)
    (p : InfinitePlace F) (j : Fin 2) :
    |sig p (ξ j)| ≤ max |UpperTheory.V.TR.pInf F ((rowA ξ ᵥ* ((z : Ad F) • M)) 0) p|
        |UpperTheory.V.TR.pInf F ((rowA ξ ᵥ* ((z : Ad F) • M)) 1) p| *
      |UpperTheory.V.TR.pInf F ((z⁻¹ : Ideles F) : Ad F) p| * mn M' := by
  set v := rowA ξ ᵥ* ((z : Ad F) • M) with hv
  have hz : (z : Ad F) * ((z⁻¹ : Ideles F) : Ad F) = 1 := Units.mul_inv z
  have key : rowA ξ = v ᵥ* (((z⁻¹ : Ideles F) : Ad F) • M') := by
    rw [hv, Matrix.vecMul_vecMul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hM, hz, one_smul,
      Matrix.vecMul_one]
  have hj' : algebraMap F (Ad F) (ξ j) = ∑ i, v i * (((z⁻¹ : Ideles F) : Ad F) * M' i j) := by
    have := congrFun key j
    simpa [rowA, Matrix.vecMul, dotProduct, Matrix.smul_apply] using this
  have hj : sig p (ξ j) = ∑ i, UpperTheory.V.TR.pInf F (v i) p *
      (UpperTheory.V.TR.pInf F ((z⁻¹ : Ideles F) : Ad F) p * UpperTheory.V.TR.pInf F (M' i j) p) := by
    rw [sig, hj', map_sum, Finset.sum_apply]
    simp only [map_mul, Pi.mul_apply]
  set ρ := max |UpperTheory.V.TR.pInf F (v 0) p| |UpperTheory.V.TR.pInf F (v 1) p|
  set ζ := |UpperTheory.V.TR.pInf F ((z⁻¹ : Ideles F) : Ad F) p|
  have hρ : ∀ i, |UpperTheory.V.TR.pInf F (v i) p| ≤ ρ := by
    intro i
    fin_cases i
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hM' : ∀ i, |UpperTheory.V.TR.pInf F (M' i j) p| ≤ ‖UpperTheory.V.TR.pInf F (M' i j)‖ := by
    intro i
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm (UpperTheory.V.TR.pInf F (M' i j)) p
  rw [hj]
  calc |∑ i, UpperTheory.V.TR.pInf F (v i) p *
        (UpperTheory.V.TR.pInf F ((z⁻¹ : Ideles F) : Ad F) p * UpperTheory.V.TR.pInf F (M' i j) p)|
      ≤ ∑ i, |UpperTheory.V.TR.pInf F (v i) p *
        (UpperTheory.V.TR.pInf F ((z⁻¹ : Ideles F) : Ad F) p * UpperTheory.V.TR.pInf F (M' i j) p)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ρ * (ζ * ‖UpperTheory.V.TR.pInf F (M' i j)‖) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_mul]
        exact mul_le_mul (hρ i) (mul_le_mul_of_nonneg_left (hM' i) (abs_nonneg _))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) ((abs_nonneg _).trans (hρ 0))
    _ = ρ * ζ * ∑ i, ‖UpperTheory.V.TR.pInf F (M' i j)‖ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ ≤ ρ * ζ * mn M' := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg ((abs_nonneg _).trans (hρ 0)) (abs_nonneg _))
        refine Finset.sum_le_sum fun i _ => ?_
        exact Finset.single_le_sum (f := fun j => ‖UpperTheory.V.TR.pInf F (M' i j)‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)

theorem term_bound {D' : 𝓞 F} (hD'0 : D' ≠ 0) (m₁ : ℕ) {Ca B : ℝ} (hB1 : 1 ≤ B)
    (hCa : ∀ x y : UpperTheory.V.TR.Rinf F,
      ‖arch x y‖ * ∏ v, ((max |x v| |y v|) ^ 2 * (1 + (max |x v| |y v|) ^ 2) ^ (2 * m₁)) ≤ Ca)
    (ξ : Fin 2 → F) (hξ : ξ ≠ 0) (hint : ∀ j, ∃ r : 𝓞 F, (D' : F) * ξ j = r)
    (a : Ideles F) (ha : ∀ v, ‖((a⁻¹ : Ideles F) : Ad F).1 v‖ ≤ B)
    (t : {r : ℝ // 0 < r}) (ht : 1 ≤ (t : ℝ)) (M M' : Matrix (Fin 2) (Fin 2) (Ad F)) (hM : M * M' = 1) :
    ‖arch (UpperTheory.V.TR.pInf F ((rowA ξ ᵥ* (((moduleSection (w0 F) t * a : Ideles F) : Ad F) • M)) 0))
        (UpperTheory.V.TR.pInf F ((rowA ξ ᵥ* (((moduleSection (w0 F) t * a : Ideles F) : Ad F) • M)) 1))‖ ≤
      Ca * |((Algebra.norm ℚ (D' : F) : ℚ) : ℝ)| ^ 2 *
        B ^ (2 * Fintype.card (InfinitePlace F) + 4 * Fintype.card (InfinitePlace F) * m₁) *
        ((t : ℝ) ^ 2)⁻¹ *
        (1 + mn M') ^ (2 * Fintype.card (InfinitePlace F) + 4 * Fintype.card (InfinitePlace F) * m₁) *
        ((∏ v, (1 + sig v (ξ 0) ^ 2)) ^ m₁)⁻¹ * ((∏ v, (1 + sig v (ξ 1) ^ 2)) ^ m₁)⁻¹ := by
  classical
  set n := Fintype.card (InfinitePlace F) with hn
  set z : Ideles F := moduleSection (w0 F) t * a with hzdef
  set v := rowA ξ ᵥ* ((z : Ad F) • M) with hv
  set ρ : InfinitePlace F → ℝ := fun p => max |UpperTheory.V.TR.pInf F (v 0) p| |UpperTheory.V.TR.pInf F (v 1) p|
    with hρdef
  set ζ : InfinitePlace F → ℝ := fun p => |UpperTheory.V.TR.pInf F ((z⁻¹ : Ideles F) : Ad F) p| with hζdef
  set m' := mn M' with hm'def
  have hm' : 0 ≤ m' := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  set L := (1 + m') * B with hLdef
  have hL1 : 1 ≤ L := by nlinarith
  have hL0 : 0 < L := by linarith
  have hρ0 : ∀ p, 0 ≤ ρ p := fun p => (abs_nonneg _).trans (le_max_left _ _)
  set ND := |((Algebra.norm ℚ (D' : F) : ℚ) : ℝ)| with hND
  have hND0 : 0 ≤ ND := abs_nonneg _
  have ht0 : (0 : ℝ) < t := t.2

  have hzinv : ∀ p, ζ p = (if p = w0 F then (t : ℝ)⁻¹ else 1) * ‖((a⁻¹ : Ideles F) : Ad F).1 p‖ := by
    intro p
    have h1 : (z⁻¹ : Ideles F) = moduleSection (w0 F) t⁻¹ * a⁻¹ := by rw [hzdef, mul_inv, map_inv]
    simp only [hζdef]
    rw [h1, Units.val_mul, map_mul, Pi.mul_apply, abs_mul, abs_pInf_moduleSection, abs_pInf]
    congr 1
  have hζB : ∀ p, ζ p ≤ B := by
    intro p
    rw [hzinv]
    have h1 : (if p = w0 F then (t : ℝ)⁻¹ else 1) ≤ 1 := by
      split_ifs
      · exact inv_le_one_of_one_le₀ ht
      · exact le_rfl
    calc _ ≤ 1 * B := mul_le_mul h1 (ha p) (norm_nonneg _) zero_le_one
      _ = B := one_mul B
  have hζprod : ∏ p, ζ p ≤ (t : ℝ)⁻¹ * B ^ n := by
    have e1 : ∏ p : InfinitePlace F, (if p = w0 F then (t : ℝ)⁻¹ else 1) = (t : ℝ)⁻¹ := by simp
    have e2 : ∏ p, ‖((a⁻¹ : Ideles F) : Ad F).1 p‖ ≤ B ^ n := by
      calc _ ≤ ∏ _p : InfinitePlace F, B :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p _ => ha p
        _ = B ^ n := by rw [Finset.prod_const, Finset.card_univ]
    rw [Finset.prod_congr rfl fun p _ => hzinv p, Finset.prod_mul_distrib, e1]
    exact mul_le_mul_of_nonneg_left e2 (inv_nonneg.2 ht0.le)
  have harch : ∀ p j, |sig p (ξ j)| ≤ ρ p * ζ p * (1 + m') := by
    intro p j
    have := arch_part ξ z M M' hM p j
    calc _ ≤ ρ p * ζ p * m' := this
      _ ≤ ρ p * ζ p * (1 + m') :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (hρ0 p) (abs_nonneg _))
  have hτ : ∀ p j, |sig p (ξ j)| ≤ ρ p * L := by
    intro p j
    calc _ ≤ ρ p * ζ p * (1 + m') := harch p j
      _ ≤ ρ p * B * (1 + m') :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hζB p) (hρ0 p)) (by linarith)
      _ = ρ p * L := by rw [hLdef]; ring

  obtain ⟨j, hj⟩ : ∃ j, ξ j ≠ 0 := by
    by_contra h
    push Not at h
    exact hξ (funext h)
  have h1 := one_le_norm_mul_prod hD'0 hj (hint j)
  set P := ∏ p, ρ p with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun p _ => hρ0 p
  have h2 : ∏ p, |sig p (ξ j)| ≤ P * ((t : ℝ)⁻¹ * B ^ n) * (1 + m') ^ n := by
    calc ∏ p, |sig p (ξ j)| ≤ ∏ p, (ρ p * ζ p * (1 + m')) :=
          Finset.prod_le_prod (fun p _ => abs_nonneg _) fun p _ => harch p j
      _ = P * (∏ p, ζ p) * (1 + m') ^ n := by
          rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      _ ≤ P * ((t : ℝ)⁻¹ * B ^ n) * (1 + m') ^ n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hζprod hP0) (pow_nonneg (by linarith) _)
  have htP : (t : ℝ) ≤ ND * L ^ n * P := by
    have h3 : 1 ≤ ND * (P * ((t : ℝ)⁻¹ * B ^ n) * (1 + m') ^ n) :=
      h1.trans (mul_le_mul_of_nonneg_left h2 hND0)
    have e : ND * (P * ((t : ℝ)⁻¹ * B ^ n) * (1 + m') ^ n) = (ND * L ^ n * P) * (t : ℝ)⁻¹ := by
      rw [hLdef, mul_pow]; ring
    rw [e, le_mul_inv_iff₀ ht0, one_mul] at h3
    exact h3

  set Q := ∏ p, (1 + ρ p ^ 2) with hQ
  have hQ0 : 0 < Q := Finset.prod_pos fun p _ => by positivity
  have hQj : ∀ j, ∏ p, (1 + sig p (ξ j) ^ 2) ≤ Q * L ^ (2 * n) := by
    intro j
    have hp : ∀ p, 1 + sig p (ξ j) ^ 2 ≤ (1 + ρ p ^ 2) * L ^ 2 := by
      intro p
      have h1 : sig p (ξ j) ^ 2 ≤ (ρ p * L) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hτ p j) 2
      have h2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
      nlinarith [sq_nonneg (ρ p)]
    calc _ ≤ ∏ p, ((1 + ρ p ^ 2) * L ^ 2) :=
          Finset.prod_le_prod (fun p _ => by positivity) fun p _ => hp p
      _ = Q * L ^ (2 * n) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul]
  have hC := hCa (UpperTheory.V.TR.pInf F (v 0)) (UpperTheory.V.TR.pInf F (v 1))
  have eprod : ∏ p, ((max |UpperTheory.V.TR.pInf F (v 0) p| |UpperTheory.V.TR.pInf F (v 1) p|) ^ 2 *
      (1 + (max |UpperTheory.V.TR.pInf F (v 0) p| |UpperTheory.V.TR.pInf F (v 1) p|) ^ 2) ^ (2 * m₁)) =
      P ^ 2 * Q ^ (2 * m₁) := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_pow]
  rw [eprod] at hC
  set X := ‖arch (UpperTheory.V.TR.pInf F (v 0)) (UpperTheory.V.TR.pInf F (v 1))‖ with hX
  have hX0 : 0 ≤ X := norm_nonneg _
  set Pi0 := ∏ p, (1 + sig p (ξ 0) ^ 2) with hPi0
  set Pi1 := ∏ p, (1 + sig p (ξ 1) ^ 2) with hPi1
  have hPi0p : 0 < Pi0 := Finset.prod_pos fun p _ => by positivity
  have hPi1p : 0 < Pi1 := Finset.prod_pos fun p _ => by positivity
  have hA : (t : ℝ) ^ 2 ≤ ND ^ 2 * L ^ (2 * n) * P ^ 2 := by
    calc (t : ℝ) ^ 2 ≤ (ND * L ^ n * P) ^ 2 := pow_le_pow_left₀ ht0.le htP 2
      _ = ND ^ 2 * L ^ (2 * n) * P ^ 2 := by ring
  have hB' : Pi0 ^ m₁ * Pi1 ^ m₁ ≤ Q ^ (2 * m₁) * L ^ (4 * n * m₁) := by
    have e0 := pow_le_pow_left₀ hPi0p.le (hQj 0) m₁
    have e1 := pow_le_pow_left₀ hPi1p.le (hQj 1) m₁
    calc _ ≤ (Q * L ^ (2 * n)) ^ m₁ * (Q * L ^ (2 * n)) ^ m₁ :=
          mul_le_mul e0 e1 (pow_nonneg hPi1p.le _) (pow_nonneg (mul_nonneg hQ0.le (pow_nonneg hL0.le _)) _)
      _ = Q ^ (2 * m₁) * L ^ (4 * n * m₁) := by ring
  have key : X * ((t : ℝ) ^ 2 * (Pi0 ^ m₁ * Pi1 ^ m₁)) ≤ Ca * ND ^ 2 * L ^ (2 * n + 4 * n * m₁) := by
    calc X * ((t : ℝ) ^ 2 * (Pi0 ^ m₁ * Pi1 ^ m₁))
        ≤ X * ((ND ^ 2 * L ^ (2 * n) * P ^ 2) * (Q ^ (2 * m₁) * L ^ (4 * n * m₁))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hA hB' (mul_nonneg (pow_nonneg hPi0p.le _) (pow_nonneg hPi1p.le _))
            (mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg hL0.le _)) (sq_nonneg _))) hX0
      _ = ND ^ 2 * L ^ (2 * n + 4 * n * m₁) * (X * (P ^ 2 * Q ^ (2 * m₁))) := by ring
      _ ≤ ND ^ 2 * L ^ (2 * n + 4 * n * m₁) * Ca :=
          mul_le_mul_of_nonneg_left hC (mul_nonneg (sq_nonneg _) (pow_nonneg hL0.le _))
      _ = Ca * ND ^ 2 * L ^ (2 * n + 4 * n * m₁) := by ring
  have hden : 0 < (t : ℝ) ^ 2 * (Pi0 ^ m₁ * Pi1 ^ m₁) :=
    mul_pos (pow_pos ht0 2) (mul_pos (pow_pos hPi0p _) (pow_pos hPi1p _))
  calc X ≤ Ca * ND ^ 2 * L ^ (2 * n + 4 * n * m₁) / ((t : ℝ) ^ 2 * (Pi0 ^ m₁ * Pi1 ^ m₁)) :=
        (le_div_iff₀ hden).mpr key
    _ = _ := by
        rw [hLdef, mul_pow, div_eq_mul_inv, mul_inv, mul_inv]
        ring

theorem core {Ψ : (Fin 2 → Ad F) → ℂ} {e : HeightOneSpectrum (𝓞 F) → ℤ} (D : 𝓞 F) (hD0 : D ≠ 0)
    (hD : ∀ w, ∀ x : w.adicCompletion F, Valued.v x ≤ WithZero.exp (e w) →
      Valued.v (algebraMap F (w.adicCompletion F) (D : F) * x) ≤ 1)
    (hΨ : ∀ v, ‖Ψ v‖ ≤ ‖arch (UpperTheory.V.TR.pInf F (v 0)) (UpperTheory.V.TR.pInf F (v 1))‖ *
      (open Classical in if boxP e v then 1 else 0))
    {K : Set (Ideles F)} (hK : IsCompact K) (Mf' : Matrix (Fin 2) (Fin 2) (Af F)) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ a ∈ K, ∀ t : {r : ℝ // 0 < r}, 1 ≤ (t : ℝ) →
      ∀ M M' : Matrix (Fin 2) (Fin 2) (Ad F), M * M' = 1 → M'.map (pFin F) = Mf' →
      Summable (fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} =>
        ‖Ψ (rowA ξ.1 ᵥ* (((moduleSection (w0 F) t * a : Ideles F) : Ad F) • M))‖) ∧
      ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
        ‖Ψ (rowA ξ.1 ᵥ* (((moduleSection (w0 F) t * a : Ideles F) : Ad F) • M))‖ ≤
          C * ((t : ℝ) ^ 2)⁻¹ * (1 + mn M') ^ N := by
  classical
  obtain ⟨D', hD'0, hfin⟩ := fin_part D hD hK Mf' hD0
  obtain ⟨m₁, hsum⟩ := summable_beta D' hD'0
  obtain ⟨Ca, hCa0, hCa⟩ := arch_bound (F := F) 2 (2 * m₁)
  obtain ⟨B, hB1, hB⟩ := exists_bound_inf hK
  set n := Fintype.card (InfinitePlace F) with hn
  set N := 2 * n + 4 * n * m₁ with hN
  set β : F → ℝ := fun x =>
    if ∃ r : 𝓞 F, (D' : F) * x = r then ((∏ v, (1 + sig v x ^ 2)) ^ m₁)⁻¹ else 0 with hβ
  have hβ0 : ∀ x, 0 ≤ β x := by
    intro x
    simp only [hβ]
    split_ifs
    · exact inv_nonneg.2 (pow_nonneg (Finset.prod_nonneg fun v _ => by positivity) _)
    · exact le_rfl
  have hG : Summable (fun ξ : Fin 2 → F => β (ξ 0) * β (ξ 1)) := by
    have h := hsum.mul_of_nonneg hsum hβ0 hβ0
    exact (finTwoArrowEquiv F).summable_iff.mpr h
  set S := ∑' ξ : Fin 2 → F, β (ξ 0) * β (ξ 1) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun ξ => mul_nonneg (hβ0 _) (hβ0 _)
  set ND := |((Algebra.norm ℚ (D' : F) : ℚ) : ℝ)| with hND
  have hND0 : 0 ≤ ND := abs_nonneg _
  have hBN : 0 ≤ B ^ N := pow_nonneg (by linarith) _
  refine ⟨Ca * ND ^ 2 * B ^ N * S, N, mul_nonneg (mul_nonneg (mul_nonneg hCa0.le (sq_nonneg _)) hBN) hS0,
    fun a ha t ht M M' hM hM' => ?_⟩
  have hm' : 0 ≤ mn M' := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  set c := Ca * ND ^ 2 * B ^ N * ((t : ℝ) ^ 2)⁻¹ * (1 + mn M') ^ N with hc
  have hc0 : 0 ≤ c := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCa0.le (sq_nonneg _)) hBN)
    (inv_nonneg.2 (sq_nonneg _))) (pow_nonneg (by linarith) _)
  have hbound : ∀ ξ : {ξ : Fin 2 → F // ξ ≠ 0},
      ‖Ψ (rowA ξ.1 ᵥ* (((moduleSection (w0 F) t * a : Ideles F) : Ad F) • M))‖ ≤
        c * (β (ξ.1 0) * β (ξ.1 1)) := by
    intro ξ
    refine (hΨ _).trans ?_
    split_ifs with hbox
    · have hint := hfin a ha t ξ.1 M M' hM hM' hbox
      have hT := term_bound hD'0 m₁ hB1 hCa ξ.1 ξ.2 hint a (fun v => (hB a ha v).2) t ht M M' hM
      have e0 : β (ξ.1 0) = ((∏ v, (1 + sig v (ξ.1 0) ^ 2)) ^ m₁)⁻¹ := if_pos (hint 0)
      have e1 : β (ξ.1 1) = ((∏ v, (1 + sig v (ξ.1 1) ^ 2)) ^ m₁)⁻¹ := if_pos (hint 1)
      rw [mul_one, e0, e1, hc]
      calc _ ≤ _ := hT
        _ = _ := by ring
    · rw [mul_zero]
      exact mul_nonneg hc0 (mul_nonneg (hβ0 _) (hβ0 _))
  have hGs : Summable (fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} => β (ξ.1 0) * β (ξ.1 1)) :=
    hG.subtype {ξ | ξ ≠ 0}
  have hsum2 := hGs.mul_left c
  have hs : Summable (fun ξ : {ξ : Fin 2 → F // ξ ≠ 0} =>
      ‖Ψ (rowA ξ.1 ᵥ* (((moduleSection (w0 F) t * a : Ideles F) : Ad F) • M))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hsum2
  refine ⟨hs, ?_⟩
  calc ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0},
        ‖Ψ (rowA ξ.1 ᵥ* (((moduleSection (w0 F) t * a : Ideles F) : Ad F) • M))‖
      ≤ ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, c * (β (ξ.1 0) * β (ξ.1 1)) :=
        hs.tsum_le_tsum hbound hsum2
    _ = c * ∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, β (ξ.1 0) * β (ξ.1 1) := tsum_mul_left
    _ ≤ c * S := mul_le_mul_of_nonneg_left
        (Summable.tsum_subtype_le (fun ξ : Fin 2 → F => β (ξ 0) * β (ξ 1)) {ξ | ξ ≠ 0}
          (fun ξ => mul_nonneg (hβ0 _) (hβ0 _)) hG) hc0
    _ = Ca * ND ^ 2 * B ^ N * S * ((t : ℝ) ^ 2)⁻¹ * (1 + mn M') ^ N := by rw [hc]; ring

end UpperTheory.HilbertEisensteinWeightOne.eisensteinGrowth
