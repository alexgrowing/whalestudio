import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormCharpoly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace FibreNormCharpoly

theorem aeval_mul_of_isHomogeneous {σ' Ω : Type*} [Field Ω] [CharZero Ω] {p : MvPolynomial σ' ℚ} {d : ℕ}
    (hp : p.IsHomogeneous d) (μ : Ω) (f : σ' → Ω) :
    aeval (fun j => μ * f j) p = μ ^ d * aeval f p := by
  classical
  conv_lhs => rw [p.as_sum]
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial]
  have hdeg : ∑ i ∈ m.support, m i = d := by
    have := hp (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem eq_zero_of_isNormForms {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    [CharZero Ω] {y : (Σ k, ι k) → Ω} {D : ℕ} {L : Fin (D + 1) → MRing ι} {m : ℕ} {s : Ω}
    {c : ℕ → MvPolynomial (Fin (D + 1)) ℚ} (σ : Ω →+* Ω) (μ : Ω) (hμ0 : μ ≠ 0)
    (hL : ∀ j, σ (aeval y (L j)) = μ * aeval y (L j)) (hμ : ∀ d, 0 < d → μ ^ d ≠ 1) (hm : 0 < m)
    (h : IsNormForms y L m s c) : s = 0 := by
  classical
  obtain ⟨hfd, hc0, hhom, hcp⟩ := h
  set P := pullField y L with hP
  set n := Module.finrank P Ω with hn

  have hfix : ∀ x ∈ P, σ x = x := by
    intro x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, j, hj, rfl⟩ := hx
      rw [map_div₀, hL, hL, mul_div_mul_left _ _ hμ0]
    | algebraMap r => exact σ.toRatAlgHom.commutes r
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  set v : ℕ → Ω := fun i => aeval (fun j => aeval y (L j)) (c i) with hv

  have hσv : ∀ i ≤ n, σ (v i) = μ ^ (i * m) * v i := by
    intro i hi
    have h1 := DFunLike.congr_fun (MvPolynomial.comp_aeval (R := ℚ) (fun j => aeval y (L j)) σ.toRatAlgHom) (c i)
    simp only [AlgHom.comp_apply] at h1
    change σ (v i) = _ at h1
    rw [h1]
    change aeval (fun j => σ (aeval y (L j))) (c i) = _
    simp only [hL]
    exact aeval_mul_of_isHomogeneous (hhom i hi) μ _

  have hcoeff : ∀ i ≤ n,
      ((LinearMap.charpoly (Algebra.lmul P Ω s)).map (algebraMap P Ω)).coeff (n - i) = v i := by
    intro i hi
    rw [hcp, Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro b hb hbi
      rw [Polynomial.coeff_C_mul_X_pow, if_neg]
      have := Finset.mem_range.mp hb
      omega
    · intro hi'
      exact absurd (Finset.mem_range.mpr (by omega)) hi'
  have hzero : ∀ i, 1 ≤ i → i ≤ n → v i = 0 := by
    intro i h1 hi
    have hfixv : σ (v i) = v i := by
      rw [← hcoeff i hi, Polynomial.coeff_map]
      exact hfix _ (SetLike.coe_mem _)
    rw [hσv i hi] at hfixv
    have hne : μ ^ (i * m) - 1 ≠ 0 := sub_ne_zero.mpr (hμ _ (Nat.mul_pos (by omega) hm))
    have : (μ ^ (i * m) - 1) * v i = 0 := by rw [sub_mul, hfixv, one_mul, sub_self]
    exact (mul_eq_zero.mp this).resolve_left hne

  have hX : (LinearMap.charpoly (Algebra.lmul P Ω s)).map (algebraMap P Ω) =
      (Polynomial.X ^ n : Polynomial P).map (algebraMap P Ω) := by
    rw [hcp, Finset.sum_eq_single 0]
    · have : v 0 = 1 := by simp [hv, hc0]
      change Polynomial.C (v 0) * _ = _
      rw [this, Polynomial.map_pow, Polynomial.map_X]
      simp
    · intro b hb hb0
      change Polynomial.C (v b) * _ = 0
      rw [hzero b (by omega) (by have := Finset.mem_range.mp hb; omega), map_zero, zero_mul]
    · intro h0
      exact absurd (Finset.mem_range.mpr (by omega)) h0
  have hchar : LinearMap.charpoly (Algebra.lmul P Ω s) = Polynomial.X ^ n :=
    Polynomial.map_injective _ (algebraMap P Ω).injective hX

  have hCH := LinearMap.aeval_self_charpoly (Algebra.lmul P Ω s)
  rw [hchar, Polynomial.aeval_X_pow, ← map_pow] at hCH
  have h1 := LinearMap.congr_fun hCH 1
  change s ^ n * 1 = 0 at h1
  rw [mul_one] at h1
  exact (pow_eq_zero_iff'.mp h1).1

end FibreNormCharpoly

namespace ProjLine

open ProjLine

def swapIx : (Σ k, GlobalTheory (Fin 2) k) → (Σ k, GlobalTheory (Fin 2) k) := fun p => ⟨(), Fin.rev p.2⟩

theorem swapIx_injective : Function.Injective swapIx := by
  rintro ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩ h
  have : Fin.rev i = Fin.rev j := by simpa [swapIx] using h
  rw [Fin.rev_inj] at this
  rw [this]

theorem swap_injective :
    Function.Injective ((algebraMap (MRing (GlobalTheory (Fin 2))) Kfr).comp (rename swapIx).toRingHom) :=
  (IsFractionRing.injective (MRing (GlobalTheory (Fin 2))) Kfr).comp (rename_injective _ swapIx_injective)

def swapK : Kfr →+* Kfr := IsFractionRing.lift swap_injective

theorem swapK_Xk (i : Fin 2) : swapK (Xk i) = Xk (Fin.rev i) := by
  simp [swapK, Xk, IsFractionRing.lift_algebraMap, swapIx]

theorem swapK_u : swapK u = u⁻¹ := by
  rw [u, map_div₀, swapK_Xk, swapK_Xk, inv_div]
  rfl

theorem closure_le_comap_swapK :
    Subfield.closure ({u} : Set Kfr) ≤ (Subfield.closure ({u} : Set Kfr)).comap swapK := by
  rw [Subfield.closure_le]
  rintro _ rfl
  show swapK u ∈ Subfield.closure ({u} : Set Kfr)
  rw [swapK_u]
  exact inv_mem (Subfield.subset_closure rfl)

def swapF : FnField →+* FnField :=
  (swapK.comp incl).codRestrict (Subfield.closure ({u} : Set Kfr)) fun x => closure_le_comap_swapK x.2

theorem uF_ne_zero : uF ≠ 0 := by
  intro h
  have h' := congrArg incl h
  rw [map_zero] at h'
  exact div_ne_zero (Xk_ne_zero 1) (Xk_ne_zero 0) h'

theorem swapF_uF : swapF uF = uF⁻¹ := by
  apply Subtype.ext
  change swapK u = incl uF⁻¹
  rw [swapK_u, map_inv₀]
  rfl

theorem uF_pow_ne_one {k : ℕ} (hk : 0 < k) : uF ^ k ≠ 1 := by
  intro h
  have h' := congrArg incl h
  rw [map_pow, map_one] at h'
  change (Xk 1 / Xk 0) ^ k = 1 at h'
  rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ (Xk_ne_zero 0)), ← map_pow, ← map_pow] at h'
  have h2 := IsFractionRing.injective (MRing (GlobalTheory (Fin 2))) Kfr h'
  have h3 := congrArg (eval (fun p : (Σ k, GlobalTheory (Fin 2) k) => if p.2 = 1 then (1 : ℤ) else 0)) h2
  simp [zero_pow hk.ne'] at h3

def Lc : Fin 2 → MRing (GlobalTheory (Fin 2)) :=
  ![X ⟨(), 0⟩ * X ⟨(), 1⟩, X ⟨(), 0⟩ ^ 2 + X ⟨(), 1⟩ ^ 2]

theorem Lc_zero : Lc 0 = X ⟨(), 0⟩ * X ⟨(), 1⟩ := rfl

theorem Lc_one : Lc 1 = X ⟨(), 0⟩ ^ 2 + X ⟨(), 1⟩ ^ 2 := rfl

theorem aeval_Lc_zero : aeval y (Lc 0) = uF := by simp [Lc]

theorem aeval_Lc_one : aeval y (Lc 1) = 1 + uF ^ 2 := by simp [Lc]

theorem swapF_Lc (j : Fin 2) : swapF (aeval y (Lc j)) = (uF ^ 2)⁻¹ * aeval y (Lc j) := by
  have hu := uF_ne_zero
  fin_cases j
  · show swapF (aeval y (Lc 0)) = _ * aeval y (Lc 0)
    rw [aeval_Lc_zero, swapF_uF]
    field_simp
  · show swapF (aeval y (Lc 1)) = _ * aeval y (Lc 1)
    rw [aeval_Lc_one, map_add, map_one, map_pow, swapF_uF]
    field_simp
    ring

theorem isMultiHomog_Lc (j : Fin 2) : IsMultiHomog (Lc j) (fun _ : Unit => 2) := by
  have h1 : ∀ i : Fin 2, IsMultiHomog (X ⟨(), i⟩ : MRing (GlobalTheory (Fin 2))) (fun _ : Unit => 1) := by
    intro i
    convert isMultiHomog_X (ι := GlobalTheory (Fin 2)) ⟨(), i⟩ using 1
    funext k
    simp
  have h2 : ∀ i i' : Fin 2, IsMultiHomog (X ⟨(), i⟩ * X ⟨(), i'⟩ : MRing (GlobalTheory (Fin 2))) (fun _ : Unit => 2) := by
    intro i i'
    convert mhMul (h1 i) (h1 i') using 1
    funext k
    simp
  match j with
  | 0 => rw [Lc_zero]; exact h2 0 1
  | 1 => rw [Lc_one, pow_two, pow_two]; exact mhAdd (h2 0 0) (h2 1 1)

theorem Lc_no_common_zero : ∀ z ∈ mcPts (mCoordIdeal (ι := GlobalTheory (Fin 2)) y), ∃ j : Fin 2,
    eval z (map (Int.castRingHom ℂ) (Lc j)) ≠ 0 := by
  intro z hz
  by_contra hcon
  push Not at hcon
  have h0 := hcon 0
  have h1 := hcon 1
  simp [Lc] at h0 h1
  obtain ⟨i, hi⟩ := hz.1 ()
  rcases h0 with h0 | h0
  · rw [h0] at h1
    have : z ⟨(), 1⟩ = 0 := by simpa using h1
    fin_cases i <;> simp_all
  · rw [h0] at h1
    have : z ⟨(), 0⟩ = 0 := by simpa using h1
    fin_cases i <;> simp_all

theorem one_mem_chartLatNm : (1 : FnField) ∈ chartLatNm (ι := GlobalTheory (Fin 2)) y (fun _ => ((1 * 2 : ℕ) : ℤ)) 1 := by
  intro c hc
  have hmem : ∀ x ∈ chartRingZ y c, x ∈ integralClosure (chartRingZ y c) FnField :=
    fun x hx => isIntegral_algebraMap (R := chartRingZ y c) (A := FnField) (x := ⟨x, hx⟩)
  apply hmem
  rw [one_mul, Fintype.prod_unique]
  have hq : ∀ p : (Σ k, GlobalTheory (Fin 2) k), y p / y ⟨p.1, c p.1⟩ ∈ chartRingZ y c :=
    fun p => Algebra.subset_adjoin ⟨p, rfl⟩
  have hc0 := hq ⟨(), 0⟩
  simp only [y_zero] at hc0
  obtain h | h : c default = 0 ∨ c default = 1 := by
    rcases Fin.exists_fin_two.mp ⟨c default, rfl⟩ with h | h <;> simp_all
  · rw [h, y_zero, one_zpow]
    exact one_mem _
  · have e : y ⟨default, c default⟩ ^ (-((1 : ℕ) * ((1 * 2 : ℕ) : ℤ))) = (1 / y ⟨(), c ()⟩) ^ 2 := by
      simp [zpow_neg, h]
    rw [e]
    exact pow_mem hc0 2

end ProjLine

namespace FibreNormCharpoly

open ProjLine

theorem statement_false : ¬ FibreNormCharpoly.Statement := by
  intro H
  have hyp := FibreNormCharpoly.hyps_inhabited
  obtain ⟨-, hH⟩ := H Unit (GlobalTheory (Fin 2)) FnField y 1 (fun _ => 2) Lc 1 hyp.2.1.1 hyp.2.1.2
    (fun _ => by norm_num) isMultiHomog_Lc Lc_no_common_zero
  obtain ⟨c, hc, -⟩ := hH 1 1 one_mem_chartLatNm
  have hμ : ∀ d, 0 < d → ((uF ^ 2)⁻¹) ^ d ≠ 1 := by
    intro d hd h
    rw [inv_pow, inv_eq_one, ← pow_mul] at h
    exact uF_pow_ne_one (by omega) h
  exact one_ne_zero (eq_zero_of_isNormForms swapF ((uF ^ 2)⁻¹) (inv_ne_zero (pow_ne_zero _ uF_ne_zero))
    swapF_Lc hμ (by norm_num) hc)

end FibreNormCharpoly

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
