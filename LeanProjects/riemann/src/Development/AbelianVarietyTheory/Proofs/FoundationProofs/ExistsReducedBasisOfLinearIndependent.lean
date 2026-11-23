import Mathlib
import ReciprocityTheory.ReducedBases.ExistsRedOf
import ReciprocityTheory.ReducedBases.PrefixProdGeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.IntegralModuleBases.NormGsoSqLeTwoPowMulOfValEqAdd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBimultiplicativeOfSecondQuotConst

noncomputable section

open Finset Module Matrix
open scoped InnerProductSpace TensorProduct MatrixOrder ComplexOrder

namespace GlobalTheory

open ReciprocityTheory.ReducedBases ReciprocityTheory.ReducedBases.T2 ReciprocityTheory.ChartRestriction.G.AR.IntegralModuleBases

section Family

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {d : ℕ}

theorem rpow_half_sq (d : ℕ) : ((2 : ℝ) ^ ((d : ℝ) / 2)) ^ 2 = 2 ^ d := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast]
  congr 1; push_cast; ring

theorem nu_sq_mul_le_norm_sq (b : Fin d → E) (hb : LinearIndependent ℝ b) (c : Fin d → ℝ)
    (j : Fin d) : nu b c j ^ 2 * ‖gs b j‖ ^ 2 ≤ ‖∑ l, c l • b l‖ ^ 2 := by
  rw [norm_sq_comb b hb c]
  exact single_le_sum (f := fun j => nu b c j ^ 2 * ‖gs b j‖ ^ 2)
    (fun k _ => by positivity) (mem_univ j)

theorem abs_inner_le_of_isRed (b : Fin d → E) (hr : IsRed b) (c : Fin d → ℤ) (i : Fin d) :
    |⟪b i, ∑ l, (c l : ℝ) • b l⟫_ℝ| ≤
      (d : ℝ) * (2 : ℝ) ^ ((d : ℝ) / 2) * ‖∑ l, (c l : ℝ) • b l‖ ^ 2 := by
  classical
  set x := ∑ l, (c l : ℝ) • b l with hx
  set s := (2 : ℝ) ^ ((d : ℝ) / 2) with hs
  have hs0 : 0 < s := by positivity
  by_cases hc : c = 0
  · simp [hx, hc]
  obtain ⟨t, ht, hmax⟩ := exists_max_image (univ.filter fun l => c l ≠ 0) id
    (by simpa [Finset.Nonempty, funext_iff] using hc)
  have ht0 : c t ≠ 0 := (mem_filter.1 ht).2
  have htop : ∀ l, t < l → (c l : ℝ) = 0 := by
    intro l hl
    by_contra h
    exact absurd (hmax l (mem_filter.2 ⟨mem_univ _, by exact_mod_cast h⟩)) (not_le.2 hl)
  have hgt : ‖gs b t‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    have h1 := nu_sq_mul_le_norm_sq b hr.1 (fun l => (c l : ℝ)) t
    rw [nu_top b hr.1 _ t htop] at h1
    have h2 : (1 : ℝ) ≤ (c t : ℝ) ^ 2 := by
      have : (1 : ℤ) ≤ c t ^ 2 := by
        have := sq_pos_of_ne_zero ht0
        omega
      exact_mod_cast this
    nlinarith [sq_nonneg ‖gs b t‖]
  have hterm : ∀ j, |⟪mu b i j • gs b j, x⟫_ℝ| ≤ s * ‖x‖ ^ 2 := by
    intro j
    have hmu : |mu b i j| ≤ 1 := by
      rcases lt_trichotomy j i with h | h | h
      · linarith [hr.2.1 i j h]
      · rw [h, mu_self b hr.1, abs_one]
      · rw [mu_of_lt b h, abs_zero]; exact zero_le_one
    rw [real_inner_smul_left, abs_mul]
    refine (mul_le_of_le_one_left (abs_nonneg _) hmu).trans ?_
    rcases le_or_gt j t with h | h
    · have h1 := gs_sq_le_pow b hr t j h
      have h2 : (2 : ℝ) ^ (t.val - j.val) ≤ 2 ^ d :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      have h3 : ‖gs b j‖ ≤ s * ‖x‖ := by
        refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
        rw [mul_pow, hs, rpow_half_sq]
        exact h1.trans (mul_le_mul h2 hgt (sq_nonneg _) (by positivity))
      calc _ ≤ ‖gs b j‖ * ‖x‖ := abs_real_inner_le_norm _ _
        _ ≤ s * ‖x‖ * ‖x‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
        _ = _ := by ring
    · rw [hx, inner_gs_comb b hr.1, nu_eq_zero_of b _ j fun l hl => htop l (h.trans_le hl)]
      rw [zero_mul, abs_zero]; positivity
  conv_lhs => rw [b_eq_sum b hr.1 i, sum_inner]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun j _ => hterm j).trans_eq ?_)
  simp [mul_assoc]

theorem abs_nu_le_of_isRed (b : Fin d → E) (hr : IsRed b) (c : Fin d → ℝ) {N : ℝ} (hN : 0 < N)
    (hmin : ∀ w : Fin d → ℤ, ‖∑ l, c l • b l‖ ^ 2 ≤ ‖∑ l, (c l - N * w l) • b l‖ ^ 2)
    (t : Fin d) : |nu b c t| ≤ (2 : ℝ) ^ ((d : ℝ) / 2 - 1) * N := by
  obtain ⟨w, hw0, hw⟩ := babai b hr.1 c hN (t.val + 1) t.isLt
  have h := hmin w
  rw [norm_sq_comb b hr.1, norm_sq_comb b hr.1,
    ← sum_filter_add_sum_filter_not univ (fun j : Fin d => j.val ≤ t.val),
    ← sum_filter_add_sum_filter_not univ (fun j : Fin d => j.val ≤ t.val)] at h
  have e : ∑ j ∈ univ.filter (fun j : Fin d => ¬ j.val ≤ t.val),
      nu b (fun l => c l - N * w l) j ^ 2 * ‖gs b j‖ ^ 2 =
      ∑ j ∈ univ.filter (fun j : Fin d => ¬ j.val ≤ t.val), nu b c j ^ 2 * ‖gs b j‖ ^ 2 := by
    refine sum_congr rfl fun j hj => ?_
    have hj' : ¬ j.val ≤ t.val := (mem_filter.1 hj).2
    rw [nu_sub, nu_eq_zero_of b (fun l => (w l : ℝ)) j fun l hl => by
      rw [hw0 l (by rw [Fin.le_def] at hl; omega), Int.cast_zero]]
    simp
  rw [e, add_le_add_iff_right] at h
  have h1 : nu b c t ^ 2 * ‖gs b t‖ ^ 2 ≤
      ∑ j ∈ univ.filter (fun j : Fin d => j.val ≤ t.val), nu b c j ^ 2 * ‖gs b j‖ ^ 2 :=
    single_le_sum (f := fun j => nu b c j ^ 2 * ‖gs b j‖ ^ 2)
      (fun k _ => by positivity) (mem_filter.2 ⟨mem_univ _, le_rfl⟩)
  have h2 : ∑ j ∈ univ.filter (fun j : Fin d => j.val ≤ t.val),
      nu b (fun l => c l - N * w l) j ^ 2 * ‖gs b j‖ ^ 2 ≤
      (N / 2) ^ 2 * ∑ j ∈ univ.filter (fun j : Fin d => j.val ≤ t.val), ‖gs b j‖ ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun j hj => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hw j (Nat.lt_succ_of_le (mem_filter.1 hj).2)) 2
  have h3 := sum_gs_le b hr.2.2 t.val t.isLt
  have h4 : (2 : ℝ) ^ (t.val + 1) - 1 ≤ 2 ^ d := by
    have : (2 : ℝ) ^ (t.val + 1) ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) t.isLt
    linarith
  have hg : 0 < ‖gs b t‖ ^ 2 := by have := gs_ne_zero b hr.1 t; positivity
  have h5 : nu b c t ^ 2 * ‖gs b t‖ ^ 2 ≤ ((N / 2) ^ 2 * 2 ^ d) * ‖gs b t‖ ^ 2 := by
    rw [mul_assoc]
    exact (h1.trans h).trans (h2.trans (mul_le_mul_of_nonneg_left
      (h3.trans (mul_le_mul_of_nonneg_right h4 hg.le)) (sq_nonneg _)))
  refine abs_le_of_sq_le_sq ((le_of_mul_le_mul_right h5 hg).trans_eq ?_) (by positivity)
  rw [Real.rpow_sub_one (by norm_num), mul_pow, div_pow, div_pow, rpow_half_sq]
  ring

theorem abs_coeff_le_of_isRed (b : Fin d → E) (hr : IsRed b) (c : Fin d → ℝ) {N : ℝ} (hN : 0 < N)
    (hmin : ∀ w : Fin d → ℤ, ‖∑ l, c l • b l‖ ^ 2 ≤ ‖∑ l, (c l - N * w l) • b l‖ ^ 2)
    (i : Fin d) : |c i| ≤ C1 d * N := by
  have h := coeff_bound b hr.1 hr.2.1 c (by positivity) (abs_nu_le_of_isRed b hr c hN hmin) i
  have hd : (1 : ℝ) ≤ d := by exact_mod_cast i.pos
  refine h.trans ?_
  rw [C1, mul_assoc, mul_assoc]
  exact le_mul_of_one_le_left (by positivity) hd

end Family

theorem exists_reduced_basis_matrix : ExistsBoundedBasis := by
  intro d A hA
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin d) (Fin d) ℝ, A = Bᴴ * B := by
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.posSemidef.nonneg
    exact ⟨B, hB⟩
  obtain ⟨e, hr⟩ :=
    exists_red_of (fB B) (fun e => (li_basis A B hA hB e).2) (hlow_of A B hA hB)
  refine ⟨e, fun i μ => ?_, fun N hN α hα i => ?_⟩
  · have h := abs_inner_le_of_isRed _ hr (fun l => e.repr μ l) i
    rw [← fB_expand B e μ] at h
    rwa [polar_eq A B hB, polar_eq A B hB, real_inner_self_eq_norm_sq]
  · refine abs_coeff_le_of_isRed _ hr (fun l => (e.repr α l : ℝ))
      (by exact_mod_cast hN) (fun w => ?_) i
    have h := hα (-e.equivFun.symm w)
    rw [Q_eq A B hB, Q_eq A B hB, fB_expand B e, fB_expand B e] at h
    have e1 : ∀ l, ((e.repr (α + N • -e.equivFun.symm w) l : ℤ) : ℝ) =
        (e.repr α l : ℝ) - N * w l := by
      intro l
      have : e.repr (e.equivFun.symm w) l = w l := congrFun (e.equivFun.apply_symm_apply w) l
      rw [map_add, map_smul, map_neg, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.neg_apply, this]
      push_cast [smul_eq_mul]; ring
    simp only [e1] at h
    linarith

section Lattice

variable {X : Type*} [AddCommGroup X] {d : ℕ}

theorem polar_equivFun (q : QuadraticMap ℤ X ℝ) (b : Basis (Fin d) ℤ X) (x y : X) :
    ReciprocityTheory.ReducedBases.polar (Matrix.of fun i j => QuadraticMap.polar q (b i) (b j))
      (b.equivFun x) (b.equivFun y) = QuadraticMap.polar q x y := by
  conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y, ← QuadraticMap.polarBilin_apply_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    QuadraticMap.polarBilin_apply_apply, ReciprocityTheory.ReducedBases.polar, toReal, dotProduct, mulVec, of_apply,
    mul_sum, Basis.equivFun_apply, zsmul_eq_mul]
  rw [sum_comm]
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

theorem quadratic_equivFun (q : QuadraticMap ℤ X ℝ) (b : Basis (Fin d) ℤ X) (x : X) :
    Q (Matrix.of fun i j => QuadraticMap.polar q (b i) (b j)) (b.equivFun x) = q x := by
  rw [Q, polar_equivFun, QuadraticMap.polar_self, nsmul_eq_mul]; push_cast; ring

theorem exists_reduced_basis_of_posDef_gram (q : QuadraticMap ℤ X ℝ) (b : Basis (Fin d) ℤ X)
    (hq : (Matrix.of fun i j => QuadraticMap.polar q (b i) (b j)).PosDef) :
    ∃ e : Basis (Fin d) ℤ X,
      (∀ (i : Fin d) (μ : X), |QuadraticMap.polar q (e i) μ| ≤
        (d : ℝ) * (2 : ℝ) ^ ((d : ℝ) / 2) * QuadraticMap.polar q μ μ) ∧
      ∀ N : ℤ, 1 ≤ N → ∀ α : X, (∀ w : X, q α ≤ q (α + N • w)) → ∀ i : Fin d,
        |(e.repr α i : ℝ)| ≤ (d : ℝ) * (3 / 2 : ℝ) ^ d * (2 : ℝ) ^ ((d : ℝ) / 2 - 1) * N := by
  obtain ⟨e, h1, h2⟩ := exists_reduced_basis_matrix d _ hq
  refine ⟨e.map b.equivFun.symm, fun i μ => ?_, fun N hN α hα i => ?_⟩
  · have h := h1 i (b.equivFun μ)
    rw [← polar_equivFun q b, ← polar_equivFun q b]
    simpa only [Basis.map_apply, LinearEquiv.apply_symm_apply] using h
  · refine h2 N hN (b.equivFun α) (fun w => ?_) i
    have h := hα (b.equivFun.symm w)
    rw [← quadratic_equivFun q b, ← quadratic_equivFun q b] at h
    simpa only [map_add, map_smul, LinearEquiv.apply_symm_apply] using h

theorem exists_reduced_basis_pairing_coord [Module.Free ℤ X] [Module.Finite ℤ X]
    (hd : finrank ℤ X = d) (q : QuadraticMap ℤ X ℝ) (hq : (realExt q).PosDef) :
    ∃ e : Basis (Fin d) ℤ X,
      (∀ (i : Fin d) (μ : X), |QuadraticMap.polar q (e i) μ| ≤
        (d : ℝ) * (2 : ℝ) ^ ((d : ℝ) / 2) * QuadraticMap.polar q μ μ) ∧
      ∀ N : ℤ, 1 ≤ N → ∀ α : X, (∀ w : X, q α ≤ q (α + N • w)) → ∀ i : Fin d,
        |(e.repr α i : ℝ)| ≤ (d : ℝ) * (3 / 2 : ℝ) ^ d * (2 : ℝ) ^ ((d : ℝ) / 2 - 1) * N :=
  exists_reduced_basis_of_posDef_gram q _
    (posDef_gram_of_posDef_realExt (finBasisOfFinrankEq ℤ X hd) hq)

theorem lt_add_smul_of_abs_polar_le (q : QuadraticMap ℤ X ℝ) {e μ : X} {c : ℝ} {N : ℤ}
    (hc : 0 ≤ c) (hN : 2 * c < N) (hμ : 0 < q μ)
    (h : |QuadraticMap.polar q e μ| ≤ c * QuadraticMap.polar q μ μ) :
    q e < q (e + N • μ) ∧ q (-e) < q (-e + N • μ) := by
  have hN0 : (0 : ℝ) < N := by linarith
  rw [QuadraticMap.polar_self, nsmul_eq_mul, abs_le] at h
  have h1 := mul_pos hN0 (mul_pos (sub_pos.2 hN) hμ)
  have h2 := mul_le_mul_of_nonneg_left h.1 hN0.le
  have h3 := mul_le_mul_of_nonneg_left h.2 hN0.le
  simp only [QuadraticMap.map_add q, QuadraticMap.polar_smul_right, QuadraticMap.polar_neg_left,
    QuadraticMap.map_smul, zsmul_eq_mul]
  push_cast at h2 h3 ⊢
  constructor <;> nlinarith

theorem pairing_const_mono {d g : ℕ} (h : d ≤ g) :
    (d : ℝ) * (2 : ℝ) ^ ((d : ℝ) / 2) ≤ (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) := by
  have : (d : ℝ) ≤ g := by exact_mod_cast h
  gcongr; norm_num

theorem coordinate_const_mono {d g : ℕ} (h : d ≤ g) :
    (d : ℝ) * (3 / 2 : ℝ) ^ d * (2 : ℝ) ^ ((d : ℝ) / 2 - 1) ≤
      (g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1) := by
  have : (d : ℝ) ≤ g := by exact_mod_cast h
  gcongr <;> norm_num

theorem exists_reduced_basis_unique_min_of_le [Module.Free ℤ X] [Module.Finite ℤ X]
    (hd : finrank ℤ X = d) {g : ℕ} (hg : d ≤ g) (q : QuadraticMap ℤ X ℝ)
    (hq : (realExt q).PosDef) :
    ∃ e : Basis (Fin d) ℤ X,
      (∀ (i : Fin d) (μ : X), |QuadraticMap.polar q (e i) μ| ≤
        (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) * QuadraticMap.polar q μ μ) ∧
      (∀ N : ℤ, 1 ≤ N → ∀ α : X, (∀ w : X, q α ≤ q (α + N • w)) → ∀ i : Fin d,
        |(e.repr α i : ℝ)| ≤ (g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1) * N) ∧
      ∀ N : ℤ, 2 * ((g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2)) < N → ∀ (i : Fin d) (w : X), w ≠ 0 →
        q (e i) < q (e i + N • w) ∧ q (-e i) < q (-e i + N • w) := by
  obtain ⟨e, h1, h2⟩ := exists_reduced_basis_pairing_coord hd q hq
  have hp := posDef_of_posDef_realExt hq
  have h1' : ∀ (i : Fin d) (μ : X), |QuadraticMap.polar q (e i) μ| ≤
      (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) * QuadraticMap.polar q μ μ := fun i μ => by
    refine (h1 i μ).trans (mul_le_mul_of_nonneg_right (pairing_const_mono hg) ?_)
    rw [QuadraticMap.polar_self]
    exact nsmul_nonneg (hp.nonneg μ) 2
  refine ⟨e, h1', fun N hN α hα i => (h2 N hN α hα i).trans ?_, fun N hN i w hw =>
    lt_add_smul_of_abs_polar_le q (by positivity) hN (hp w hw) (h1' i w)⟩
  exact mul_le_mul_of_nonneg_right (coordinate_const_mono hg) (by exact_mod_cast (by omega))

end Lattice

end GlobalTheory
