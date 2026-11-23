import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MemEurOfTeichmullerSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicPowerSeriesAlgHomActionLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowSubOneOfNotDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAddValuationFinExt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cyc PowerSeries

namespace GlobalTheory.Cyc.InvBasis

section Formal

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
  (γ : K⟦X⟧ →ₐ[K] K⟦X⟧) (G : Matrix ι ι K⟦X⟧)

theorem coeff_mul_apply (hγ : constantCoeff (γ X) = 0) (g c : K⟦X⟧) (n : ℕ) :
    coeff n (g * γ c) = ∑ d ∈ Finset.range (n + 1), coeff n (g * γ X ^ d) * coeff d c := by
  obtain ⟨a, ha⟩ := X_dvd_iff.2 hγ
  have hc : c = X ^ (n + 1) * (PowerSeries.mk fun i ↦ coeff (i + (n + 1)) c) +
      ∑ d ∈ Finset.range (n + 1), coeff d c • X ^ d := by
    ext m
    rw [map_add, coeff_X_pow_mul', map_sum]
    simp only [coeff_smul, coeff_X_pow, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_range, coeff_mk]
    split_ifs with h1 h2 h2
    · omega
    · rw [add_zero, Nat.sub_add_cancel h1]
    · rw [zero_add]
    · omega
  conv_lhs => rw [hc]
  rw [map_add, mul_add, map_add, map_mul γ, map_pow γ, map_sum γ, Finset.mul_sum, map_sum]
  have h0 : ∀ b : K⟦X⟧, coeff n (g * (γ X ^ (n + 1) * b)) = 0 := fun b => by
    rw [ha, mul_pow, show g * (X ^ (n + 1) * a ^ (n + 1) * b) = X ^ (n + 1) * (g * a ^ (n + 1) * b) by ring,
      coeff_X_pow_mul', if_neg (by omega)]
  rw [h0, zero_add]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_smul, map_pow, mul_smul_comm, coeff_smul, smul_eq_mul, mul_comm]

theorem coeff_mul_pow_self (hγ : constantCoeff (γ X) = 0) (g : K⟦X⟧) (n : ℕ) :
    coeff n (g * γ X ^ n) = constantCoeff g * coeff 1 (γ X) ^ n := by
  obtain ⟨a, ha⟩ := X_dvd_iff.2 hγ
  rw [ha, mul_pow, show g * (X ^ n * a ^ n) = X ^ n * (g * a ^ n) by ring, coeff_X_pow_mul',
    if_pos le_rfl, Nat.sub_self, coeff_succ_X_mul]
  simp

theorem coeff_op (hγ : constantCoeff (γ X) = 0) (hG : G.map constantCoeff = 1) (c : ι → K⟦X⟧) (i : ι)
    (n : ℕ) : coeff n (G.mulVec (fun j => γ (c j)) i) = coeff 1 (γ X) ^ n * coeff n (c i) +
      ∑ j, ∑ d ∈ Finset.range n, coeff n (G i j * γ X ^ d) * coeff d (c j) := by
  simp only [Matrix.mulVec, dotProduct, map_sum, coeff_mul_apply γ hγ, Finset.sum_range_succ,
    Finset.sum_add_distrib, coeff_mul_pow_self γ hγ]
  rw [add_comm]
  congr 1
  have : ∀ j, constantCoeff (G i j) = (1 : Matrix ι ι K) i j := fun j => by rw [← hG]; rfl
  simp [this, Matrix.one_apply]

theorem exists_rec {α : Type} (F : (n : ℕ) → (Fin n → α) → α) :
    ∃ f : ℕ → α, ∀ n, f n = F n fun k => f k := by
  refine ⟨fun n => Nat.strongRec (motive := fun _ => α) (fun n ih => F n fun k => ih k k.2) n, fun n => ?_⟩
  exact Nat.strongRec_eq _ n

theorem exists_sol (hγ : constantCoeff (γ X) = 0) (hG : G.map constantCoeff = 1)
    (hu : ∀ n, n ≠ 0 → coeff 1 (γ X) ^ n ≠ 1) (c₀ : ι → K) :
    ∃ c : ι → K⟦X⟧, (∀ i, constantCoeff (c i) = c₀ i) ∧ G.mulVec (fun j => γ (c j)) = c := by
  obtain ⟨f, hf⟩ := exists_rec (α := ι → K) fun n p => if n = 0 then c₀ else fun i =>
    (1 - coeff 1 (γ X) ^ n)⁻¹ * ∑ j, ∑ d : Fin n, coeff n (G i j * γ X ^ (d : ℕ)) * p d j
  refine ⟨fun i => PowerSeries.mk fun n => f n i, fun i => ?_, ?_⟩
  · rw [constantCoeff_mk, hf, if_pos rfl]
  · ext i n
    rw [coeff_op γ G hγ hG]
    simp only [coeff_mk]
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have h := congrFun (hf n) i
      rw [if_neg hn] at h
      have h1 : 1 - coeff 1 (γ X) ^ n ≠ 0 := sub_ne_zero.2 (hu n hn).symm
      simp only [Finset.sum_range]
      rw [eq_inv_mul_iff_mul_eq₀ h1] at h
      rw [← h]; ring

theorem sol_eq_zero (hγ : constantCoeff (γ X) = 0) (hG : G.map constantCoeff = 1)
    (hu : ∀ n, n ≠ 0 → coeff 1 (γ X) ^ n ≠ 1) (c : ι → K⟦X⟧) (h0 : ∀ i, constantCoeff (c i) = 0)
    (hc : G.mulVec (fun j => γ (c j)) = c) : c = 0 := by
  have : ∀ n i, coeff n (c i) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i
      rcases eq_or_ne n 0 with rfl | hn
      · simpa using h0 i
      · have h := coeff_op γ G hγ hG c i n
        rw [hc, Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun d hd => by
          rw [ih d (Finset.mem_range.1 hd), mul_zero], add_zero] at h
        by_contra hne
        exact hu n hn (mul_right_cancel₀ hne (h.symm.trans (one_mul _).symm))
  ext i n
  simp [this]

omit [DecidableEq ι] in

theorem apply_C (x : K) : γ (C x) = C x := γ.commutes x

end Formal

section Bound

variable {K : Type} [NormedField K] [IsUltrametricDist K] {ι : Type} [Fintype ι] [DecidableEq ι]
  (γ : K⟦X⟧ →ₐ[K] K⟦X⟧) (G : Matrix ι ι K⟦X⟧)

theorem norm_sol_le (hγ : constantCoeff (γ X) = 0) (hG : G.map constantCoeff = 1)
    (hint : ∀ i j n d, ‖coeff n (G i j * γ X ^ d)‖ ≤ 1) (B : ℕ → ℝ) (hB0 : 1 ≤ B 0) (hB : Monotone B)
    (hu : ∀ n, coeff 1 (γ X) ^ (n + 1) ≠ 1)
    (hBu : ∀ n, B n ≤ ‖1 - coeff 1 (γ X) ^ (n + 1)‖ * B (n + 1))
    (c : ι → K⟦X⟧) (h0 : ∀ i, ‖constantCoeff (c i)‖ ≤ 1)
    (hc : G.mulVec (fun j => γ (c j)) = c) (n : ℕ) : ∀ i, ‖coeff n (c i)‖ ≤ B n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro i
    rcases n with _ | n
    · simpa using (h0 i).trans hB0
    · have h := coeff_op γ G hγ hG c i (n + 1)
      rw [hc] at h
      have hBn : 0 ≤ B n := zero_le_one.trans (hB0.trans (hB (Nat.zero_le n)))
      have h2 : ‖(1 - coeff 1 (γ X) ^ (n + 1)) * coeff (n + 1) (c i)‖ ≤ B n := by
        rw [sub_mul, one_mul, sub_eq_of_eq_add' h]
        refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hBn fun j _ =>
          IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hBn fun d hd => ?_
        have hd' := Finset.mem_range.1 hd
        rw [norm_mul]
        calc _ ≤ 1 * B d := mul_le_mul (hint _ _ _ _) (ih d hd' j) (norm_nonneg _) zero_le_one
          _ ≤ B n := by rw [one_mul]; exact hB (by omega)
      rw [norm_mul] at h2
      have h1 : 0 < ‖1 - coeff 1 (γ X) ^ (n + 1)‖ := norm_pos_iff.2 (sub_ne_zero.2 (hu n).symm)
      exact le_of_mul_le_mul_left (h2.trans (hBu n)) h1

end Bound

theorem isUnit_det {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R⟦X⟧)
    (hA : A.map constantCoeff = 1) : IsUnit A.det := by
  rw [isUnit_iff_constantCoeff, RingHom.map_det, RingHom.mapMatrix_apply, hA, Matrix.det_one]
  exact isUnit_one

theorem inv_const {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι R⟦X⟧)
    (hA : A.map constantCoeff = 1) : A⁻¹.map constantCoeff = 1 := by
  have := congrArg (fun M : Matrix ι ι R⟦X⟧ => M.map constantCoeff) (A.mul_nonsing_inv (isUnit_det A hA))
  simp only [Matrix.map_mul, hA, one_mul] at this
  rw [this, Matrix.map_one _ (map_zero _) (map_one _)]

theorem exists_basis {K O : Type} [NormedField K] [IsUltrametricDist K] [CommRing O] {ι : Type} [Fintype ι]
    [DecidableEq ι] (γ : K⟦X⟧ →ₐ[K] K⟦X⟧) (φ : O →+* K) (hφ : ∀ x, ‖φ x‖ ≤ 1) (a : O⟦X⟧)
    (ha : γ X = PowerSeries.map φ a) (hγ : constantCoeff (γ X) = 0) (B : ℕ → ℝ) (hB0 : 1 ≤ B 0)
    (hB : Monotone B) (hu : ∀ n, n ≠ 0 → coeff 1 (γ X) ^ n ≠ 1)
    (hBu : ∀ n, B n ≤ ‖1 - coeff 1 (γ X) ^ (n + 1)‖ * B (n + 1))
    (G : Matrix ι ι O⟦X⟧) (hG : G.map constantCoeff = 1) :
    ∃ U V : Matrix ι ι K⟦X⟧, U * V = 1 ∧ U.map constantCoeff = 1 ∧
      G.map (PowerSeries.map φ) * U.map γ = U ∧
      (∀ c : ι → K⟦X⟧, (G.map (PowerSeries.map φ)).mulVec (fun i => γ (c i)) = c →
        c = U.mulVec fun i => C (constantCoeff (c i))) ∧
      ∀ i j n, ‖coeff n (U i j)‖ ≤ B n ∧ ‖coeff n (V i j)‖ ≤ B n := by
  have hmap : ∀ H : Matrix ι ι O⟦X⟧, H.map constantCoeff = 1 →
      (H.map (PowerSeries.map φ)).map constantCoeff = 1 := fun H hH => by
    ext i j
    have : constantCoeff (H i j) = (1 : Matrix ι ι O) i j := by rw [← hH]; rfl
    rw [Matrix.map_apply, Matrix.map_apply, ← coeff_zero_eq_constantCoeff_apply, coeff_map,
      coeff_zero_eq_constantCoeff_apply, this, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hone : ∀ i j, ‖(1 : Matrix ι ι K) i j‖ ≤ 1 := fun i j => by
    rw [Matrix.one_apply]; split_ifs <;> simp
  have hbd : ∀ H : Matrix ι ι O⟦X⟧, H.map constantCoeff = 1 → ∀ c : ι → K⟦X⟧,
      (∀ i, ‖constantCoeff (c i)‖ ≤ 1) → (H.map (PowerSeries.map φ)).mulVec (fun j => γ (c j)) = c →
      ∀ n i, ‖coeff n (c i)‖ ≤ B n := fun H hH c h0 hc =>
    norm_sol_le γ _ hγ (hmap H hH) (fun i j n d => by
      rw [ha, Matrix.map_apply, ← map_pow, ← map_mul, coeff_map]; exact hφ _) B hB0 hB
      (fun n => hu _ n.succ_ne_zero) hBu c h0 hc
  choose c hc0 hc using fun k => exists_sol γ _ hγ (hmap G hG) hu fun i => (1 : Matrix ι ι K) i k
  set U : Matrix ι ι K⟦X⟧ := Matrix.of fun i k => c k i with hU
  have hU0 : U.map constantCoeff = 1 := by ext i k; exact hc0 k i
  have hGU : G.map (PowerSeries.map φ) * U.map γ = U := by
    ext1 i k; exact congrFun (hc k) i
  have hUV := U.mul_nonsing_inv (isUnit_det U hU0)
  have hVU := U.nonsing_inv_mul (isUnit_det U hU0)
  refine ⟨U, U⁻¹, hUV, hU0, hGU, fun b hb => ?_, fun i j n => ⟨?_, ?_⟩⟩
  · rw [← sub_eq_zero]
    have hγv : (fun j => γ (U.mulVec (fun i => C (constantCoeff (b i))) j)) =
        (U.map γ).mulVec fun i => C (constantCoeff (b i)) := by
      funext j
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, apply_C, Matrix.map_apply]
    refine sol_eq_zero γ _ hγ (hmap G hG) hu _ (fun i => ?_) ?_
    · have : ∀ j, constantCoeff (U i j) = (1 : Matrix ι ι K) i j := fun j => by rw [← hU0]; rfl
      simp [Matrix.mulVec, dotProduct, this, Matrix.one_apply]
    · have : (fun j => γ ((b - U.mulVec fun i => C (constantCoeff (b i))) j)) =
          (fun j => γ (b j)) - (U.map γ).mulVec fun i => C (constantCoeff (b i)) := by
        rw [← hγv]; funext j; simp only [Pi.sub_apply, map_sub]
      rw [this, Matrix.mulVec_sub, hb, Matrix.mulVec_mulVec, hGU]
  · exact hbd G hG (c j) (fun i => by rw [hc0]; exact hone _ _) (hc j) n i
  · have hHG : (G⁻¹).map (PowerSeries.map φ) * G.map (PowerSeries.map φ) = 1 := by
      rw [← Matrix.map_mul, G.nonsing_inv_mul (isUnit_det G hG), Matrix.map_one _ (map_zero _) (map_one _)]
    have h1 : U⁻¹.map γ * U.map γ = 1 := by
      rw [← Matrix.map_mul, hVU, Matrix.map_one _ (map_zero _) (map_one _)]
    have h2 : U.map γ = (G⁻¹).map (PowerSeries.map φ) * U := by
      conv_rhs => rw [← hGU, ← mul_assoc, hHG, one_mul]
    have h3 : U⁻¹.map γ * (G⁻¹).map (PowerSeries.map φ) = U⁻¹ := by
      rw [h2, ← mul_assoc] at h1
      rw [← mul_one (_ * _), ← hUV, ← mul_assoc, h1, one_mul]
    refine hbd (G⁻¹).transpose (by rw [Matrix.transpose_map, inv_const G hG, Matrix.transpose_one]) (U⁻¹ i)
      (fun k => ?_) ?_ n j
    · have : constantCoeff (U⁻¹ i k) = (1 : Matrix ι ι K) i k := by rw [← inv_const U hU0]; rfl
      rw [this]; exact hone _ _
    · rw [Matrix.transpose_map, Matrix.mulVec_transpose]
      funext k
      exact congrFun (congrFun h3 i) k

theorem bound_le (l : ℕ) [hl : Fact l.Prime] (s n : ℕ) :
    (l : ℝ) ^ (n * s) * ‖(n.factorial : ℤ_[l])‖⁻¹ ≤ ((l : ℝ) ^ ((s : ℝ) + 1 / ((l : ℝ) - 1))) ^ n := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have h0 : (n.factorial : ℚ_[l]) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hn : ‖(n.factorial : ℤ_[l])‖ = (l : ℝ) ^ (-(padicValNat l n.factorial : ℤ)) := by
    rw [PadicInt.norm_def, PadicInt.coe_natCast, Padic.norm_eq_zpow_neg_valuation h0,
      Padic.valuation_natCast]
  have hv : ((l : ℝ) - 1) * (padicValNat l n.factorial : ℝ) ≤ n := by
    have h := sub_one_mul_padicValNat_factorial (p := l) n
    have h' : (l - 1) * padicValNat l n.factorial ≤ n := h ▸ Nat.sub_le _ _
    have h'' : (((l - 1) * padicValNat l n.factorial : ℕ) : ℝ) ≤ n := by exact_mod_cast h'
    rwa [Nat.cast_mul, Nat.cast_sub hl.out.one_lt.le, Nat.cast_one] at h''
  rw [hn, zpow_neg, inv_inv, zpow_natCast, ← pow_add, ← Real.rpow_natCast, ← Real.rpow_natCast,
    ← Real.rpow_mul (by positivity)]
  refine Real.rpow_le_rpow_of_exponent_le h1.le ?_
  have : (padicValNat l n.factorial : ℝ) ≤ 1 / ((l : ℝ) - 1) * n := by
    rw [one_div, inv_mul_eq_div, le_div_iff₀ (by linarith)]; linarith
  push_cast
  nlinarith

theorem tendsto_of_le (x : ℕ → ℝ) (h0 : ∀ n, 0 ≤ x n) (b : ℝ) (hb : 0 < b) (hx : ∀ n, x n ≤ b ^ n) (r : ℝ)
    (hr : 0 < r) (hrb : r < b⁻¹) : Filter.Tendsto (fun k : ℕ => x k * r ^ k) Filter.atTop (nhds 0) := by
  refine squeeze_zero (fun k => mul_nonneg (h0 k) (by positivity)) (fun k => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (r := b * r) (by positivity) ?_)
  · rw [mul_pow]; exact mul_le_mul_of_nonneg_right (hx k) (by positivity)
  · rwa [← lt_inv_mul_iff₀ hb, mul_one]

theorem norm_algebraMap (l : ℕ) [Fact l.Prime] (LL : FinExt l) (x : ℤ_[l]) :
    ‖algebraMap ℤ_[l] ↥LL.1 x‖ = ‖x‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]
  exact PadicAlgCl.norm_extends l (x : ℚ_[l])

end GlobalTheory.Cyc.InvBasis

namespace GlobalTheory.Cyc

open InvBasis

theorem exists_invariant_basis : ∀ (l : ℕ) [Fact l.Prime], ∀ (LL : FinExt l) (s r : ℕ) (u : ℤ_[l]ˣ), 1 ≤ s → (l = 2 → 2 ≤ s) → ‖(u : ℤ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) → ∀ G : Matrix (Fin r) (Fin r) (PowerSeries ↥(OL LL)), G.map PowerSeries.constantCoeff = 1 → ∃ U V : Matrix (Fin r) (Fin r) (PowerSeries ↥LL.1), U * V = 1 ∧ U.map PowerSeries.constantCoeff = 1 ∧ G.map (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1)) * U.map (act l ↥LL.1 u) = U ∧ (∀ c : Fin r → PowerSeries ↥LL.1, (G.map (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1))).mulVec (fun i => act l ↥LL.1 u (c i)) = c → c = U.mulVec fun i => PowerSeries.C (PowerSeries.constantCoeff (c i))) ∧ ∀ i j, (∀ r : ℝ, 0 < r → r < (l : ℝ) ^ (-((s : ℝ) + 1 / ((l : ℝ) - 1))) → Filter.Tendsto (fun k : ℕ => ‖((PowerSeries.coeff k (U i j) : ↥LL.1) : Om l)‖ * r ^ k) Filter.atTop (nhds 0)) ∧ (∀ r : ℝ, 0 < r → r < (l : ℝ) ^ (-((s : ℝ) + 1 / ((l : ℝ) - 1))) → Filter.Tendsto (fun k : ℕ => ‖((PowerSeries.coeff k (V i j) : ↥LL.1) : Om l)‖ * r ^ k) Filter.atTop (nhds 0)) := by
  intro l hl LL s r u hs h2 hu G hG
  have h1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hnorm : ∀ n : ℕ, n ≠ 0 → ‖1 - coeff 1 (act l ↥LL.1 u X) ^ n‖ =
      (l : ℝ) ^ (-(s : ℤ)) * ‖(n : ℤ_[l])‖ := fun n hn => by
    have h := norm_unit_zpow_sub_one l s u hs h2 hu n (by exact_mod_cast hn)
    rw [zpow_natCast, Units.val_pow_eq_pow_val, Int.cast_natCast] at h
    rw [act_X, coeff_one_cyc, ← h, norm_sub_rev, ← norm_algebraMap l LL, map_sub, map_pow, map_one]
  have hpos : ∀ n : ℕ, n ≠ 0 → 0 < ‖(n : ℤ_[l])‖ := fun n hn => norm_pos_iff.2 (by exact_mod_cast hn)
  have hstep : ∀ n : ℕ, (l : ℝ) ^ (n * s) * ‖(n.factorial : ℤ_[l])‖⁻¹ =
      (l : ℝ) ^ (-(s : ℤ)) * ‖((n + 1 : ℕ) : ℤ_[l])‖ *
        ((l : ℝ) ^ ((n + 1) * s) * ‖((n + 1).factorial : ℤ_[l])‖⁻¹) := fun n => by
    have := hpos (n + 1) n.succ_ne_zero
    have := hpos _ n.factorial_ne_zero
    rw [Nat.factorial_succ, Nat.cast_mul, norm_mul, zpow_neg, zpow_natCast]
    field_simp
    ring
  obtain ⟨U, V, hUV, hU0, hGU, huniq, hbd⟩ := exists_basis (act l ↥LL.1 u)
    (algebraMap ↥(OL LL) ↥LL.1) (fun x => (GlobalTheory.Per.Val.mem_OL_iff LL x.1).1 x.2) (cyc l ↥(OL LL) u)
    (by
      rw [act_X, cyc, cyc, map_sub, map_one]
      congr 1)
    (by rw [act_X, cyc_const])
    (fun n => (l : ℝ) ^ (n * s) * ‖(n.factorial : ℤ_[l])‖⁻¹) (by simp)
    (monotone_nat_of_le_succ fun n => by
      have hf := hpos _ (n + 1).factorial_ne_zero
      refine (hstep n).le.trans (mul_le_of_le_one_left (by positivity) ?_)
      exact mul_le_one₀ (zpow_le_one_of_nonpos₀ h1.le (by omega)) (norm_nonneg _) (PadicInt.norm_le_one _))
    (fun n hn h => by
      have h3 := hnorm n hn
      have := hpos n hn
      rw [h, sub_self, norm_zero] at h3
      exact absurd h3 (by positivity))
    (fun n => by rw [hnorm _ n.succ_ne_zero]; exact (hstep n).le) G hG
  refine ⟨U, V, hUV, hU0, hGU, huniq, fun i j => ⟨fun ρ h0 hρ => ?_, fun ρ h0 hρ => ?_⟩⟩
  · rw [Real.rpow_neg (by positivity)] at hρ
    exact tendsto_of_le _ (fun _ => norm_nonneg _) _ (by positivity)
      (fun n => (hbd i j n).1.trans (bound_le l s n)) ρ h0 hρ
  · rw [Real.rpow_neg (by positivity)] at hρ
    exact tendsto_of_le _ (fun _ => norm_nonneg _) _ (by positivity)
      (fun n => (hbd i j n).2.trans (bound_le l s n)) ρ h0 hρ

end GlobalTheory.Cyc
