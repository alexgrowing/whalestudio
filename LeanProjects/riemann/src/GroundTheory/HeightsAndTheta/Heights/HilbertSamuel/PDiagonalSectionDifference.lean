import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDiagonalSectionDifference
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsDimZero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSerreGraded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultigradedHilbertPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEventualPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftDegreePolynomial
import GroundTheory.HeightsAndTheta.Heights.Intersections.AvoidRing
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.GradedSpanProducts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

noncomputable section

set_option linter.unusedSectionVars false

namespace DiagonalSectionDifference

section Pieces

variable {Ω : Type} [Field Ω] {q : ℕ} (w : Fin q → Ω)

abbrev pc (n : ℕ) : AddSubgroup Ω := gradedSpan w (fun _ : Fin 1 => 0) (fun _ => 1) n

theorem pc_mul {a b : ℕ} {x z : Ω} (hx : x ∈ pc w a) (hz : z ∈ pc w b) : x * z ∈ pc w (a + b) :=
  by apply _root_.UpperTheory.Reformulated.B.GradedSpanProducts.pc_mul <;> assumption

theorem pc_one : (1 : Ω) ∈ pc w 0 :=
  AddSubgroup.subset_closure ⟨0, 0, by simp, by simp⟩

theorem pc_gen (j : Fin q) : w j ∈ pc w 1 := by
  have h := gradedSpan_gen_mem w (fun _ : Fin 1 => 0) (fun _ => 1) 0 (Pi.single j 1)
  have e : ∏ i, w i ^ (Pi.single j 1 : Fin q → ℕ) i = w j := by
    rw [Finset.prod_eq_single j (fun b _ hb => by simp [hb]) (by simp)]; simp
  simpa [e] using h

theorem pc_pow {a : ℕ} {x : Ω} (hx : x ∈ pc w a) (e : ℕ) : x ^ e ∈ pc w (a * e) := by
  induction e with
  | zero => simpa using pc_one w
  | succ e ih => rw [pow_succ, Nat.mul_succ]; exact pc_mul w ih hx

theorem pc_natCast_mul (N : ℕ) {a : ℕ} {x : Ω} (hx : x ∈ pc w a) : (N : Ω) * x ∈ pc w a := by
  rw [← nsmul_eq_mul]; exact AddSubgroup.nsmul_mem _ hx N

theorem pc_intCast_mul (N : ℤ) {a : ℕ} {x : Ω} (hx : x ∈ pc w a) : (N : Ω) * x ∈ pc w a := by
  rw [← zsmul_eq_mul]; exact AddSubgroup.zsmul_mem _ hx N

end Pieces

section Charts

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

open Classical

def segre (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : Ω := ∏ k, y ⟨k, c k⟩

def sw (y : (Σ k, ι k) → Ω) : Fin (Fintype.card (∀ k, ι k)) → Ω :=
  fun j => segre y ((Fintype.equivFin (∀ k, ι k)).symm j)

theorem sw_equiv (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : sw y (Fintype.equivFin _ c) = segre y c := by
  simp [sw]

theorem segre_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : segre y c ∈ pc (sw y) 1 := by
  rw [← sw_equiv]; exact pc_gen _ _

theorem rt_mul_segre (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (p : Σ k, ι k) :
    SectionsDimZero.rt y c p * segre y c = segre y (Function.update c p.1 p.2) := by
  obtain ⟨k, i⟩ := p
  simp only [segre, SectionsDimZero.rt]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k),
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ k)]
  have hrest : ∏ x ∈ Finset.univ.erase k, y ⟨x, Function.update c k i x⟩ =
      ∏ x ∈ Finset.univ.erase k, y ⟨x, c x⟩ :=
    Finset.prod_congr rfl fun x hx => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [hrest, Function.update_self, ← mul_assoc, div_mul_cancel₀ _ (hc k)]

theorem chart_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω}
    (hx : x ∈ chartRingQ y c) :
    ∃ N : ℕ, 0 < N ∧ ∃ D : ℕ, ∀ e, D ≤ e → (N : Ω) * x * segre y c ^ e ∈ pc (sw y) e := by
  have hWp : ∀ e, segre y c ^ e ∈ pc (sw y) e := fun e => by simpa using pc_pow _ (segre_mem y c) e
  rw [chartRingQ] at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    refine ⟨1, one_pos, 1, fun e he => ?_⟩
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le he
    have h1 : SectionsDimZero.rt y c p * segre y c ∈ pc (sw y) 1 := by
      rw [rt_mul_segre y c hc]; exact segre_mem y _
    have h2 := pc_mul _ h1 (hWp e)
    rw [Nat.cast_one, one_mul, pow_add, pow_one, ← mul_assoc]
    exact h2
  | algebraMap r =>
    refine ⟨r.den, r.den_pos, 0, fun e _ => ?_⟩
    have hd : (r.den : Ω) ≠ 0 := Nat.cast_ne_zero.mpr r.den_nz
    have h : (r.den : Ω) * algebraMap ℚ Ω r = (r.num : Ω) := by
      rw [eq_ratCast, Rat.cast_def]; field_simp
    rw [h]; exact pc_intCast_mul _ _ (hWp e)
  | add x z _ _ hx hz =>
    obtain ⟨N1, hN1, D1, h1⟩ := hx
    obtain ⟨N2, hN2, D2, h2⟩ := hz
    refine ⟨N1 * N2, Nat.mul_pos hN1 hN2, max D1 D2, fun e he => ?_⟩
    have e1 := pc_natCast_mul _ N2 (h1 e (le_of_max_le_left he))
    have e2 := pc_natCast_mul _ N1 (h2 e (le_of_max_le_right he))
    convert add_mem e1 e2 using 1
    push_cast; ring
  | mul x z _ _ hx hz =>
    obtain ⟨N1, hN1, D1, h1⟩ := hx
    obtain ⟨N2, hN2, D2, h2⟩ := hz
    refine ⟨N1 * N2, Nat.mul_pos hN1 hN2, D1 + D2, fun e he => ?_⟩
    obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le he
    have h := pc_mul _ (h1 D1 le_rfl) (h2 (D2 + e') (Nat.le_add_right _ _))
    rw [show D1 + D2 + e' = D1 + (D2 + e') by ring]
    convert h using 1
    push_cast; ring

theorem pc_le_valueSpan (y : (Σ k, ι k) → Ω) (n : ℕ) {x : Ω} (hx : x ∈ pc (sw y) n) :
    x ∈ valueSpan y (fun _ => n) := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨l, μ, hμ, rfl⟩ := hx
    have h := GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_prod (R := ℤ) Finset.univ
      (fun j => (∏ k, (X ⟨k, ((Fintype.equivFin (∀ k, ι k)).symm j) k⟩ : MRing ι) ^ (fun _ : K => 1) k) ^ μ j)
      (fun j => μ j • (fun _ : K => 1))
      (fun j _ => GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_pow
        (GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_coordProd _ _) (μ j))
    have hdeg : (∑ j, μ j • (fun _ : K => (1 : ℕ))) = fun _ => n := by
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_one] at hμ ⊢
      simpa using hμ
    rw [hdeg] at h
    refine Submodule.subset_span ⟨_, h, ?_⟩
    simp [sw, segre, map_prod, map_pow]
  | zero => exact zero_mem _
  | add _ _ _ _ h h' => exact add_mem h h'
  | neg _ _ h => exact neg_mem h

theorem prod_neg_mul (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (n D : ℕ) (s : Ω) :
    s * (∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * ((n : ℤ) • (1 : K → ℤ)) k))) * segre y c ^ (n + D) =
      s * segre y c ^ D := by
  have hW : segre y c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  have hprod : (∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * ((n : ℤ) • (1 : K → ℤ)) k))) =
      (segre y c ^ n)⁻¹ := by
    rw [segre, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp [zpow_neg]
  rw [hprod, pow_add]
  field_simp

theorem exists_chartLatQ_le (y : (Σ k, ι k) → Ω) (hrel : ∃ c : ∀ k, ι k, ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → chartLatQ y ((n : ℤ) • (1 : K → ℤ)) 1 ≤ valueSpan y (fun _ => n) := by
  obtain ⟨c0, hc0⟩ := hrel
  have hw : ∃ j, sw y j ≠ 0 :=
    ⟨Fintype.equivFin _ c0, by rw [sw_equiv]; exact Finset.prod_ne_zero_iff.2 fun k _ => hc0 k⟩
  obtain ⟨n₀, hn₀⟩ := SerreGraded.proof Ω _ 1 (sw y) (fun _ => 0) (fun _ => 1) hw
  refine ⟨n₀, fun n hn s hs => ?_⟩
  have hloc : ∀ c : ∀ k, ι k, ∃ N : ℕ, 0 < N ∧ ∃ D : ℕ,
      (∀ k, y ⟨k, c k⟩ ≠ 0) → (N : Ω) * s * segre y c ^ D ∈ pc (sw y) (n + D) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨N, hN, D, hD⟩ := chart_mem y c hc (hs c hc)
      refine ⟨N, hN, D, fun _ => ?_⟩
      have h := hD (n + D) (Nat.le_add_left _ _)
      rw [mul_assoc, prod_neg_mul y c hc n D s] at h
      rwa [mul_assoc]
    · exact ⟨1, one_pos, 0, fun h => absurd h hc⟩
  choose N hN D hD using hloc
  have hM : 0 < ∏ c, N c := Finset.prod_pos fun c _ => hN c
  have hmem : ((∏ c, N c : ℕ) : Ω) * s ∈ pc (sw y) n := by
    refine hn₀ n hn _ fun j hj => ?_
    have hjc : sw y j = segre y ((Fintype.equivFin (∀ k, ι k)).symm j) := rfl
    have hc : ∀ k, y ⟨k, ((Fintype.equivFin (∀ k, ι k)).symm j) k⟩ ≠ 0 := fun k h0 =>
      hj (by rw [hjc, segre]; exact Finset.prod_eq_zero (Finset.mem_univ k) h0)
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ ((Fintype.equivFin (∀ k, ι k)).symm j))
    refine ⟨D ((Fintype.equivFin (∀ k, ι k)).symm j), ?_⟩
    have h := pc_natCast_mul _ m (hD _ hc)
    rw [hjc, hm]
    convert h using 1
    push_cast; ring
  have hV := pc_le_valueSpan y n hmem
  have hM0 : ((∏ c, N c : ℕ) : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have e : s = ((∏ c, N c : ℕ) : ℚ)⁻¹ • (((∏ c, N c : ℕ) : Ω) * s) := by
    rw [Algebra.smul_def, ← mul_assoc, map_inv₀, map_natCast, inv_mul_cancel₀ hM0, one_mul]
  rw [e]
  exact Submodule.smul_mem _ _ hV

theorem valueSpan_le_chartLatQ (y : (Σ k, ι k) → Ω) (n : ℕ) :
    valueSpan y (fun _ => n) ≤ chartLatQ y ((n : ℤ) • (1 : K → ℤ)) 1 := by
  intro s hs c hc
  obtain ⟨t, ht, rfl⟩ := Submodule.mem_map.mp (SectionsDimZero.valueSpan_le y c hc _ hs)
  have h1 : (∏ k, y ⟨k, c k⟩ ^ (fun _ : K => n) k) *
      ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * ((n : ℤ) • (1 : K → ℤ)) k)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => by simp [zpow_neg, hc k]
  rw [LinearMap.mulRight_apply, mul_assoc, h1, mul_one]
  exact ht

end Charts

theorem pow_sub_pow_le (t : ℚ) (ht : 1 ≤ t) (e : ℕ) : t ^ (e + 1) - (t - 1) ^ (e + 1) ≤ (e + 1) * t ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    have h0 : (t - 1) ^ (e + 1) ≤ t ^ (e + 1) := pow_le_pow_left₀ (by linarith) (by linarith) _
    have key : t ^ (e + 1 + 1) - (t - 1) ^ (e + 1 + 1) =
        t * (t ^ (e + 1) - (t - 1) ^ (e + 1)) + (t - 1) ^ (e + 1) := by ring
    rw [key]
    calc t * (t ^ (e + 1) - (t - 1) ^ (e + 1)) + (t - 1) ^ (e + 1)
        ≤ t * ((e + 1) * t ^ e) + t ^ (e + 1) := by gcongr
      _ = ((e + 1 : ℕ) + 1) * t ^ (e + 1) := by push_cast; ring

theorem poly_diff_bound {σ : Type} (p : MvPolynomial σ ℚ) (D : ℕ) (hp : p.totalDegree ≤ D) :
    ∃ C : ℚ, ∀ t : ℚ, 1 ≤ t → eval (fun _ => t) p - eval (fun _ => t - 1) p ≤ C * t ^ (D - 1) := by
  have hev : ∀ t : ℚ, eval (fun _ => t) p = ∑ m ∈ p.support, coeff m p * t ^ (m.sum fun _ e => e) := by
    intro t
    rw [MvPolynomial.eval_eq]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  refine ⟨∑ m ∈ p.support, |coeff m p| * (m.sum fun _ e => e : ℕ), fun t ht => ?_⟩
  rw [hev, hev, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine Finset.sum_le_sum fun m hm => ?_
  have he : (m.sum fun _ e => e) ≤ D := (le_totalDegree hm).trans hp
  set e := m.sum fun _ e => e
  have h0 : (t - 1) ^ e ≤ t ^ e := pow_le_pow_left₀ (by linarith) (by linarith) _
  have h2 : t ^ e - (t - 1) ^ e ≤ (e : ℚ) * t ^ (D - 1) := by
    rcases Nat.eq_zero_or_pos e with h | h
    · simp [h]
    · obtain ⟨e', he'⟩ := Nat.exists_eq_add_of_lt h
      have h3 := pow_sub_pow_le t ht e'
      have h4 : t ^ e' ≤ t ^ (D - 1) := pow_le_pow_right₀ ht (by omega)
      rw [he', zero_add]
      calc t ^ (e' + 1) - (t - 1) ^ (e' + 1) ≤ (e' + 1) * t ^ e' := h3
        _ ≤ (e' + 1) * t ^ (D - 1) := by gcongr
        _ = ((e' + 1 : ℕ) : ℚ) * t ^ (D - 1) := by push_cast; ring
  calc coeff m p * t ^ e - coeff m p * (t - 1) ^ e = coeff m p * (t ^ e - (t - 1) ^ e) := by ring
    _ ≤ |coeff m p| * (t ^ e - (t - 1) ^ e) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    _ ≤ |coeff m p| * ((e : ℚ) * t ^ (D - 1)) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = |coeff m p| * (e : ℚ) * t ^ (D - 1) := by ring

end DiagonalSectionDifference

theorem DiagonalSectionDifference.proof : DiagonalSectionDifference.Statement := by
  classical
  intro K _ ι _ Ω _ _ y D _ hV
  obtain ⟨hQ, hdim⟩ := ShiftDegreePolynomial.genericFibre hV
  obtain ⟨p, a₀, hpdeg, hp⟩ :=
    MultigradedHilbertPolynomial.proof EventualPolynomial.proof ℚ K ι _ D hQ hdim
  have hrel : ∃ c : ∀ k, ι k, ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    choose c hcX using hV.2.1.2.2
    exact ⟨c, fun k h0 => hcX k (CoordCurveDegree.X_mem_of_eq_zero h0)⟩
  obtain ⟨n₀, hn₀⟩ := DiagonalSectionDifference.exists_chartLatQ_le y hrel
  have hval : ∀ n, max n₀ a₀ ≤ n →
      (Module.finrank ℚ (chartLatQ y ((n : ℤ) • (1 : K → ℤ)) 1) : ℚ) = eval (fun _ => (n : ℚ)) p := by
    intro n hn
    rw [le_antisymm (hn₀ n (le_of_max_le_left hn)) (DiagonalSectionDifference.valueSpan_le_chartLatQ y n)]
    have h1 := HilbFnValueSpan.proof K ι Ω y (fun _ => n)
    have h2 := hp (fun _ => n) (fun _ => le_of_max_le_right hn)
    rw [h1] at h2
    exact_mod_cast h2
  obtain ⟨C, hC⟩ := DiagonalSectionDifference.poly_diff_bound p D hpdeg
  refine ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop (max n₀ a₀ + 1)] with j hj
  have hj1 : (j : ℤ) • (1 : K → ℤ) - 1 = ((j - 1 : ℕ) : ℤ) • (1 : K → ℤ) := by
    funext k
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    omega
  rw [hj1]
  have e1 := hval j (by omega)
  have e2 := hval (j - 1) (by omega)
  have hc := hC (j : ℚ) (by exact_mod_cast (show 1 ≤ j by omega))
  have hcast : ((j - 1 : ℕ) : ℚ) = (j : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hcast] at e2
  have key : (Module.finrank ℚ (chartLatQ y ((j : ℤ) • (1 : K → ℤ)) 1) : ℚ) ≤
      Module.finrank ℚ (chartLatQ y (((j - 1 : ℕ) : ℤ) • (1 : K → ℤ)) 1) + C * (j : ℚ) ^ (D - 1) := by
    rw [e1, e2]; linarith
  exact_mod_cast key

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
