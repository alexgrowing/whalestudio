import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.LeftInv
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB.CG.HeightGrowth

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exp_posLog {x : ℝ} (hx : 0 ≤ x) : Real.exp (Real.posLog x) = max 1 x := by
  rcases le_or_gt x 1 with h | h
  · have : Real.posLog x = 0 := by
      rw [Real.posLog_def]; simp only [Pi.sup_apply, Pi.zero_apply]
      exact max_eq_left (Real.log_nonpos hx h)
    rw [this, Real.exp_zero, max_eq_left h]
  · have : Real.posLog x = Real.log x := by
      rw [Real.posLog_def]; simp only [Pi.sup_apply, Pi.zero_apply]
      exact max_eq_right (Real.log_nonneg h.le)
    rw [this, Real.exp_log (by linarith), max_eq_right h.le]

theorem posLog_nonneg' (x : ℝ) : 0 ≤ Real.posLog x := by
  rw [Real.posLog_def]; simp only [Pi.sup_apply, Pi.zero_apply]; exact le_max_left _ _

theorem le_one_of_posLog_eq_zero {x : ℝ} (hx : 0 ≤ x) (h : Real.posLog x = 0) : x ≤ 1 := by
  have := exp_posLog hx
  rw [h, Real.exp_zero] at this
  exact this ▸ le_max_right 1 x

theorem le_exp_of_posLog_sq_le {y R : ℝ} (hy : 0 ≤ y) (hR : 0 ≤ R) (h : Real.posLog (y ^ 2) ≤ R) :
    y ≤ Real.exp R := by
  have h1 := exp_posLog (sq_nonneg y)
  have h2 : max 1 (y ^ 2) ≤ Real.exp R := h1 ▸ Real.exp_le_exp.2 h
  rcases le_or_gt y 1 with h3 | h3
  · exact h3.trans (Real.one_le_exp hR)
  · nlinarith [le_max_right 1 (y ^ 2)]

theorem norm_cV_alg (v : InfinitePlace E) (α : E) : ‖cV v (algebraMap E (Ad E) α)‖ = v α := by
  simp [cV, pInf_algebraMap, InfinitePlace.norm_embedding_eq]

theorem norm_cW_alg (w : HeightOneSpectrum (𝓞 E)) (α : E) :
    ‖cW w (algebraMap E (Ad E) α)‖ = NumberField.HeightOneSpectrum.adicAbv E w α :=
  FinitePlace.norm_embedding w α

theorem adicAbv_eq_zpow (w : HeightOneSpectrum (𝓞 E)) {α : E} (hα : α ≠ 0) :
    ∃ z : ℤ, NumberField.HeightOneSpectrum.adicAbv E w α = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ z := by
  have h0 : HeightOneSpectrum.valuation E w α ≠ 0 := (Valuation.ne_zero_iff _).2 hα
  refine ⟨(WithZero.unzero h0).toAdd, ?_⟩
  rw [HeightOneSpectrum.adicAbv_def, WithZeroMulInt.toNNReal_neg_apply _ h0]
  push_cast
  rfl

theorem adicAbv_le_one_iff (w : HeightOneSpectrum (𝓞 E)) (α : E) :
    NumberField.HeightOneSpectrum.adicAbv E w α ≤ 1 ↔ HeightOneSpectrum.valuation E w α ≤ 1 := by
  rw [HeightOneSpectrum.adicAbv_def, ← WithZeroMulInt.toNNReal_le_one_iff
    (HeightOneSpectrum.one_lt_absNorm_nnreal w)]
  exact NNReal.coe_le_one

theorem adicAbv_absNorm_le (w : HeightOneSpectrum (𝓞 E)) :
    NumberField.HeightOneSpectrum.adicAbv E w ((Ideal.absNorm w.asIdeal : ℕ) : E) ≤
      ((Ideal.absNorm w.asIdeal : ℕ) : ℝ)⁻¹ := by
  set N := Ideal.absNorm w.asIdeal
  have hN1 : 1 < N := HeightOneSpectrum.one_lt_absNorm w
  have hmem : ((N : ℕ) : 𝓞 E) ∈ w.asIdeal := Ideal.absNorm_mem _
  have hlt := (FinitePlace.norm_lt_one_iff_mem E w _).2 hmem
  rw [FinitePlace.norm_embedding, map_natCast] at hlt
  have hne : ((N : ℕ) : E) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨z, hz⟩ := adicAbv_eq_zpow w hne
  rw [hz] at hlt ⊢
  have hN : (1 : ℝ) < N := by exact_mod_cast hN1
  have hz0 : z < 0 := by
    by_contra h
    push_neg at h
    exact absurd hlt (not_lt.2 (one_le_zpow₀ hN.le h))
  calc (N : ℝ) ^ z ≤ (N : ℝ) ^ (-1 : ℤ) := zpow_le_zpow_right₀ hN.le (by omega)
    _ = _ := zpow_neg_one _

theorem exists_den (α : E) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ w ∉ S, NumberField.HeightOneSpectrum.adicAbv E w α ≤ 1) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ ∏ w ∈ S, max 1 (NumberField.HeightOneSpectrum.adicAbv E w α) ∧
      ∃ z : 𝓞 E, (z : E) = m * α := by
  classical
  by_cases hα : α = 0
  · refine ⟨1, one_pos, ?_, 0, by simp [hα]⟩
    rw [Nat.cast_one]
    calc (1 : ℝ) = ∏ _w ∈ S, (1 : ℝ) := Finset.prod_const_one.symm
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun _ _ => le_max_left _ _)
  set N : HeightOneSpectrum (𝓞 E) → ℕ := fun w => Ideal.absNorm w.asIdeal with hNdef
  have hN1 : ∀ w, (1 : ℝ) < N w := fun w => by exact_mod_cast HeightOneSpectrum.one_lt_absNorm w
  choose z hz using fun w => adicAbv_eq_zpow w hα
  set k : HeightOneSpectrum (𝓞 E) → ℕ := fun w => (z w).toNat
  have hk : ∀ w, ((N w : ℝ)) ^ k w = max 1 (NumberField.HeightOneSpectrum.adicAbv E w α) := by
    intro w
    rw [hz w]
    rcases le_or_gt 0 (z w) with h | h
    · have e : ((k w : ℕ) : ℤ) = z w := Int.toNat_of_nonneg h
      rw [← e, zpow_natCast, max_eq_right (one_le_pow₀ (hN1 w).le)]
    · have e : k w = 0 := Int.toNat_eq_zero.2 h.le
      rw [e, pow_zero, max_eq_left (zpow_le_one_of_nonpos₀ (hN1 w).le h.le)]
  refine ⟨∏ w ∈ S, N w ^ k w, Finset.prod_pos fun w _ => pow_pos (by have := hN1 w; exact_mod_cast (zero_lt_one.trans this)) _, ?_, ?_⟩
  · push_cast
    exact le_of_eq (Finset.prod_congr rfl fun w _ => hk w)
  · have hint : ∀ w0 : HeightOneSpectrum (𝓞 E),
        NumberField.HeightOneSpectrum.adicAbv E w0 (((∏ w ∈ S, N w ^ k w : ℕ) : E) * α) ≤ 1 := by
      intro w0
      set A := NumberField.HeightOneSpectrum.adicAbv E w0
      have hnn : ∀ w, 0 ≤ A ((N w : E) ^ k w) := fun w => A.nonneg _
      have hle1 : ∀ w, A ((N w : E) ^ k w) ≤ 1 := fun w => by
        rw [map_pow]
        exact pow_le_one₀ (A.nonneg _) (HeightOneSpectrum.adicAbv_natCast_le_one E w0 (N w))
      rw [map_mul, Nat.cast_prod, map_prod]
      push_cast
      by_cases hw0 : w0 ∈ S
      · rw [← Finset.mul_prod_erase S _ hw0]
        have h1 : ∏ w ∈ S.erase w0, A ((N w : E) ^ k w) ≤ 1 :=
          Finset.prod_le_one (fun w _ => hnn w) (fun w _ => hle1 w)
        have h2 : A ((N w0 : E) ^ k w0) ≤ ((N w0 : ℝ)⁻¹) ^ k w0 := by
          rw [map_pow]
          exact pow_le_pow_left₀ (A.nonneg _) (adicAbv_absNorm_le w0) _
        have h3 : A α ≤ (N w0 : ℝ) ^ k w0 := (hk w0).symm ▸ le_max_right _ _
        have h4 : ((N w0 : ℝ)⁻¹) ^ k w0 * (N w0 : ℝ) ^ k w0 = 1 := by
          rw [← mul_pow, inv_mul_cancel₀ (by linarith [hN1 w0]), one_pow]
        have hp0 : 0 ≤ ∏ w ∈ S.erase w0, A ((N w : E) ^ k w) := Finset.prod_nonneg fun w _ => hnn w
        calc (A ((N w0 : E) ^ k w0) * ∏ w ∈ S.erase w0, A ((N w : E) ^ k w)) * A α
            ≤ (((N w0 : ℝ)⁻¹) ^ k w0 * 1) * (N w0 : ℝ) ^ k w0 :=
              mul_le_mul (mul_le_mul h2 h1 hp0 (pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _)) h3
                (A.nonneg _) (mul_nonneg (pow_nonneg (inv_nonneg.2 (Nat.cast_nonneg _)) _) zero_le_one)
          _ = 1 := by rw [mul_one, h4]
      · have h1 : ∏ w ∈ S, A ((N w : E) ^ k w) ≤ 1 :=
          Finset.prod_le_one (fun w _ => hnn w) (fun w _ => hle1 w)
        calc (∏ w ∈ S, A ((N w : E) ^ k w)) * A α ≤ 1 * 1 :=
              mul_le_mul h1 (hS w0 hw0) (A.nonneg _) zero_le_one
          _ = 1 := one_mul 1
    obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E _
      fun w => (adicAbv_le_one_iff w _).1 (hint w)
    exact ⟨y, hy⟩

theorem posLog_eq_zero_of_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : Real.posLog x = 0 := by
  rw [Real.posLog_def]; simp only [Pi.sup_apply, Pi.zero_apply]
  exact max_eq_left (Real.log_nonpos hx0 hx1)

theorem supp_fin {n : ℕ} (A : Matrix (Fin n) (Fin n) (Ad E)) :
    (Function.support fun w : HeightOneSpectrum (𝓞 E) =>
      Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖)).Finite := by
  have hev : ∀ p : Fin n × Fin n, ∀ᶠ w in Filter.cofinite, ‖cW w (A p.1 p.2)‖ ≤ 1 := by
    intro p
    filter_upwards [RestrictedProduct.eventually _ _ (pFin E (A p.1 p.2))] with w hw
    have e : cW w (A p.1 p.2) = (pFin E (A p.1 p.2)) w := rfl
    rw [e, FinitePlace.norm_def, NNReal.coe_le_one,
      WithZeroMulInt.toNNReal_le_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal w)]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 hw
  have hall : ∀ᶠ w in Filter.cofinite, ∀ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖ ≤ 1 :=
    Filter.eventually_all.2 hev
  refine (Filter.eventually_cofinite.1 hall).subset fun w hw => ?_
  intro h
  exact hw (posLog_eq_zero_of_le_one (Real.iSup_nonneg fun _ => norm_nonneg _)
    (Real.iSup_le h zero_le_one))

theorem logSizeM_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) (Ad E)) : 0 ≤ logSizeM A :=
  add_nonneg (Finset.sum_nonneg fun _ _ => posLog_nonneg' _) (finsum_nonneg fun _ => posLog_nonneg' _)

def Bx (E : Type) [Field E] [NumberField E] (R : ℝ) : Set E :=
  {α | (∀ v : InfinitePlace E, v α ≤ Real.exp R) ∧
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp R ∧ ∃ z : 𝓞 E, (z : E) = m * α}

theorem entry_mem {n : ℕ} {R : ℝ} (hR : 0 ≤ R) (γ : GL (Fin n) E) (h : logSize (ratGL E n γ) ≤ R)
    (i j : Fin n) : (γ : Matrix (Fin n) (Fin n) E) i j ∈ Bx E R := by
  classical
  set A := (ratGL E n γ : Matrix (Fin n) (Fin n) (Ad E))
  set α := (γ : Matrix (Fin n) (Fin n) E) i j
  have hA : A i j = algebraMap E (Ad E) α := rfl
  have hM : logSizeM A ≤ R := le_trans (le_add_of_nonneg_right (logSizeM_nonneg _)) h
  set F : HeightOneSpectrum (𝓞 E) → ℝ := fun w => Real.posLog (⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖)
  have hF0 : ∀ w, 0 ≤ F w := fun w => posLog_nonneg' _
  have hinf0 : ∀ v, Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (A p.1 p.2)‖ ^ 2) ≤ R := by
    intro v
    refine le_trans ?_ hM
    refine le_trans ?_ (le_add_of_nonneg_right (finsum_nonneg fun w => hF0 w))
    exact Finset.single_le_sum (f := fun v => Real.posLog (⨆ p : Fin n × Fin n, ‖cV v (A p.1 p.2)‖ ^ 2))
      (fun _ _ => posLog_nonneg' _) (Finset.mem_univ v)
  refine ⟨fun v => ?_, ?_⟩
  · have h1 : ‖cV v (A i j)‖ ^ 2 ≤ ⨆ p : Fin n × Fin n, ‖cV v (A p.1 p.2)‖ ^ 2 :=
      le_ciSup (f := fun p : Fin n × Fin n => ‖cV v (A p.1 p.2)‖ ^ 2) (Set.finite_range _).bddAbove (i, j)
    have h2 := (Real.posLog_le_posLog (sq_nonneg _) h1).trans (hinf0 v)
    rw [hA, norm_cV_alg] at h2
    exact le_exp_of_posLog_sq_le (AbsoluteValue.nonneg _ _) hR h2
  · have hFfin := supp_fin A
    set S := hFfin.toFinset
    have hG : ∀ w, Real.posLog (NumberField.HeightOneSpectrum.adicAbv E w α) ≤ F w := by
      intro w
      have h1 : ‖cW w (A i j)‖ ≤ ⨆ p : Fin n × Fin n, ‖cW w (A p.1 p.2)‖ :=
        le_ciSup (f := fun p : Fin n × Fin n => ‖cW w (A p.1 p.2)‖) (Set.finite_range _).bddAbove (i, j)
      rw [hA, norm_cW_alg] at h1
      exact Real.posLog_le_posLog (AbsoluteValue.nonneg _ _) h1
    have hS : ∀ w ∉ S, NumberField.HeightOneSpectrum.adicAbv E w α ≤ 1 := by
      intro w hw
      rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hw
      refine le_one_of_posLog_eq_zero (AbsoluteValue.nonneg _ _) (le_antisymm ?_ (posLog_nonneg' _))
      exact (hG w).trans hw.le
    obtain ⟨m, hm, hmle, z, hz⟩ := exists_den α S hS
    refine ⟨m, hm, hmle.trans ?_, z, hz⟩
    have e1 : ∏ w ∈ S, max 1 (NumberField.HeightOneSpectrum.adicAbv E w α) =
        Real.exp (∑ w ∈ S, Real.posLog (NumberField.HeightOneSpectrum.adicAbv E w α)) := by
      rw [Real.exp_sum]
      exact Finset.prod_congr rfl fun w _ => (exp_posLog (AbsoluteValue.nonneg _ _)).symm
    rw [e1, Real.exp_le_exp]
    have e2 : ∑ᶠ w, F w = ∑ w ∈ S, F w := finsum_eq_sum F hFfin
    calc ∑ w ∈ S, Real.posLog (NumberField.HeightOneSpectrum.adicAbv E w α) ≤ ∑ w ∈ S, F w :=
          Finset.sum_le_sum fun w _ => hG w
      _ = ∑ᶠ w, F w := e2.symm
      _ ≤ logSizeM A := le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => posLog_nonneg' _)
      _ ≤ R := hM

theorem bx_count : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → (Bx E R).Finite ∧
    ((Bx E R).ncard : ℝ) ≤ C * Real.exp ((2 * Module.finrank ℚ E + 1) * R) := by
  classical
  obtain ⟨C₂, hC₂, hcount⟩ := GroundTheory.Automorphic.CuspidalSpectrum.exists_ncard_integers_le E
  set d := Module.finrank ℚ E
  refine ⟨C₂ * 2 ^ d, by positivity, fun R hR => ?_⟩
  have hT : 0 ≤ Real.exp (2 * R) := (Real.exp_pos _).le
  obtain ⟨hZf, hZc⟩ := hcount (Real.exp (2 * R)) hT
  set M := ⌊Real.exp R⌋₊
  set T : Finset E := ((Finset.Icc 1 M) ×ˢ hZf.toFinset).image fun p : ℕ × 𝓞 E => (p.2 : E) / p.1
  have hsub : Bx E R ⊆ (T : Set E) := by
    rintro α ⟨hv, m, hm, hmR, z, hz⟩
    rw [Finset.mem_coe, Finset.mem_image]
    refine ⟨(m, z), ?_, ?_⟩
    · rw [Finset.mem_product, Finset.mem_Icc, Set.Finite.mem_toFinset]
      refine ⟨⟨hm, Nat.le_floor hmR⟩, fun w => ?_⟩
      rw [hz, map_mul, InfinitePlace.map_natCast]
      have e : Real.exp (2 * R) = Real.exp R * Real.exp R := by rw [← Real.exp_add]; ring_nf
      rw [e]
      exact mul_le_mul hmR (hv w) (AbsoluteValue.nonneg _ _) (Real.exp_pos _).le
    · have hm0 : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
      show (z : E) / m = α
      rw [hz]; field_simp
  refine ⟨(Finset.finite_toSet T).subset hsub, ?_⟩
  have h1 : (Bx E R).ncard ≤ T.card := by
    rw [← Set.ncard_coe_finset]; exact Set.ncard_le_ncard hsub (Finset.finite_toSet T)
  have h2 : T.card ≤ M * hZf.toFinset.card := by
    refine (Finset.card_image_le).trans ?_
    rw [Finset.card_product, Nat.card_Icc, Nat.add_sub_cancel]
  have h3 : (hZf.toFinset.card : ℝ) ≤ C₂ * (1 + Real.exp (2 * R)) ^ d := by
    rw [← Set.ncard_eq_toFinset_card _ hZf]; exact hZc
  have hM : (M : ℝ) ≤ Real.exp R := Nat.floor_le (Real.exp_pos _).le
  have h4 : (1 + Real.exp (2 * R)) ^ d ≤ 2 ^ d * Real.exp (d * (2 * R)) := by
    rw [Real.exp_nat_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.one_le_exp (by linarith : (0:ℝ) ≤ 2 * R)]) _
  have e : Real.exp ((2 * d + 1) * R) = Real.exp R * Real.exp (d * (2 * R)) := by
    rw [← Real.exp_add]; ring_nf
  calc ((Bx E R).ncard : ℝ) ≤ (M : ℝ) * hZf.toFinset.card := by exact_mod_cast h1.trans h2
    _ ≤ Real.exp R * (C₂ * (2 ^ d * Real.exp (d * (2 * R)))) :=
        mul_le_mul hM (h3.trans (mul_le_mul_of_nonneg_left h4 hC₂)) (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = C₂ * 2 ^ d * Real.exp ((2 * d + 1) * R) := by rw [e]; ring

theorem gl_count (n : ℕ) : ∃ C K : ℝ, 0 ≤ C ∧ 0 ≤ K ∧ ∀ R : ℝ, 0 ≤ R →
    {γ : GL (Fin n) E | logSize (ratGL E n γ) ≤ R}.Finite ∧
    ({γ : GL (Fin n) E | logSize (ratGL E n γ) ≤ R}.ncard : ℝ) ≤ C * Real.exp (K * R) := by
  classical
  obtain ⟨C, hC, hB⟩ := bx_count (E := E)
  set d := Module.finrank ℚ E
  refine ⟨C ^ (n * n), (2 * d + 1) * ((n * n : ℕ) : ℝ), by positivity, by positivity, fun R hR => ?_⟩
  obtain ⟨hf, hc⟩ := hB R hR
  set F := hf.toFinset
  set Φ : GL (Fin n) E → Fin n → Fin n → E := fun γ i j => (γ : Matrix (Fin n) (Fin n) E) i j
  set box : Finset (Fin n → Fin n → E) := Fintype.piFinset fun _ => Fintype.piFinset fun _ => F
  have hmaps : ∀ γ ∈ {γ : GL (Fin n) E | logSize (ratGL E n γ) ≤ R}, Φ γ ∈ (box : Set _) := by
    intro γ hγ
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Fintype.mem_piFinset]
    intro j
    rw [Set.Finite.mem_toFinset]
    exact entry_mem hR γ hγ i j
  have hinj : Set.InjOn Φ {γ : GL (Fin n) E | logSize (ratGL E n γ) ≤ R} := fun γ _ γ' _ h =>
    Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j)
  have hfin : (box : Set (Fin n → Fin n → E)).Finite := Finset.finite_toSet _
  refine ⟨hfin.of_injOn hmaps hinj, ?_⟩
  have hcard := Set.ncard_le_ncard_of_injOn Φ hmaps hinj hfin
  rw [Set.ncard_coe_finset] at hcard
  simp only [box, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcard
  have hF : (F.card : ℝ) ≤ C * Real.exp ((2 * d + 1) * R) := by
    rw [← Set.ncard_eq_toFinset_card _ hf]; exact hc
  calc (({γ : GL (Fin n) E | logSize (ratGL E n γ) ≤ R}.ncard : ℕ) : ℝ)
      ≤ (((F.card ^ n) ^ n : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (F.card : ℝ) ^ (n * n) := by push_cast; rw [← pow_mul]
    _ ≤ (C * Real.exp ((2 * d + 1) * R)) ^ (n * n) := pow_le_pow_left₀ (Nat.cast_nonneg _) hF _
    _ = C ^ (n * n) * Real.exp ((2 * d + 1) * ((n * n : ℕ) : ℝ) * R) := by
        rw [mul_pow, ← Real.exp_nat_mul]; congr 2; ring

section Pair

open PositivityTheory.Rg.BcB.E
open scoped ENNReal Pointwise

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

theorem countable_E : Countable E :=
  (Module.finBasis ℚ E).equivFun.injective.countable

theorem countable_GL (n : ℕ) : Countable (GL (Fin n) E) := by
  haveI := countable_E (E := E)
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  exact Function.Injective.countable (f := (Units.val : GL (Fin n) E → Matrix (Fin n) (Fin n) E)) fun _ _ h => Units.ext h

theorem countable_ratH (a b : ℕ) : Countable (ratH E a b) := by
  haveI := countable_GL (E := E) a
  haveI := countable_GL (E := E) b
  exact ((ratGL E a).prodMap (ratGL E b)).rangeRestrict_surjective.countable

theorem measurableMul_H (a b : ℕ) : MeasurableMul (H E a b) :=
  haveI : BorelSpace (H E a b) := ⟨rfl⟩
  ⟨fun c => (continuous_const.mul continuous_id).measurable, fun c => (continuous_id.mul continuous_const).measurable⟩

theorem mem_ratH {a b : ℕ} (δ : ratH E a b) :
    ∃ (γ₁ : GL (Fin a) E) (γ₂ : GL (Fin b) E), (δ : H E a b) = (ratGL E a γ₁, ratGL E b γ₂) := by
  obtain ⟨⟨γ₁, γ₂⟩, h⟩ := δ.2
  exact ⟨γ₁, γ₂, h.symm⟩

theorem fold {a b : ℕ} (D : Dom E a b) (g : H E a b → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ y, g y ∂D.μ = ∫⁻ y, ∑' γ : ratH E a b, g ((γ : H E a b) * y) ∂D.ν := by
  haveI : BorelSpace (H E a b) := ⟨rfl⟩
  haveI := measurableMul_H (E := E) a b
  haveI := D.haar.1
  haveI := countable_ratH (E := E) a b
  haveI : MeasurableConstSMul (ratH E a b) (H E a b) :=
    ⟨fun γ => (continuous_const.mul continuous_id).measurable⟩
  haveI : SMulInvariantMeasure (ratH E a b) (H E a b) D.μ :=
    ⟨fun γ s _ => measure_preimage_mul D.μ (γ : H E a b) s⟩
  rw [D.fd.lintegral_eq_tsum'' g, Dom.ν, lintegral_tsum]
  · rfl
  · intro γ
    exact (hg.comp (continuous_const.mul continuous_id).measurable).aemeasurable

theorem logSize_inv {n : ℕ} (g : GA E n) : logSize g⁻¹ = logSize g := by
  unfold logSize; rw [inv_inv, add_comm]

theorem redSize_nonneg (hS : SizeBasic) {n : ℕ} (g : GA E n) : 0 ≤ redSize g :=
  le_ciInf fun γ => (hS E n).2.1 _

theorem redSize_le (hS : SizeBasic) {n : ℕ} (γ : GL (Fin n) E) (g : GA E n) :
    redSize g ≤ logSize (ratGL E n γ * g) :=
  ciInf_le (f := fun γ : GL (Fin n) E => logSize (ratGL E n γ * g))
    ⟨0, by rintro _ ⟨δ, rfl⟩; exact (hS E n).2.1 _⟩ γ

theorem tsum_indicator_one {α : Type} (T : Set α) (hT : T.Finite) :
    ∑' δ, T.indicator (1 : α → ℝ≥0∞) δ = (T.ncard : ℝ≥0∞) := by
  classical
  rw [tsum_eq_sum (s := hT.toFinset) fun δ hδ => Set.indicator_of_notMem (by simpa using hδ) _]
  rw [Finset.sum_congr rfl fun δ hδ => Set.indicator_of_mem (by simpa using hδ) (1 : α → ℝ≥0∞)]
  simp [Set.ncard_eq_toFinset_card _ hT]

end Pair

section Main

open PositivityTheory.Rg.BcB.E
open scoped ENNReal Pointwise

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

theorem conj_count (hS : SizeBasic) {a b : ℕ} (Q : Set (H E a b)) (hQ : IsCompact Q) :
    ∃ n₀ k₀ : ℝ, 0 ≤ n₀ ∧ 0 ≤ k₀ ∧ ∀ x : H E a b,
      ∑' δ : ratH E a b, Q.indicator (1 : H E a b → ℝ≥0∞) (x⁻¹ * (δ : H E a b) * x) ≤
        ENNReal.ofReal (n₀ * Real.exp (k₀ * (logSize x.1 + logSize x.2))) := by
  classical
  obtain ⟨hc1, hn1, -, c1, hm1⟩ := hS E a
  obtain ⟨hc2, hn2, -, c2, hm2⟩ := hS E b
  obtain ⟨r1, hr1⟩ := hc1 (Prod.fst '' Q) (hQ.image continuous_fst)
  obtain ⟨r2, hr2⟩ := hc2 (Prod.snd '' Q) (hQ.image continuous_snd)
  obtain ⟨C1, K1, hC1, hK1, hA1⟩ := gl_count (E := E) a
  obtain ⟨C2, K2, hC2, hK2, hA2⟩ := gl_count (E := E) b
  set q1 := max 0 r1 + 2 * |c1|
  set q2 := max 0 r2 + 2 * |c2|
  have hq1 : 0 ≤ q1 := by positivity
  have hq2 : 0 ≤ q2 := by positivity
  refine ⟨C1 * C2 * Real.exp (K1 * q1 + K2 * q2), 2 * (K1 + K2), by positivity, by positivity, fun x => ?_⟩
  have hx1 := hn1 x.1
  have hx2 := hn2 x.2
  set R1 := 2 * logSize x.1 + q1
  set R2 := 2 * logSize x.2 + q2
  have hR1 : 0 ≤ R1 := by positivity
  have hR2 : 0 ≤ R2 := by positivity
  obtain ⟨hf1, hcard1⟩ := hA1 R1 hR1
  obtain ⟨hf2, hcard2⟩ := hA2 R2 hR2
  set A1 := {γ : GL (Fin a) E | logSize (ratGL E a γ) ≤ R1}
  set A2 := {γ : GL (Fin b) E | logSize (ratGL E b γ) ≤ R2}
  set e : GL (Fin a) E × GL (Fin b) E → ratH E a b :=
    fun p => ⟨((ratGL E a).prodMap (ratGL E b)) p, ⟨p, rfl⟩⟩
  set T := e '' (A1 ×ˢ A2)
  have hT : T.Finite := (hf1.prod hf2).image e
  have hle : ∀ δ : ratH E a b, Q.indicator (1 : H E a b → ℝ≥0∞) (x⁻¹ * (δ : H E a b) * x) ≤
      T.indicator 1 δ := by
    intro δ
    by_cases hδ : x⁻¹ * (δ : H E a b) * x ∈ Q
    · obtain ⟨γ₁, γ₂, hγ⟩ := mem_ratH δ
      set q := x⁻¹ * (δ : H E a b) * x
      have hxq : (δ : H E a b) = x * q * x⁻¹ := by simp only [q]; group
      have e1 : ratGL E a γ₁ = x.1 * q.1 * x.1⁻¹ := by
        have := congrArg Prod.fst hxq
        rw [hγ] at this
        simpa using this
      have e2 : ratGL E b γ₂ = x.2 * q.2 * x.2⁻¹ := by
        have := congrArg Prod.snd hxq
        rw [hγ] at this
        simpa using this
      have hmem : δ ∈ T := by
        refine ⟨(γ₁, γ₂), ⟨?_, ?_⟩, Subtype.ext hγ.symm⟩
        · show logSize (ratGL E a γ₁) ≤ R1
          rw [e1]
          have h1 := hm1 (x.1 * q.1) x.1⁻¹
          have h2 := hm1 x.1 q.1
          have h3 := hr1 q.1 ⟨q, hδ, rfl⟩
          rw [logSize_inv] at h1
          have := le_max_right 0 r1
          have := le_abs_self c1
          linarith
        · show logSize (ratGL E b γ₂) ≤ R2
          rw [e2]
          have h1 := hm2 (x.2 * q.2) x.2⁻¹
          have h2 := hm2 x.2 q.2
          have h3 := hr2 q.2 ⟨q, hδ, rfl⟩
          rw [logSize_inv] at h1
          have := le_max_right 0 r2
          have := le_abs_self c2
          linarith
      rw [Set.indicator_of_mem hδ, Set.indicator_of_mem hmem]
      exact le_rfl
    · rw [Set.indicator_of_notMem hδ]
      exact zero_le
  refine (ENNReal.tsum_le_tsum hle).trans ?_
  rw [tsum_indicator_one T hT, ← ENNReal.ofReal_natCast]
  refine ENNReal.ofReal_le_ofReal ?_
  have hT1 : (T.ncard : ℝ) ≤ (A1.ncard : ℝ) * A2.ncard := by
    have := (Set.ncard_image_le (f := e) (hf1.prod hf2)).trans (le_of_eq (Set.ncard_prod (s := A1) (t := A2)))
    exact_mod_cast this
  have hexp : Real.exp (K1 * R1) * Real.exp (K2 * R2) ≤
      Real.exp (K1 * q1 + K2 * q2) * Real.exp (2 * (K1 + K2) * (logSize x.1 + logSize x.2)) := by
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
    simp only [R1, R2]
    nlinarith [mul_nonneg hK1 hx2, mul_nonneg hK2 hx1]
  calc (T.ncard : ℝ) ≤ (A1.ncard : ℝ) * A2.ncard := hT1
    _ ≤ (C1 * Real.exp (K1 * R1)) * (C2 * Real.exp (K2 * R2)) :=
        mul_le_mul hcard1 hcard2 (Nat.cast_nonneg _) (by positivity)
    _ = C1 * C2 * (Real.exp (K1 * R1) * Real.exp (K2 * R2)) := by ring
    _ ≤ C1 * C2 * (Real.exp (K1 * q1 + K2 * q2) * Real.exp (2 * (K1 + K2) * (logSize x.1 + logSize x.2))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by ring

end Main

section Growth

open PositivityTheory.Rg.BcB.E
open scoped ENNReal Pointwise

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

theorem amgm (p q : ℝ≥0∞) : p * q ≤ p ^ 2 + q ^ 2 := by
  rcases le_total p q with h | h
  · calc p * q ≤ q * q := mul_le_mul_left h q
      _ = q ^ 2 := (sq q).symm
      _ ≤ _ := le_add_self
  · calc p * q ≤ p * p := mul_le_mul_right h p
      _ = p ^ 2 := (sq p).symm
      _ ≤ _ := le_self_add

theorem inv_pow_sq (w : ℝ) (M : ℕ) : ((w ^ M)⁻¹) ^ 2 = w ^ (-(2 * M : ℤ)) := by
  rw [_root_.zpow_neg, show (2 * (M : ℤ)) = ((M * 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, pow_mul, inv_pow]

theorem growth_main (hS : SizeBasic) (a b : ℕ) (D : Dom E a b) (ι : Type) [Fintype ι]
    (Φ : Matrix ι ι (H E a b → ℂ)) (M : ℕ) (f : ι → H E a b → ℂ) (c : ℂ) (hΦ : IsTestM Φ)
    (hf : ∀ i, Continuous (f i)) (hL : LeftInv f) (hW : WL2 D M f) (hc : c ≠ 0)
    (hconv : PositivityTheory.Rg.BcB.E.conv D.μ Φ f = c • f) :
    ∃ C N : ℝ, ∀ i x, ‖f i x‖ ≤ C * Real.exp (N * (logSize x.1 + logSize x.2)) := by
  classical
  haveI : BorelSpace (H E a b) := ⟨rfl⟩
  haveI := measurableMul_H (E := E) a b
  haveI := D.haar.1
  haveI := D.haar.2.2.2
  haveI := countable_ratH (E := E) a b
  obtain ⟨hc1, hn1, -, c1, hm1⟩ := hS E a
  obtain ⟨hc2, hn2, -, c2, hm2⟩ := hS E b

  set S : Set (H E a b) := ⋃ i, ⋃ j, tsupport (Φ i j) with hSdef
  have hScpt : IsCompact S := isCompact_iUnion fun i => isCompact_iUnion fun j => (hΦ i j).2
  have hSm : MeasurableSet S :=
    (isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j => isClosed_tsupport _).measurableSet
  have hμS : D.μ S ≠ ⊤ :=
    (hScpt.measure_lt_top_of_nhdsWithin fun x _ => (D.μ.finiteAt_nhds x).filter_mono inf_le_left).ne

  choose Cb hCb using fun i j => (hΦ i j).1.bounded_above_of_compact_support (hΦ i j).2
  set B0 : ℝ := ∑ i, ∑ j, |Cb i j|
  have hB0 : 0 ≤ B0 := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hΦB : ∀ i j y, ‖Φ i j y‖ ≤ B0 := fun i j y =>
    (hCb i j y).trans ((le_abs_self _).trans ((Finset.single_le_sum (f := fun j => |Cb i j|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans (Finset.single_le_sum
        (f := fun i => ∑ j, |Cb i j|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))))
  have hΦS : ∀ i j y, ENNReal.ofReal ‖Φ i j y‖ ≤ ENNReal.ofReal B0 * S.indicator 1 y := by
    intro i j y
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy, Pi.one_apply, mul_one]
      exact ENNReal.ofReal_le_ofReal (hΦB i j y)
    · have : y ∉ tsupport (Φ i j) := fun h => hy (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, h⟩⟩)
      rw [image_eq_zero_of_notMem_tsupport this]
      simp

  set Q : Set (H E a b) := S * S⁻¹
  obtain ⟨n₀, k₀, hn₀, hk₀, hN⟩ := conj_count hS Q (hScpt.mul hScpt.inv)
  obtain ⟨scaledBoxRadiiAtEntry, hrS1⟩ := hc1 (Prod.fst '' S) (hScpt.image continuous_fst)
  obtain ⟨rS2, hrS2⟩ := hc2 (Prod.snd '' S) (hScpt.image continuous_snd)
  set w0 : ℝ := max 0 scaledBoxRadiiAtEntry + max 0 rS2 + |c1| + |c2|
  have hw0 : 0 ≤ w0 := by positivity

  set I : ι → ℝ≥0∞ := fun j => ∫⁻ y, ENNReal.ofReal (wt y ^ (-(2 * M : ℤ))) * ‖f j y‖ₑ ^ 2 ∂D.ν
  set i0 : ℝ := ∑ j, (I j).toReal
  have hi0 : 0 ≤ i0 := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hI : ∀ j, I j ≤ ENNReal.ofReal i0 := fun j => by
    refine le_of_eq_of_le (ENNReal.ofReal_toReal (hW j).ne).symm ?_
    exact ENNReal.ofReal_le_ofReal (Finset.single_le_sum (f := fun j => (I j).toReal)
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ j))
  set s0 : ℝ := (D.μ S).toReal
  have hs0 : 0 ≤ s0 := ENNReal.toReal_nonneg
  set Kst : ℝ := B0 * (n₀ * Real.exp (2 * M * w0) * s0 + i0)
  have hKst : 0 ≤ Kst := by positivity
  set Kex : ℝ := k₀ + 2 * M
  have hmi : ∀ x : H E a b, Measurable fun y : H E a b => S.indicator (1 : H E a b → ℝ≥0∞) (x⁻¹ * y) :=
    fun x => ((measurable_const (a := (1 : ℝ≥0∞))).indicator hSm).comp (measurable_const_mul x⁻¹)
  have hfm : ∀ j, Measurable fun y => ‖f j y‖ₑ := fun j => (hf j).measurable.enorm
  have key : ∀ i j x, ∫⁻ y, ENNReal.ofReal ‖Φ i j y * f j (x * y)‖ ∂D.μ ≤
      ENNReal.ofReal (Kst * Real.exp (Kex * (logSize x.1 + logSize x.2))) := by
    intro i j x
    have hx1 := hn1 x.1
    have hx2 := hn2 x.2
    set Lx := logSize x.1 + logSize x.2
    have hLx : 0 ≤ Lx := by positivity
    set P : H E a b → ℝ≥0∞ := fun y => ∑' γ : ratH E a b, S.indicator 1 (x⁻¹ * ((γ : H E a b) * y))
    have hPm : Measurable P := Measurable.ennreal_tsum fun γ => (hmi x).comp (measurable_const_mul _)
    have s1 : ∫⁻ y, ENNReal.ofReal ‖Φ i j y * f j (x * y)‖ ∂D.μ ≤
        ENNReal.ofReal B0 * ∫⁻ y, S.indicator 1 (x⁻¹ * y) * ‖f j y‖ₑ ∂D.μ := by
      rw [← lintegral_mul_left_eq_self (fun y => S.indicator (1 : H E a b → ℝ≥0∞) (x⁻¹ * y) * ‖f j y‖ₑ) x,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      refine lintegral_mono fun y => ?_
      simp only [inv_mul_cancel_left]
      rw [norm_mul, ENNReal.ofReal_mul (norm_nonneg _), ← mul_assoc, ofReal_norm_eq_enorm (f j (x * y))]
      exact mul_le_mul' (hΦS i j y) le_rfl
    have s2 : ∫⁻ y, S.indicator 1 (x⁻¹ * y) * ‖f j y‖ₑ ∂D.μ = ∫⁻ y, P y * ‖f j y‖ₑ ∂D.ν := by
      rw [fold D (fun y => S.indicator (1 : H E a b → ℝ≥0∞) (x⁻¹ * y) * ‖f j y‖ₑ) ((hmi x).mul (hfm j))]
      refine lintegral_congr fun y => ?_
      simp only [P]
      rw [← ENNReal.tsum_mul_right]
      refine tsum_congr fun γ => ?_
      rw [hL j γ y]
    have hP1 : ∀ y, P y ≠ 0 → P y ≤ ∑' δ : ratH E a b, Q.indicator 1 (x⁻¹ * (δ : H E a b) * x) ∧
        wt y ≤ 1 + Lx + w0 := by
      intro y hy
      obtain ⟨γ0, hγ0⟩ : ∃ γ0 : ratH E a b, x⁻¹ * ((γ0 : H E a b) * y) ∈ S := by
        by_contra hne
        push_neg at hne
        exact hy (ENNReal.tsum_eq_zero.2 fun γ => Set.indicator_of_notMem (hne γ) _)
      constructor
      · rw [← (Equiv.mulRight γ0⁻¹).tsum_eq (fun δ : ratH E a b => Q.indicator (1 : H E a b → ℝ≥0∞)
          (x⁻¹ * (δ : H E a b) * x))]
        refine ENNReal.tsum_le_tsum fun γ => ?_
        by_cases hγ : x⁻¹ * ((γ : H E a b) * y) ∈ S
        · have hq : x⁻¹ * ((Equiv.mulRight γ0⁻¹ γ : ratH E a b) : H E a b) * x ∈ Q := by
            have e : x⁻¹ * ((Equiv.mulRight γ0⁻¹ γ : ratH E a b) : H E a b) * x =
                (x⁻¹ * ((γ : H E a b) * y)) * (x⁻¹ * ((γ0 : H E a b) * y))⁻¹ := by
              simp only [Equiv.coe_mulRight, Subgroup.coe_mul, Subgroup.coe_inv]
              group
            rw [e]
            exact Set.mul_mem_mul hγ (Set.inv_mem_inv.2 hγ0)
          rw [Set.indicator_of_mem hγ, Set.indicator_of_mem hq]
          exact le_rfl
        · rw [Set.indicator_of_notMem hγ]
          exact zero_le
      · obtain ⟨γ₁, γ₂, hγ⟩ := mem_ratH γ0
        set s := x⁻¹ * ((γ0 : H E a b) * y)
        have hxs : (γ0 : H E a b) * y = x * s := by simp only [s, mul_inv_cancel_left]
        have hs1 : ratGL E a γ₁ * y.1 = x.1 * s.1 := by
          have := congrArg Prod.fst hxs
          rw [hγ] at this
          simpa using this
        have hs2 : ratGL E b γ₂ * y.2 = x.2 * s.2 := by
          have := congrArg Prod.snd hxs
          rw [hγ] at this
          simpa using this
        have h1 := redSize_le hS γ₁ y.1
        have h2 := redSize_le hS γ₂ y.2
        rw [hs1] at h1
        rw [hs2] at h2
        have h3 := hm1 x.1 s.1
        have h4 := hm2 x.2 s.2
        have h5 := hrS1 s.1 ⟨s, hγ0, rfl⟩
        have h6 := hrS2 s.2 ⟨s, hγ0, rfl⟩
        have := le_max_right 0 scaledBoxRadiiAtEntry
        have := le_max_right 0 rS2
        have := le_abs_self c1
        have := le_abs_self c2
        show 1 + redSize y.1 + redSize y.2 ≤ 1 + Lx + w0
        simp only [Lx, w0]
        linarith
    set Nb := ENNReal.ofReal (n₀ * Real.exp (k₀ * Lx))
    set Ub := ENNReal.ofReal ((1 + Lx + w0) ^ (2 * M))
    have s3 : ∀ y, P y * ‖f j y‖ₑ ≤
        (Nb * Ub) * P y + ENNReal.ofReal (wt y ^ (-(2 * M : ℤ))) * ‖f j y‖ₑ ^ 2 := by
      intro y
      by_cases hy : P y = 0
      · rw [hy, zero_mul]
        exact zero_le
      obtain ⟨hPN, hwt⟩ := hP1 y hy
      have hw1 : 1 ≤ wt y := by
        show 1 ≤ 1 + redSize y.1 + redSize y.2
        linarith [redSize_nonneg hS y.1, redSize_nonneg hS y.2]
      have hwp : 0 < wt y ^ M := pow_pos (by linarith) M
      set u := ENNReal.ofReal (wt y ^ M)
      set v := ENNReal.ofReal ((wt y ^ M)⁻¹)
      have huv : u * v = 1 := by
        rw [← ENNReal.ofReal_mul hwp.le, mul_inv_cancel₀ hwp.ne', ENNReal.ofReal_one]
      have hv2 : v ^ 2 = ENNReal.ofReal (wt y ^ (-(2 * M : ℤ))) := by
        rw [← ENNReal.ofReal_pow (inv_nonneg.2 hwp.le), inv_pow_sq]
      have hu2 : u ^ 2 ≤ Ub := by
        rw [← ENNReal.ofReal_pow hwp.le, ← pow_mul, mul_comm M 2]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by linarith) hwt _)
      have hPu : P y * u ^ 2 ≤ Nb * Ub := mul_le_mul' (hPN.trans (hN x)) hu2
      calc P y * ‖f j y‖ₑ = (P y * u) * (‖f j y‖ₑ * v) := by
            rw [mul_mul_mul_comm, huv, mul_one]
        _ ≤ (P y * u) ^ 2 + (‖f j y‖ₑ * v) ^ 2 := amgm _ _
        _ = P y * (P y * u ^ 2) + v ^ 2 * ‖f j y‖ₑ ^ 2 := by ring
        _ ≤ P y * (Nb * Ub) + ENNReal.ofReal (wt y ^ (-(2 * M : ℤ))) * ‖f j y‖ₑ ^ 2 := by
            rw [hv2]
            exact add_le_add (mul_le_mul' le_rfl hPu) le_rfl
        _ = _ := by ring
    have s4 : ∫⁻ y, P y ∂D.ν = D.μ S := by
      rw [← fold D _ (hmi x), ← lintegral_mul_left_eq_self (fun y => S.indicator (1 : H E a b → ℝ≥0∞) (x⁻¹ * y)) x]
      simp only [inv_mul_cancel_left]
      exact lintegral_indicator_one hSm
    have s5 : ∫⁻ y, P y * ‖f j y‖ₑ ∂D.ν ≤ Nb * Ub * D.μ S + I j := by
      refine (lintegral_mono s3).trans (le_of_eq ?_)
      rw [lintegral_add_left (hPm.const_mul _), lintegral_const_mul _ hPm, s4]
    have hW' : (1 + Lx + w0) ^ (2 * M) ≤ Real.exp (2 * M * w0) * Real.exp (2 * M * Lx) := by
      calc (1 + Lx + w0) ^ (2 * M) ≤ (Real.exp (Lx + w0)) ^ (2 * M) :=
            pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (Lx + w0)]) _
        _ = _ := by
            rw [← Real.exp_nat_mul, ← Real.exp_add]
            congr 1
            push_cast
            ring
    have hE1 : 1 ≤ Real.exp (Kex * Lx) := Real.one_le_exp (by positivity)
    have e : Real.exp (k₀ * Lx) * Real.exp (2 * M * Lx) = Real.exp (Kex * Lx) := by
      rw [← Real.exp_add]
      congr 1
      simp only [Kex]
      ring
    have hreal : B0 * (n₀ * Real.exp (k₀ * Lx) * (1 + Lx + w0) ^ (2 * M) * s0 + i0) ≤
        Kst * Real.exp (Kex * Lx) := by
      have h1 : n₀ * Real.exp (k₀ * Lx) * (1 + Lx + w0) ^ (2 * M) * s0 ≤
          n₀ * Real.exp (k₀ * Lx) * (Real.exp (2 * M * w0) * Real.exp (2 * M * Lx)) * s0 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW' (by positivity)) hs0
      have h2 : i0 ≤ i0 * Real.exp (Kex * Lx) := le_mul_of_one_le_right hi0 hE1
      calc B0 * (n₀ * Real.exp (k₀ * Lx) * (1 + Lx + w0) ^ (2 * M) * s0 + i0)
          ≤ B0 * (n₀ * Real.exp (k₀ * Lx) * (Real.exp (2 * M * w0) * Real.exp (2 * M * Lx)) * s0 +
              i0 * Real.exp (Kex * Lx)) := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hB0
        _ = B0 * (n₀ * Real.exp (2 * M * w0) * s0 * (Real.exp (k₀ * Lx) * Real.exp (2 * M * Lx)) +
              i0 * Real.exp (Kex * Lx)) := by ring
        _ = Kst * Real.exp (Kex * Lx) := by rw [e]; ring
    calc ∫⁻ y, ENNReal.ofReal ‖Φ i j y * f j (x * y)‖ ∂D.μ
        ≤ ENNReal.ofReal B0 * ∫⁻ y, P y * ‖f j y‖ₑ ∂D.ν := s2 ▸ s1
      _ ≤ ENNReal.ofReal B0 * (Nb * Ub * ENNReal.ofReal s0 + ENNReal.ofReal i0) := by
          rw [ENNReal.ofReal_toReal hμS]
          exact mul_le_mul' le_rfl (s5.trans (add_le_add le_rfl (hI j)))
      _ = ENNReal.ofReal (B0 * (n₀ * Real.exp (k₀ * Lx) * (1 + Lx + w0) ^ (2 * M) * s0 + i0)) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) hi0, ← ENNReal.ofReal_mul hB0]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
  refine ⟨(Fintype.card ι : ℝ) * Kst / ‖c‖, Kex, fun i x => ?_⟩
  have hcx : ‖c‖ * ‖f i x‖ ≤ (Fintype.card ι : ℝ) * (Kst * Real.exp (Kex * (logSize x.1 + logSize x.2))) := by
    have e := congrFun (congrFun hconv i) x
    simp only [PositivityTheory.Rg.BcB.E.conv, Pi.smul_apply, smul_eq_mul] at e
    rw [← norm_mul, ← e]
    calc ‖∑ j, ∫ y, Φ i j y * f j (x * y) ∂D.μ‖ ≤ ∑ j, ‖∫ y, Φ i j y * f j (x * y) ∂D.μ‖ := norm_sum_le _ _
      _ ≤ ∑ _j : ι, Kst * Real.exp (Kex * (logSize x.1 + logSize x.2)) :=
          Finset.sum_le_sum fun j _ => (norm_integral_le_lintegral_norm _).trans
            (ENNReal.toReal_le_of_le_ofReal (by positivity) (key i j x))
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc0 : 0 < ‖c‖ := norm_pos_iff.2 hc
  rw [div_mul_eq_mul_div, le_div_iff₀ hc0]
  calc ‖f i x‖ * ‖c‖ = ‖c‖ * ‖f i x‖ := mul_comm _ _
    _ ≤ _ := hcx
    _ = _ := by ring

end Growth

end PositivityTheory.Rg.BcB.CG.HeightGrowth

namespace PositivityTheory.Rg.BcB.CG

theorem growthOf (hS : SizeBasic) : GrowthOf :=
  fun _ _ _ _ a b D ι _ Φ M f c hΦ hf hL hW hc hconv =>
    HeightGrowth.growth_main hS a b D ι Φ M f c hΦ hf hL hW hc hconv

end PositivityTheory.Rg.BcB.CG

end
