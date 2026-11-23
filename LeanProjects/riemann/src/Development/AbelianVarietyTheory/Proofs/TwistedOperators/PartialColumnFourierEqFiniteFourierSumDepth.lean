import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingPiCurry

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.ColFourier
open scoped Pointwise

noncomputable section
namespace GlobalTheory.ColFourier

section Lemmas
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {A C : Type} [Fintype A] [DecidableEq C]

theorem mem_maxIdeal_pow_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (n : ℕ) (r : 𝒪[k]) :
    r ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ n ↔ valuation k (r : k) ≤ valuation k ((ϖ ^ n : kˣ) : k) := by
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← (Valuation.integer.integers (valuation k)).le_iff_dvd]
  rfl

theorem natDatum_setCols_eq {ϖ : kˣ} {n : ℕ} {Φ : Matrix A C k → ℂ} (hΦ : IsNatDatum ϖ n Φ) (P : Finset C)
    (Y : Matrix A C k) {U V : Matrix A P k} (h : ∀ i j, U i j - V i j ∈ cball (ϖ ^ n)) :
    Φ (setCols P Y U) = Φ (setCols P Y V) := by
  have h0 : 0 < valuation k ((ϖ ^ n : kˣ) : k) := zero_lt_iff.2 (by simp)
  have hZ : setCols P 0 (U - V) ∈ matLat A ((ϖ ^ n) • stdLat k C) := by
    rw [mem_matLat]
    intro i
    rw [mem_smul_lat, mem_stdLat]
    intro j
    by_cases hj : j ∈ P
    · have h1 := h i ⟨j, hj⟩
      simp only [cball, Set.mem_setOf_eq] at h1
      simp only [Pi.smul_apply, Matrix.row, setCols, of_apply, dif_pos hj, Matrix.sub_apply, Units.smul_def,
        smul_eq_mul]
      rw [Valuation.mem_integer_iff, map_mul, Units.val_inv_eq_inv_val, map_inv₀, inv_mul_le_iff₀ h0, mul_one]
      exact h1
    · simp [Matrix.row, setCols, hj]
  have := hΦ.2 (setCols P Y V) _ hZ
  rw [← this]
  congr 1
  ext i j
  by_cases hj : j ∈ P <;> simp [setCols, hj]

theorem psi_pairCols_eq {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ϖ : kˣ} {n : ℕ} (P : Finset C)
    {Y : Matrix A C k} (hY : ∀ i, ∀ j ∈ P, ((ϖ ^ n : kˣ) : k) * Y i j ∈ 𝒪[k]) {U V : Matrix A P k}
    (h : ∀ i j, U i j - V i j ∈ cball (ϖ ^ n)) : ψ (pairCols P Y U) = ψ (pairCols P Y V) := by
  have h1 : pairCols P Y U = pairCols P Y V + pairCols P Y (U - V) := by
    simp only [pairCols, ← Finset.sum_add_distrib, Matrix.sub_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h1, AddChar.map_add_eq_mul, hψ.eq_one (y := pairCols P Y (U - V)) ?_, mul_one]
  show valuation k _ ≤ valuation k ((1 : kˣ) : k)
  rw [Units.val_one, map_one]
  refine Valuation.map_sum_le _ fun i _ => Valuation.map_sum_le _ fun j _ => ?_
  have h2 := h i j
  have h3 := hY i j j.2
  rw [cball, Set.mem_setOf_eq] at h2
  rw [Valuation.mem_integer_iff, map_mul] at h3
  rw [map_mul, Matrix.sub_apply]
  exact (mul_le_mul' h2 le_rfl).trans (by rw [mul_comm] at h3 ⊢; exact h3)

end Lemmas

theorem fourierInt_eq_fourierSum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (A C : Type) [Fintype A] [DecidableEq A]
    [DecidableEq C] (ψ : AddChar k Circle) (m : Measure k) (ϖ : kˣ), IsUnif ϖ → HasConductor ψ 1 → IsUnitVol m →
    ∀ (P : Finset C) (n : ℕ) (Φ : Matrix A C k → ℂ), IsNatDatum ϖ n Φ →
      fourierInt ψ m P Φ = fourierSum ψ ϖ n P Φ := by
  intro k _ _ _ _ _ _ A C _ _ _ ψ m ϖ hϖ hψ hm P n Φ hΦ
  haveI := secondCountable k
  haveI := t2Space k
  haveI := hm.1
  have h0 : 0 < valuation k ((ϖ ^ n : kˣ) : k) := zero_lt_iff.2 (by simp)
  funext Y
  rw [fourierSum_apply]
  split_ifs with hY
  · rw [fourierInt]
    set F : Matrix A P k → ℂ := fun U => Φ (setCols P Y U) * (ψ (pairCols P Y U) : ℂ) with hF
    let S : (A → P → Res k n) → Set (Matrix A P k) := fun T =>
      Set.univ.pi fun i => Set.univ.pi fun j => (fun x => x + -liftRes T i j) ⁻¹' cball (ϖ ^ n)
    have hmemS : ∀ T U, U ∈ S T ↔ ∀ i j, U i j - liftRes T i j ∈ cball (ϖ ^ n) := by
      intro T U
      exact ⟨fun h i j => by simpa [sub_eq_add_neg] using h i trivial j trivial,
        fun h i _ j _ => by simpa [sub_eq_add_neg] using h i j⟩
    have hS : ∀ T, MeasurableSet (S T) := fun T =>
      MeasurableSet.univ_pi fun i => MeasurableSet.univ_pi fun j =>
        (isOpen_cball _).measurableSet.preimage (measurable_add_const _)
    have hcb : m (cball (ϖ ^ n)) = (distribHaarChar k (ϖ ^ n) : ENNReal) := by
      rw [measure_cball, hm.2, mul_one]
    have hvolE : ∀ T, (volM m A P) (S T) = (distribHaarChar k (ϖ ^ n) : ENNReal) ^ (Fintype.card A * P.card) := by
      intro T
      simp only [volM, S]
      refine (Measure.pi_pi (fun _ : A => Measure.pi fun _ : P => m)
        (fun i => Set.univ.pi fun j => (fun x => x + -liftRes T i j) ⁻¹' cball (ϖ ^ n))).trans ?_
      simp only [Measure.pi_pi, measure_preimage_add_right, hcb, Finset.prod_const, Finset.card_univ,
        Fintype.card_coe, ← pow_mul]
      rw [mul_comm]
    have hnabs : nabs k (ϖ ^ n) = ((resCard k : ℝ) ^ n)⁻¹ := by
      have h1 : ∀ l : ℕ, nabs k (ϖ ^ l) = nabs k ϖ ^ l := by
        intro l; induction l with
        | zero => simp [nabs_one]
        | succ l ih => rw [pow_succ, nabs_mul, ih, pow_succ]
      rw [h1, nabs_uniformiser hϖ.irreducible (x := ϖ) rfl, inv_pow]
    have hvol : ∀ T, (volM m A P).real (S T) = ((resCard k : ℝ) ^ (n * Fintype.card A * P.card))⁻¹ := by
      intro T
      rw [Measure.real, hvolE, ENNReal.toReal_pow, ENNReal.coe_toReal]
      have : ((distribHaarChar k (ϖ ^ n) : NNReal) : ℝ) = nabs k (ϖ ^ n) := rfl
      rw [this, hnabs, inv_pow, ← pow_mul, mul_assoc]
    have hfin : ∀ T, (volM m A P) (S T) ≠ ⊤ := fun T => by
      rw [hvolE]; exact ENNReal.pow_ne_top ENNReal.coe_ne_top
    have hpt : ∀ U, F U = ∑ T, (S T).indicator (fun _ => F (liftRes T)) U := by
      intro U
      by_cases hU : ∀ i j, U i j ∈ 𝒪[k]
      · let T0 : A → P → Res k n := fun i j => Ideal.Quotient.mk _ ⟨U i j, hU i j⟩
        have key1 : ∀ T i j, U i j - liftRes T i j ∈ cball (ϖ ^ n) ↔ T i j = T0 i j := by
          intro T i j
          have e : T i j = T0 i j ↔ (⟨U i j, hU i j⟩ - Quotient.out (T i j) : 𝒪[k]) ∈
              IsLocalRing.maximalIdeal 𝒪[k] ^ n := by
            conv_lhs => rw [← Ideal.Quotient.mk_out (T i j)]
            rw [eq_comm]
            exact Ideal.Quotient.eq
          rw [e, mem_maxIdeal_pow_iff hϖ]
          rfl
        have key : ∀ T, U ∈ S T ↔ T = T0 := by
          intro T
          rw [hmemS]
          simp only [key1]
          exact ⟨fun h => funext fun i => funext fun j => h i j, fun h i j => by rw [h]⟩
        rw [Finset.sum_eq_single T0 (fun T _ hT => Set.indicator_of_notMem (fun h => hT ((key T).1 h)) _)
          (by simp), Set.indicator_of_mem ((key T0).2 rfl)]
        have hd := (hmemS T0 U).1 ((key T0).2 rfl)
        simp only [hF]
        rw [natDatum_setCols_eq hΦ P Y hd, psi_pairCols_eq hψ P hY hd]
      · push_neg at hU
        obtain ⟨i, j, hij⟩ := hU
        have hz : F U = 0 := by
          simp only [hF]
          rw [hΦ.1 _ ?_, zero_mul]
          intro hm'
          apply hij
          have := mem_matLat_stdLat.1 hm' i j
          simpa [setCols, j.2] using this
        rw [hz]
        symm
        refine Finset.sum_eq_zero fun T _ => Set.indicator_of_notMem (fun h => hij ?_) _
        have h1 : valuation k (U i j - liftRes T i j) ≤ valuation k ((ϖ ^ n : kˣ) : k) := (hmemS T U).1 h i j
        have h2 : U i j - liftRes T i j ∈ 𝒪[k] := by
          rw [Valuation.mem_integer_iff]
          refine le_trans h1 ?_
          rw [Units.val_pow_eq_pow_val, map_pow]
          exact pow_le_one' (hϖ.mem) n
        simpa using add_mem h2 (liftRes_mem T i j)
    rw [show F = fun U => ∑ T, (S T).indicator (fun _ => F (liftRes T)) U from funext hpt]
    rw [integral_finset_sum _ (fun T _ => (integrable_indicator_iff (hS T)).2
      (integrableOn_const (lt_top_iff_ne_top.2 (hfin T)).ne)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [integral_indicator_const _ (hS T), hvol, Complex.real_smul]
    push_cast
    rfl
  · rw [fourierInt_eq_pi]
    refine GlobalTheory.SplitWeil.FourierPi.fourier_eq_zero_pi _ hψ (s := ϖ ^ n) (fun t ht x => ?_) ?_
    · exact natDatum_setCols_eq hΦ P Y fun i j => by simpa using ht ⟨i, j⟩ trivial
    · intro hmem
      apply hY
      intro i j hj
      have h1 : valuation k (Y i j) ≤ valuation k ((((1 : kˣ) * (ϖ ^ n)⁻¹ : kˣ)) : k) := hmem ⟨i, ⟨j, hj⟩⟩ trivial
      rw [one_mul, Units.val_inv_eq_inv_val, map_inv₀] at h1
      rw [Valuation.mem_integer_iff, map_mul]
      calc valuation k ((ϖ ^ n : kˣ) : k) * valuation k (Y i j)
          ≤ valuation k ((ϖ ^ n : kˣ) : k) * (valuation k ((ϖ ^ n : kˣ) : k))⁻¹ := mul_le_mul' le_rfl h1
        _ = 1 := mul_inv_cancel₀ h0.ne'

end GlobalTheory.ColFourier
