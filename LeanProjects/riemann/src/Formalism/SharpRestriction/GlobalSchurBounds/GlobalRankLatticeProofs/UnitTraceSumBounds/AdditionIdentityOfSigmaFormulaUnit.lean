import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.OkpUnitsDense
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormula
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtEndIntWHolds
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.StmtTransInvHolds

namespace Formalism.MainNotions.Ext.CutA

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.MainNotions.Ext NumberField

section
variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

private lemma lamC_hom_lemma (x : D.host.K) :
    lamC lam (D.host.φ₀ (x : D.host.E)) = lam ⟨D.host.φ₀ (x : D.host.E), test_vector_mem_schwartz_bruhat D x⟩ := by
  unfold lamC
  rw [dif_pos (test_vector_mem_schwartz_bruhat D x)]

theorem lamPhi_int (n : ℤ) : lamC lam (D.host.φ₀ (n : D.host.E)) = (n : ℂ_[p]) := by
  have h : (((n : D.host.K)) : D.host.E) = (n : D.host.E) := by push_cast; rfl
  rw [← h, lamC_hom_lemma]
  convert map_intCast lam n
  simp

theorem tauK_add (a b : D.host.K) : tauK D lam (a + b) = tauK D lam a + tauK D lam b := by
  unfold tauK
  rw [lamC_hom_lemma, lamC_hom_lemma, lamC_hom_lemma, ← map_add]
  congr 1
  ext
  simp

theorem tauK_mul (a b : D.host.K) : tauK D lam (a * b) = tauK D lam a * tauK D lam b := by
  unfold tauK
  rw [lamC_hom_lemma, lamC_hom_lemma, lamC_hom_lemma, ← map_mul]
  congr 1
  ext
  simp

private lemma lamC_hom_lemma_2 (z : D.host.E) :
    lamC lam (D.host.φ₀ z) = lam ⟨D.host.φ₀ z, test_vector_mem_schwartz_bruhat D z⟩ := by
  unfold lamC
  rw [dif_pos (test_vector_mem_schwartz_bruhat D z)]

theorem tauKc_add (a b : D.host.K) : tauKc D lam (a + b) = tauKc D lam a + tauKc D lam b := by
  unfold tauKc
  rw [lamC_hom_lemma_2, lamC_hom_lemma_2, lamC_hom_lemma_2, ← map_add]
  congr 1
  ext
  simp

theorem tauKc_mul (a b : D.host.K) : tauKc D lam (a * b) = tauKc D lam a * tauKc D lam b := by
  unfold tauKc
  rw [lamC_hom_lemma_2, lamC_hom_lemma_2, lamC_hom_lemma_2, ← map_mul]
  congr 1
  ext
  simp

theorem tauK_one : tauK D lam 1 = 1 := by
  unfold tauK
  rw [lamC_hom_lemma]
  convert map_one lam
  simp

theorem tauKc_one : tauKc D lam 1 = 1 := by
  unfold tauKc
  rw [lamC_hom_lemma_2]
  convert map_one lam
  simp

theorem tau_norm (a : 𝓞 D.host.K) :
    tauK D lam (a : D.host.K) * tauKc D lam (a : D.host.K) = ((Algebra.norm ℤ a : ℤ) : ℂ_[p]) := by
  have h := Formalism.MainNotions.UnusedSlot33.HK.norm_int D.host a
  rw [Algebra.intNorm_eq_norm] at h
  unfold tauK tauKc
  rw [← lamPhi_mul, ← h, lamPhi_int]

theorem tau_trace (a : 𝓞 D.host.K) :
    tauK D lam (a : D.host.K) + tauKc D lam (a : D.host.K) =
      ((Algebra.norm ℤ (1 + a) - Algebra.norm ℤ a - 1 : ℤ) : ℂ_[p]) := by
  have h1 := tau_norm D lam (1 + a)
  have h2 := tau_norm D lam a
  have e : ((1 + a : 𝓞 D.host.K) : D.host.K) = 1 + (a : D.host.K) := by push_cast; ring
  rw [e, tauK_add, tauKc_add, tauK_one, tauKc_one] at h1
  push_cast
  linear_combination h1 - h2

theorem zc_int (n : ℤ) : zc ((n : ℤ_[p])) = (n : ℂ_[p]) := by
  unfold zc
  rw [PadicInt.coe_intCast, map_intCast]

theorem zc_continuous : Continuous (zc : ℤ_[p] → ℂ_[p]) := by
  unfold zc
  exact (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val

theorem isClosed_range_zc : IsClosed (Set.range (zc : ℤ_[p] → ℂ_[p])) :=
  (isCompact_range zc_continuous).isClosed

theorem okpTrace_holds : OkpTrace D := by
  intro q _ l α hα
  unfold OKp at hα
  have hs : Set.range (fun a : 𝓞 D.host.K => (tauK D l (a : D.host.K), tauKc D l (a : D.host.K))) ⊆
      (fun β : ℂ_[q] × ℂ_[q] => β.1 + β.2) ⁻¹' Set.range (zc : ℤ_[q] → ℂ_[q]) := by
    rintro _ ⟨a, rfl⟩
    exact ⟨_, (zc_int _).trans (tau_trace D l a).symm⟩
  obtain ⟨n, hn⟩ := closure_minimal hs (isClosed_range_zc.preimage (continuous_fst.add continuous_snd)) hα
  exact ⟨n, hn.symm⟩

theorem okpNorm_holds : OkpNorm D := by
  intro q _ l α hα
  unfold OKp at hα
  have hs : Set.range (fun a : 𝓞 D.host.K => (tauK D l (a : D.host.K), tauKc D l (a : D.host.K))) ⊆
      (fun β : ℂ_[q] × ℂ_[q] => β.1 * β.2) ⁻¹' Set.range (zc : ℤ_[q] → ℂ_[q]) := by
    rintro _ ⟨a, rfl⟩
    exact ⟨_, (zc_int _).trans (tau_norm D l a).symm⟩
  obtain ⟨n, hn⟩ := closure_minimal hs (isClosed_range_zc.preimage (continuous_fst.mul continuous_snd)) hα
  exact ⟨n, hn.symm⟩

end

section
variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem norm_zc (z : ℤ_[p]) : ‖zc z‖ = ‖z‖ := by
  unfold zc
  rw [norm_algebraMap', PadicInt.norm_def]

theorem norm_int_cp (n : ℤ) : ‖(n : ℂ_[p])‖ = ‖(n : ℤ_[p])‖ := by
  rw [← zc_int, norm_zc]

theorem norm_int_cp_le (n : ℤ) : ‖(n : ℂ_[p])‖ ≤ 1 := by
  rw [norm_int_cp]
  exact PadicInt.norm_le_one _

theorem norm_int_cp_eq_one (n : ℤ) (h : ¬ (p : ℤ) ∣ n) : ‖(n : ℂ_[p])‖ = 1 := by
  rw [norm_int_cp]
  exact le_antisymm (PadicInt.norm_le_one _)
    (not_lt.mp fun h' => h ((PadicInt.norm_int_lt_one_iff_dvd n).mp h'))

theorem norm_int_cp_lt_one (n : ℤ) (h : (p : ℤ) ∣ n) : ‖(n : ℂ_[p])‖ < 1 := by
  rw [norm_int_cp]
  exact (PadicInt.norm_int_lt_one_iff_dvd n).mpr h

theorem not_dvd_two (hp : p ≠ 2) : ¬ (p : ℤ) ∣ 2 := by
  intro h
  have h2 : p ∣ 2 := by exact_mod_cast h
  exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h2)

theorem norm_two_cp (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h := norm_int_cp_eq_one (p := p) 2 (not_dvd_two hp)
  exact_mod_cast h

theorem norm_two_zp (hp : p ≠ 2) : ‖(2 : ℤ_[p])‖ = 1 := by
  have h := norm_int_cp_eq_one (p := p) 2 (not_dvd_two hp)
  rw [norm_int_cp] at h
  exact_mod_cast h

theorem norm_le_one_of_quad (x : ℂ_[p]) (t n : ℤ) (h : x ^ 2 = t * x - n) : ‖x‖ ≤ 1 := by
  by_contra hx
  push_neg at hx
  have h1 : ‖(t : ℂ_[p]) * x‖ ≤ ‖x‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (norm_int_cp_le t)
  have h2 : ‖(n : ℂ_[p])‖ ≤ ‖x‖ := (norm_int_cp_le n).trans hx.le
  have h3 : ‖x‖ ^ 2 ≤ ‖x‖ := by
    rw [← norm_pow, h]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 ?_)
    rw [norm_neg]
    exact h2
  nlinarith

theorem okp_norm_le (α : ℂ_[p] × ℂ_[p]) (hα : α ∈ OKp D lam) : ‖α.1‖ ≤ 1 ∧ ‖α.2‖ ≤ 1 := by
  unfold OKp at hα
  have hs : Set.range (fun a : 𝓞 D.host.K => (tauK D lam (a : D.host.K), tauKc D lam (a : D.host.K))) ⊆
      {β : ℂ_[p] × ℂ_[p] | ‖β.1‖ ≤ 1 ∧ ‖β.2‖ ≤ 1} := by
    rintro _ ⟨a, rfl⟩
    have hT := tau_trace D lam a
    have hN := tau_norm D lam a
    constructor
    · exact norm_le_one_of_quad _ (Algebra.norm ℤ (1 + a) - Algebra.norm ℤ a - 1) (Algebra.norm ℤ a)
        (by rw [← hT, ← hN]; ring)
    · exact norm_le_one_of_quad _ (Algebra.norm ℤ (1 + a) - Algebra.norm ℤ a - 1) (Algebra.norm ℤ a)
        (by rw [← hT, ← hN]; ring)
  have hc : IsClosed {β : ℂ_[p] × ℂ_[p] | ‖β.1‖ ≤ 1 ∧ ‖β.2‖ ≤ 1} :=
    (isClosed_le (continuous_norm.comp continuous_fst) continuous_const).inter
      (isClosed_le (continuous_norm.comp continuous_snd) continuous_const)
  exact closure_minimal hs hc hα

theorem okp_one : ((1 : ℂ_[p]), (1 : ℂ_[p])) ∈ OKp D lam := by
  unfold OKp
  refine subset_closure ⟨1, ?_⟩
  ext <;> simp [tauK_one, tauKc_one]

private lemma tauK_neg_lemma_3 (a : D.host.K) : tauK D lam (-a) = -tauK D lam a := by
  unfold tauK
  rw [lamC_hom_lemma, lamC_hom_lemma, ← map_neg]
  congr 1
  ext
  simp

private lemma tauKc_neg_lemma_4 (a : D.host.K) : tauKc D lam (-a) = -tauKc D lam a := by
  unfold tauKc
  rw [lamC_hom_lemma_2, lamC_hom_lemma_2, ← map_neg]
  congr 1
  ext
  simp

theorem okp_neg' (α : ℂ_[p] × ℂ_[p]) (hα : α ∈ OKp D lam) : -α ∈ OKp D lam := by
  unfold OKp at hα ⊢
  have hs : Set.range (fun a : 𝓞 D.host.K => (tauK D lam (a : D.host.K), tauKc D lam (a : D.host.K))) ⊆
      (fun β : ℂ_[p] × ℂ_[p] => -β) ⁻¹'
        closure (Set.range (fun a : 𝓞 D.host.K => (tauK D lam (a : D.host.K), tauKc D lam (a : D.host.K)))) := by
    rintro _ ⟨a, rfl⟩
    refine subset_closure ⟨-a, ?_⟩
    ext <;> simp [tauK_neg_lemma_3, tauKc_neg_lemma_4]
  exact closure_minimal hs (isClosed_closure.preimage continuous_neg) hα

private lemma sub_le_lemma (x c : ℂ_[p]) (hx : ‖x‖ ≤ 1) (hc : ‖c‖ = 1) : ‖x - c‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx ?_)
  rw [norm_neg, hc]

private lemma sub_unit_lemma_2 (x c : ℂ_[p]) (hx : ‖x‖ < 1) (hc : ‖c‖ = 1) : ‖x - c‖ = 1 := by
  refine le_antisymm (sub_le_lemma x c hx.le hc) (not_lt.mp fun hlt => ?_)
  have h : ‖c‖ ≤ max ‖x‖ ‖-(x - c)‖ := by
    have e : c = x + -(x - c) := by ring
    conv_lhs => rw [e]
    exact IsUltrametricDist.norm_add_le_max _ _
  rw [norm_neg, hc] at h
  exact absurd h (not_le.mpr (max_lt hx hlt))

theorem pick_c (hp : p ≠ 2) (x y : ℂ_[p]) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (hxy : ¬ (‖x‖ = 1 ∧ ‖y‖ = 1)) :
    ∃ c : ℂ_[p], (c = 1 ∨ c = -1) ∧ ‖x - c‖ = 1 ∧ ‖y - c‖ = 1 := by
  have hn1 : ‖(1 : ℂ_[p])‖ = 1 := norm_one
  have hnm1 : ‖(-1 : ℂ_[p])‖ = 1 := by rw [norm_neg, norm_one]
  have hboth : ∀ z : ℂ_[p], ‖z‖ ≤ 1 → ‖z - 1‖ = 1 ∨ ‖z - (-1)‖ = 1 := by
    intro z hz
    by_contra hc
    push_neg at hc
    have h1 : ‖z - 1‖ < 1 := lt_of_le_of_ne (sub_le_lemma z 1 hz hn1) hc.1
    have h2 : ‖z - (-1)‖ < 1 := lt_of_le_of_ne (sub_le_lemma z (-1) hz hnm1) hc.2
    have h3 : ‖(2 : ℂ_[p])‖ ≤ max ‖z - (-1)‖ ‖-(z - 1)‖ := by
      have e : (2 : ℂ_[p]) = (z - (-1)) + -(z - 1) := by ring
      conv_lhs => rw [e]
      exact IsUltrametricDist.norm_add_le_max _ _
    rw [norm_neg, norm_two_cp hp] at h3
    exact absurd h3 (not_le.mpr (max_lt h2 h1))
  have hxy' : ‖x‖ < 1 ∨ ‖y‖ < 1 := by
    by_contra hc
    push_neg at hc
    exact hxy ⟨le_antisymm hx hc.1, le_antisymm hy hc.2⟩
  rcases hxy' with hx1 | hy1
  · rcases hboth y hy with h | h
    · exact ⟨1, Or.inl rfl, sub_unit_lemma_2 x 1 hx1 hn1, h⟩
    · exact ⟨-1, Or.inr rfl, sub_unit_lemma_2 x (-1) hx1 hnm1, h⟩
  · rcases hboth x hx with h | h
    · exact ⟨1, Or.inl rfl, h, sub_unit_lemma_2 y 1 hy1 hn1⟩
    · exact ⟨-1, Or.inr rfl, h, sub_unit_lemma_2 y (-1) hy1 hnm1⟩

theorem okpTwoUnits2_holds : OkpTwoUnits2 D := by
  intro p _ lam hp α hα
  obtain ⟨hx, hy⟩ := okp_norm_le D lam α hα
  have h2 := norm_two_cp hp
  by_cases hu : ‖α.1‖ = 1 ∧ ‖α.2‖ = 1
  · refine ⟨α + α, okp_add D lam _ _ hα hα, -α, okp_neg' D lam _ hα, ?_, ?_, ?_, ?_, by ring⟩
    · rw [Prod.fst_add, ← two_mul, norm_mul, h2, hu.1, one_mul]
    · rw [Prod.snd_add, ← two_mul, norm_mul, h2, hu.2, one_mul]
    · rw [Prod.fst_neg, norm_neg, hu.1]
    · rw [Prod.snd_neg, norm_neg, hu.2]
  · obtain ⟨c, hc, h1, h2'⟩ := pick_c hp α.1 α.2 hx hy hu
    have hcm : ((c : ℂ_[p]), c) ∈ OKp D lam := by
      rcases hc with rfl | rfl
      · exact okp_one D lam
      · exact okpNeg_holds D p lam
    have hnc : ‖c‖ = 1 := by rcases hc with rfl | rfl <;> simp
    refine ⟨(c, c), hcm, α - (c, c), ?_, hnc, hnc, h1, h2', by ring⟩
    rw [sub_eq_add_neg]
    exact okp_add D lam _ _ hα (okp_neg' D lam _ hcm)

theorem okpTwoUnits_holds : OkpTwoUnits D := by
  intro p _ lam hp α hα
  obtain ⟨β, hβ, γ, hγ, h1, -, h3, -, h⟩ := okpTwoUnits2_holds D p lam hp α hα
  exact ⟨β, hβ, γ, hγ, h1, h3, h⟩

theorem okpUnitsDense_holds : OkpUnitsDense D := by
  intro p _ lam hp α hα h1 h2
  have hU : IsOpen {x : ℂ_[p] × ℂ_[p] | ‖x.1‖ = 1 ∧ ‖x.2‖ = 1} := by
    have hs : IsOpen {z : ℂ_[p] | ‖z‖ = 1} := by
      have := IsUltrametricDist.isOpen_sphere (0 : ℂ_[p]) (one_ne_zero (α := ℝ))
      simpa [Metric.sphere, dist_zero_right] using this
    exact (hs.preimage continuous_fst).inter (hs.preimage continuous_snd)
  have h := hU.inter_closure ⟨⟨h1, h2⟩, hα⟩
  refine closure_mono ?_ h
  rintro _ ⟨⟨n1, n2⟩, ⟨a, rfl⟩⟩
  refine ⟨a, ?_, rfl⟩
  have hn := tau_norm D lam a
  have h3 : ‖((Algebra.norm ℤ a : ℤ) : ℂ_[p])‖ = 1 := by
    rw [← hn, norm_mul]; simp only at n1 n2; rw [n1, n2, one_mul]
  have h4 : ¬ (p : ℤ) ∣ Algebra.norm ℤ a := by
    intro hd
    have := norm_int_cp_lt_one (p := p) _ hd
    linarith
  have h5 : ¬ p ∣ (Algebra.norm ℤ a).natAbs := fun hd => h4 (Int.natCast_dvd.2 hd)
  exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 h5)

end

section
variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem zc_neg (z : ℤ_[p]) : zc (-z) = - zc z := by
  unfold zc
  rw [PadicInt.coe_neg, map_neg]

theorem zc_pow (z : ℤ_[p]) (n : ℕ) : zc (z ^ n) = zc z ^ n := by
  unfold zc
  rw [PadicInt.coe_pow, map_pow]

theorem norm_int_zp_eq_one (n : ℤ) (h : ¬ (p : ℤ) ∣ n) : ‖(n : ℤ_[p])‖ = 1 := by
  rw [← norm_int_cp]
  exact norm_int_cp_eq_one n h

theorem sqrtMinusD_sq : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := by
  apply D.host.φ₀.injective
  have h1 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  rw [map_pow, h1, map_neg, map_natCast, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]
  push_cast; ring

noncomputable def sK : 𝓞 D.host.K :=
  ⟨⟨D.host.sqrtMinusD, Formalism.MainNotions.UnusedSlot33.HK.bE_mem D.host⟩, by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (D.host.d : ℤ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
    have h : (⟨D.host.sqrtMinusD, Formalism.MainNotions.UnusedSlot33.HK.bE_mem D.host⟩ : D.host.K) ^ 2 = -(D.host.d : D.host.K) :=
      Subtype.ext (by push_cast; exact sqrtMinusD_sq D)
    simp [h]⟩

theorem tauKc_sK : tauKc D lam (sK D : D.host.K) = - tauK D lam (sK D : D.host.K) := by
  have h0 : tauK D lam ((sK D : D.host.K) + (-(sK D : D.host.K))) = 0 := by
    rw [add_neg_cancel]
    have := lamPhi_int D lam 0
    unfold tauK; simpa using this
  rw [tauK_add] at h0
  have e : tauKc D lam (sK D : D.host.K) = tauK D lam (-(sK D : D.host.K)) := by
    unfold tauKc tauK
    congr 2
    show D.host.conj D.host.sqrtMinusD = -D.host.sqrtMinusD
    exact Formalism.MainNotions.UnusedSlot33.HK.conj_b D.host
  rw [e]; linear_combination h0

private lemma tauK_int_lemma_5 (n : ℤ) : tauK D lam (n : D.host.K) = (n : ℂ_[p]) := by
  unfold tauK
  have h : (((n : D.host.K)) : D.host.E) = (n : D.host.E) := by push_cast; rfl
  rw [h]
  exact lamPhi_int D lam n

theorem tauK_sK_sq : tauK D lam (sK D : D.host.K) ^ 2 = -((D.host.d : ℤ) : ℂ_[p]) := by
  have h0 : (⟨D.host.sqrtMinusD, Formalism.MainNotions.UnusedSlot33.HK.bE_mem D.host⟩ : D.host.K) ^ 2 = -(D.host.d : D.host.K) :=
    Subtype.ext (by push_cast; exact sqrtMinusD_sq D)
  have h1 : ((sK D : D.host.K)) ^ 2 = ((-(D.host.d : ℤ) : ℤ) : D.host.K) := by
    rw [show ((sK D : D.host.K)) = ⟨D.host.sqrtMinusD, Formalism.MainNotions.UnusedSlot33.HK.bE_mem D.host⟩ from rfl, h0]
    first | (push_cast; done) | (push_cast; ring) | (push_cast; rfl) | simp
  rw [sq, ← tauK_mul, ← sq, h1, tauK_int_lemma_5]
  first | (push_cast; done) | (push_cast; ring) | (push_cast; rfl) | simp

theorem norm_tauK_sK_sq : ‖tauK D lam (sK D : D.host.K)‖ ^ 2 = ‖((D.host.d : ℤ) : ℤ_[p])‖ := by
  rw [← norm_pow, tauK_sK_sq, norm_neg, norm_int_cp]

theorem okpDiff_holds : OkpDiff D := by
  intro p _ lam hp
  refine ⟨_, subset_closure ⟨sK D, rfl⟩, ?_⟩
  simp only
  rw [tauKc_sK, sub_neg_eq_add, ← two_mul, norm_mul, norm_two_cp hp, one_mul]
  have t0 : 0 ≤ ‖tauK D lam (sK D : D.host.K)‖ := norm_nonneg _
  have hsq := norm_tauK_sK_sq D lam
  have hd : D.host.d.Prime := D.host.hyp.2.1
  split_ifs with h
  · have e : ‖((D.host.d : ℤ) : ℤ_[p])‖ = (p : ℝ)⁻¹ := by
      rw [← h]; simp
    rw [e] at hsq
    rw [← Real.sqrt_sq t0, hsq, Real.sqrt_inv, Real.sqrt_eq_rpow]
  · have hnd : ¬ (p : ℤ) ∣ (D.host.d : ℤ) := by
      intro hdv
      have : p ∣ D.host.d := by exact_mod_cast hdv
      exact h ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hd).1 this)
    rw [norm_int_zp_eq_one _ hnd] at hsq
    rw [← Real.sqrt_sq t0, hsq, Real.sqrt_one]

theorem okpSplit_holds : OkpSplit D := by
  intro p _ lam hp hs
  unfold SplitK at hs
  have hpp : p.Prime := Fact.out
  have hnd : ¬ (p : ℤ) ∣ (D.host.d : ℤ) := by
    intro hdv
    have h0 : ((-(D.host.d : ℤ) : ℤ) : ZMod p) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact (dvd_neg).2 hdv
    have h1 := (legendreSym.eq_zero_iff p (-(D.host.d : ℤ))).2 h0
    rw [jacobiSym.legendreSym.to_jacobiSym] at h1
    rw [h1] at hs
    exact absurd hs (by decide)
  obtain ⟨r, hr⟩ := ZMod.isSquare_of_jacobiSym_eq_one hs
  push_cast at hr
  set x : ℤ := (r.val : ℤ) with hxdef
  have ex : ((x : ℤ) : ZMod p) = r := by simp [hxdef]
  have hx : (p : ℤ) ∣ x * x + D.host.d := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ex]
    linear_combination -hr
  have hnx : ¬ (p : ℤ) ∣ x := by
    intro h
    apply hnd
    have := dvd_sub hx (dvd_mul_of_dvd_left h x)
    simpa using this
  have h2x : ¬ (p : ℤ) ∣ 2 * x := by
    intro h
    rcases (Nat.prime_iff_prime_int.mp hpp).dvd_or_dvd h with h | h
    · exact not_dvd_two hp h
    · exact hnx h
  let F : Polynomial ℤ := Polynomial.X ^ 2 + Polynomial.C (D.host.d : ℤ)
  have hF : ∀ z : ℤ_[p], F.aeval z = z ^ 2 + (D.host.d : ℤ_[p]) := by intro z; simp [F]
  have hF' : ∀ z : ℤ_[p], (Polynomial.derivative F).aeval z = 2 * z := by
    intro z; simp [F]
    left; exact map_ofNat _ 2
  have hnorm : ‖F.aeval (x : ℤ_[p])‖ < ‖(Polynomial.derivative F).aeval (x : ℤ_[p])‖ ^ 2 := by
    rw [hF, hF']
    have e1 : (x : ℤ_[p]) ^ 2 + (D.host.d : ℤ_[p]) = ((x * x + D.host.d : ℤ) : ℤ_[p]) := by push_cast; ring
    have e2 : 2 * (x : ℤ_[p]) = ((2 * x : ℤ) : ℤ_[p]) := by push_cast; ring
    rw [e1, e2, norm_int_zp_eq_one _ h2x, one_pow]
    exact (PadicInt.norm_int_lt_one_iff_dvd _).2 hx
  obtain ⟨z, hz, -⟩ := hensels_lemma hnorm
  rw [hF] at hz
  have hz2 : z ^ 2 = -((D.host.d : ℤ) : ℤ_[p]) := by push_cast; linear_combination hz
  have hzn : ‖z‖ = 1 := by
    have h1 : ‖z‖ ^ 2 = 1 := by
      rw [← norm_pow, hz2, norm_neg, norm_int_zp_eq_one _ hnd]
    rw [← Real.sqrt_sq (norm_nonneg z), h1, Real.sqrt_one]
  have hzc : zc z ^ 2 = tauK D lam (sK D : D.host.K) ^ 2 := by
    rw [← zc_pow, hz2, tauK_sK_sq, zc_neg, zc_int]
  obtain ⟨s, hs1, hs2⟩ : ∃ s : ℤ_[p], tauK D lam (sK D : D.host.K) = zc s ∧ ‖s‖ = 1 := by
    have h0 : (tauK D lam (sK D : D.host.K) - zc z) * (tauK D lam (sK D : D.host.K) + zc z) = 0 := by
      linear_combination -hzc
    rcases mul_eq_zero.1 h0 with h | h
    · exact ⟨z, by linear_combination h, hzn⟩
    · exact ⟨-z, by rw [zc_neg]; linear_combination h, by rw [norm_neg, hzn]⟩
  refine ⟨_, subset_closure ⟨sK D, rfl⟩, s, -s, ?_, ?_⟩
  · simp only
    rw [tauKc_sK, hs1, zc_neg]
  · rw [PadicInt.isUnit_iff, sub_neg_eq_add, ← two_mul, norm_mul, norm_two_zp hp, hs2, one_mul]

end

section
variable {p : ℕ} [Fact p.Prime]

theorem lamC_one (lam : Qbar →+* ℂ_[p]) : lamC lam 1 = 1 := by
  unfold lamC
  simp
  exact map_one lam

theorem coeff_one_subst (f s : PowerSeries ℂ_[p]) (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.coeff 1 (PowerSeries.subst f s : PowerSeries ℂ_[p]) = PowerSeries.coeff 1 s * PowerSeries.coeff 1 f := by
  have ha : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf
  have key : ∀ t : PowerSeries ℂ_[p], (PowerSeries.subst f t : PowerSeries ℂ_[p]) =
      (PowerSeries.subst f (PowerSeries.mk fun n => PowerSeries.coeff (n + 1) t) : PowerSeries ℂ_[p]) * f +
        PowerSeries.C (PowerSeries.constantCoeff t) := by
    intro t
    conv_lhs => rw [PowerSeries.eq_shift_mul_X_add_const t]
    rw [PowerSeries.subst_add ha, PowerSeries.subst_mul ha, PowerSeries.subst_X ha, PowerSeries.subst_C]
    rfl
  have c0 : ∀ t : PowerSeries ℂ_[p], PowerSeries.constantCoeff (PowerSeries.subst f t : PowerSeries ℂ_[p]) =
      PowerSeries.constantCoeff t := by
    intro t
    rw [key t, map_add, map_mul, hf, mul_zero, zero_add, PowerSeries.constantCoeff_C]
  rw [key s, map_add, PowerSeries.coeff_C, if_neg one_ne_zero, add_zero, PowerSeries.coeff_mul,
    Finset.Nat.antidiagonal_succ]
  simp only [Finset.Nat.antidiagonal_zero, Finset.map_singleton, Finset.sum_cons, Finset.sum_singleton]
  simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hf, c0]

theorem ePhiOne_holds (D : D7) : EPhiOne D := by
  intro p _ cc δ g hA
  obtain ⟨hcI, -, hδ, hL, ok⟩ := hA
  have hsp := Formalism.MainNotions.Ext.sgStar_spec D cc hcI.1 δ hδ
  have hs1 : PowerSeries.coeff 1 (sgSer g.lam g.abelian₂) = 1 := by
    rw [hL]; unfold sgSer
    rw [PowerSeries.coeff_mk, iteratedDeriv_one, hsp.2.1]
    simpa using lamC_one g.lam
  have hw0 : PowerSeries.constantCoeff g.wq = 1 := by
    have h := ok.2.1
    unfold IsWq at h
    have h2 := congrArg PowerSeries.constantCoeff h
    simpa using h2
  have hom : PowerSeries.constantCoeff (omegaW (g.C • wModel g.lam g.abelian₂) g.wq) = 1 := by
    unfold omegaW
    simp [PowerSeries.constantCoeff_inv, hw0]
    rw [map_ofNat]
    exact mul_inv_cancel₀ two_ne_zero
  have hl0 : PowerSeries.constantCoeff (flog (g.C • wModel g.lam g.abelian₂) g.wq) = 0 := by
    unfold flog; rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]; simp
  have hl1 : PowerSeries.coeff 1 (flog (g.C • wModel g.lam g.abelian₂) g.wq) = 1 := by
    unfold flog; rw [PowerSeries.coeff_mk]; simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hom]
  set ep : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hep
  have hep0 : ep ≠ 0 := Units.ne_zero _
  have hf0 : PowerSeries.constantCoeff (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) ep * flog (g.C • wModel g.lam g.abelian₂) g.wq) = 0 := by
    rw [map_mul, hl0, mul_zero]
  have hf1 : PowerSeries.coeff 1 (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) ep * flog (g.C • wModel g.lam g.abelian₂) g.wq) = ep := by
    have e : algebraMap ℂ_[p] (PowerSeries ℂ_[p]) ep = PowerSeries.C ep := by
      rfl
    rw [e, PowerSeries.coeff_C_mul, hl1, mul_one]
  unfold ePhi1
  simp only []
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, zero_add, coeff_one_subst _ _ hf0,
    hs1, hf1, one_mul, inv_mul_cancel₀ hep0]

end

theorem phNorm_of' (H1 : PhNormOfUnits) (H2 : PhNormClosed) (D : D7) (hOK : PhNormOK D) (he : endInt D)
    (ha : addInt D) (hB : beBiadd D) : phNorm D :=
  phNorm_of H1 H2 D hOK (okpUnitsDense_holds D) (okpTwoUnits2_holds D) (okpTrace_holds D) (okpNorm_holds D) he ha hB

theorem beConj_of' (H : BeConjOfNorm) (D : D7) (he : endInt D) (ha : addInt D) (hn : phNorm D) (hB : beBiadd D) :
    beConj D :=
  beConj_of H D (okpNorm_holds D) (okpTwoUnits_holds D) he ha hn hB

theorem splitZero_of' (H : SplitZeroG) (D : D7) (he : endInt D) (ha : addInt D) (hn : phNorm D)
    (hb : beConj D) (hB : beBiadd D) : splitZero D :=
  splitZero_of H D (okpSplit_holds D) he ha hn hb hB

theorem beDiag_of' (H : BeDiagG) (D : D7) (he : endInt D) (ha : addInt D) (hn : phNorm D) (hb : beConj D)
    (hB : beBiadd D) : beDiag D :=
  beDiag_of H D (okpTrace_holds D) he ha hn hb hB

theorem jetsPh_of' (HH : JetsHigh) (H1 : JetsOne) (H2 : JetsTwo) (D : D7) (hc : cube D) (hn : phNorm D)
    (hb : beConj D) : jetsPh D :=
  jetsPh_of HH H1 H2 D hc hn hb (okpDiff_holds D)

theorem addition_identity_of_sigma_formula_unit (H31 : UnitTraceSumSecondBound) (HC : CubeIdentityFromAdditionFormula) (D : D7) (hQ : PAdicSigmaAdditionFormula D) (ha : addInt D) : cube2 D :=
  addition_identity_of_sigma_formula H31 HC D hQ (ePhiOne_holds D) ha

def LemmaThreeOneThird : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok → IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    ∃ n : MvPowerSeries (Fin 3) ℂ_[p], IntegralMv n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      (Xv 0) ^ 3 * PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) g.wq * (Xv 2 - Xv 1) +
          (Xv 1) ^ 3 * PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) g.wq * (Xv 0 - Xv 2) +
          (Xv 2) ^ 3 * PowerSeries.subst (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) g.wq * (Xv 1 - Xv 0) =
        g.add (g.add (Xv 0) (Xv 1)) (Xv 2) * g.sub (Xv 0) (Xv 1) * g.sub (Xv 1) (Xv 2) * g.sub (Xv 2) (Xv 0) * n

def Cube3OfDet : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), g.Ok →
    PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1 →
    ((Xv 0) ^ 3 * PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) g.wq * (Xv 2 - Xv 1) +
          (Xv 1) ^ 3 * PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) g.wq * (Xv 0 - Xv 2) +
          (Xv 2) ^ 3 * PowerSeries.subst (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) g.wq * (Xv 1 - Xv 0)) *
        PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) ^ 3 *
        PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) ^ 3 *
        PowerSeries.subst (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) ^ 3 =
      PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) g.wq *
        PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) g.wq *
        PowerSeries.subst (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) g.wq *
        (g.add (g.add (Xv 0) (Xv 1)) (Xv 2) *
          PowerSeries.subst (g.add (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq)) *
        (g.sub (Xv 0) (Xv 1) *
          PowerSeries.subst (g.sub (Xv 0) (Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq)) *
        (g.sub (Xv 1) (Xv 2) *
          PowerSeries.subst (g.sub (Xv 1) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq)) *
        (g.sub (Xv 2) (Xv 0) *
          PowerSeries.subst (g.sub (Xv 2) (Xv 0) : MvPowerSeries (Fin 3) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq)) →
    (∃ n : MvPowerSeries (Fin 3) ℂ_[p], IntegralMv n ∧ MvPowerSeries.constantCoeff n = 1 ∧
      (Xv 0) ^ 3 * PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) g.wq * (Xv 2 - Xv 1) +
          (Xv 1) ^ 3 * PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) g.wq * (Xv 0 - Xv 2) +
          (Xv 2) ^ 3 * PowerSeries.subst (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) g.wq * (Xv 1 - Xv 0) =
        g.add (g.add (Xv 0) (Xv 1)) (Xv 2) * g.sub (Xv 0) (Xv 1) * g.sub (Xv 1) (Xv 2) * g.sub (Xv 2) (Xv 0) * n) →
    Simeq (g.phAt (g.add (g.add (Xv 0) (Xv 1)) (Xv 2)) + g.phAt (g.sub (Xv 0) (Xv 1)) +
        g.phAt (g.sub (Xv 1) (Xv 2)) + g.phAt (g.sub (Xv 2) (Xv 0)) : MvPowerSeries (Fin 3) ℂ_[p])
      (3 * (g.phAt (Xv 0) + g.phAt (Xv 1) + g.phAt (Xv 2)))

def PAdicFrobeniusStickelberger (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    ((Xv 0) ^ 3 * PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) g.wq * (Xv 2 - Xv 1) +
          (Xv 1) ^ 3 * PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) g.wq * (Xv 0 - Xv 2) +
          (Xv 2) ^ 3 * PowerSeries.subst (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) g.wq * (Xv 1 - Xv 0)) *
        PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) ^ 3 *
        PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) ^ 3 *
        PowerSeries.subst (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq) ^ 3 =
      PowerSeries.subst (Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) g.wq *
        PowerSeries.subst (Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) g.wq *
        PowerSeries.subst (Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) g.wq *
        (g.add (g.add (Xv 0) (Xv 1)) (Xv 2) *
          PowerSeries.subst (g.add (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq)) *
        (g.sub (Xv 0) (Xv 1) *
          PowerSeries.subst (g.sub (Xv 0) (Xv 1) : MvPowerSeries (Fin 3) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq)) *
        (g.sub (Xv 1) (Xv 2) *
          PowerSeries.subst (g.sub (Xv 1) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq)) *
        (g.sub (Xv 2) (Xv 0) *
          PowerSeries.subst (g.sub (Xv 2) (Xv 0) : MvPowerSeries (Fin 3) ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq))

theorem cube_second_identity_of_determinant (H31 : LemmaThreeOneThird) (HC : Cube3OfDet) (D : D7) (hQ : PAdicFrobeniusStickelberger D) (ha : addInt D) : cube3 D := by
  intro q _ cc δ g hA
  have hok : g.Ok := hA.2.2.2.2
  exact HC q g hok (ePhiOne_holds D q cc δ g hA) (hQ q cc δ g hA) (H31 q g hok (ha q cc δ g hA).1)

theorem cube_of' (HE : CubeOfTwoIdentities) (H31 : UnitTraceSumSecondBound) (HC2 : CubeIdentityFromAdditionFormula) (H31' : LemmaThreeOneThird) (HC3 : Cube3OfDet) (D : D7)
    (hQ : PAdicSigmaAdditionFormula D) (hQd : PAdicFrobeniusStickelberger D) (ha : addInt D) : cube D :=
  cube_of HE D (addition_identity_of_sigma_formula_unit H31 HC2 D hQ ha) (cube_second_identity_of_determinant H31' HC3 D hQd ha)

end Formalism.MainNotions.Ext.CutA
