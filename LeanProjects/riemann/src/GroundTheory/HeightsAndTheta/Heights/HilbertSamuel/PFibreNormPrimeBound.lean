import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormPrimeBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullFormsGeneric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNormFormGaussBound
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartPrimePowerInverse
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem FibreNormPrimeBound.block_ne_zero {y : (Σ k, ι k) → Ω} {e : K → ℕ} {f : MRing ι}
    (he : ∀ k, 1 ≤ e k) (hf : IsMultiHomog f e) (hy : aeval y f ≠ 0) (k : K) : ∃ i, y ⟨k, i⟩ ≠ 0 := by
  by_contra h
  push Not at h
  apply hy
  rw [aeval_def, eval₂_eq']
  refine Finset.sum_eq_zero fun m hm => ?_
  have hsum : ∑ i, m ⟨k, i⟩ ≠ 0 := by rw [hf m hm k]; exact (Nat.one_le_iff_ne_zero.mp (he k))
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ⟨k, i⟩) ?_)
  rw [h i, zero_pow hi]

omit [Fintype K] in

theorem FibreNormPrimeBound.exists_chart (V : ValuationSubring Ω) {y : (Σ k, ι k) → Ω}
    (hblk : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) :
    ∃ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) ∧ ∀ q : Σ k, ι k, y q / y ⟨q.1, c q.1⟩ ∈ V := by
  classical
  have hmax : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 ∧ ∀ i', V.valuation (y ⟨k, i'⟩) ≤ V.valuation (y ⟨k, i⟩) := by
    intro k
    obtain ⟨i, hi, hm⟩ := Finset.exists_max_image (Finset.univ.filter fun i => y ⟨k, i⟩ ≠ 0)
      (fun i => V.valuation (y ⟨k, i⟩)) (by obtain ⟨i0, h0⟩ := hblk k; exact ⟨i0, by simp [h0]⟩)
    refine ⟨i, (Finset.mem_filter.mp hi).2, fun i' => ?_⟩
    by_cases h : y ⟨k, i'⟩ = 0
    · rw [h, map_zero]; exact zero_le
    · exact hm i' (by simp [h])
  choose c hc0 hcm using hmax
  refine ⟨c, hc0, fun ⟨k, i⟩ => ?_⟩
  have hv : V.valuation (y ⟨k, c k⟩) ≠ 0 := (Valuation.ne_zero_iff _).mpr (hc0 k)
  rw [← V.valuation_le_one_iff, div_eq_mul_inv, map_mul, map_inv₀]
  calc V.valuation (y ⟨k, i⟩) * (V.valuation (y ⟨k, c k⟩))⁻¹
      ≤ V.valuation (y ⟨k, c k⟩) * (V.valuation (y ⟨k, c k⟩))⁻¹ := mul_le_mul_left (hcm k i) _
    _ = 1 := mul_inv_cancel₀ hv

theorem FibreNormPrimeBound.mem_of_isIntegral (V : ValuationSubring Ω) {S : Subalgebra ℤ Ω} (hS : ∀ s ∈ S, s ∈ V)
    {u : Ω} (hu : IsIntegral S u) : u ∈ V := by
  let φ : S →+* V :=
    { toFun := fun r => ⟨r, hS r r.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl,
      map_add' := fun _ _ => rfl }
  obtain ⟨f, hf, hfu⟩ := hu
  have hint : IsIntegral V u := ⟨f.map φ, hf.map φ, by rw [Polynomial.eval₂_map]; exact hfu⟩
  obtain ⟨v, hv⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hint
  exact hv ▸ v.2

theorem FibreNormPrimeBound.proof (hG : PullFormsGeneric.Statement) (hN : NormFormGaussBound.Statement)
    (hC : ChartPrimePowerInverse.Statement) : FibreNormPrimeBound.Statement := by
  classical
  intro K _ ι _ Ω _ _ y D e L q hAr hBir he hhomL hnz p hp
  have hM : ∀ j, ∃ M : ℕ, aeval y (L j) ≠ 0 → ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      (p : Ω) ^ M * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j) ∈
        Subring.closure (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) ∪
          Set.range (fun i => aeval y (L i) / aeval y (L j)) ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹}) := by
    intro j
    by_cases hj : aeval y (L j) = 0
    · exact ⟨0, fun h => (h hj).elim⟩
    · obtain ⟨M, hM⟩ := hC K ι Ω y D e L hhomL hnz p hp j hj
      exact ⟨M, fun _ => hM⟩
  choose M hM using hM
  refine ⟨Module.finrank (pullField y L) Ω * (∑ j, M j) * q, ?_⟩
  intro τ s hs j c hc μ
  obtain ⟨hLj, hfd, -, hhom, hcp⟩ := hc
  have := hfd
  set S := ∑ j, M j with hS
  set Sset : Set Ω := {z | ∃ i k, z = aeval y (L i) / aeval y (L k)} ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹}
  have key : ∀ V : ValuationSubring Ω, Sset ⊆ V.toSubring →
      (p : Ω) ^ (S * (q * τ)) * (s / aeval y (L j) ^ (q * τ)) ∈ V := by
    intro V hSV
    obtain ⟨c, hc0, hcV⟩ :=
      FibreNormPrimeBound.exists_chart V (FibreNormPrimeBound.block_ne_zero he (hhomL j) hLj)
    set Z := ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * ((q * e k : ℕ) : ℤ))) with hZ
    set Y := ∏ k, y ⟨k, c k⟩ ^ e k with hY
    have hu : s * Z ∈ V := by
      refine FibreNormPrimeBound.mem_of_isIntegral V (S := chartRingZ y c) ?_ (hs c hc0)
      intro t ht
      rw [chartRingZ, Algebra.adjoin_int] at ht
      refine (Subring.closure_le (t := V.toSubring)).mpr ?_ ht
      rintro _ ⟨q', rfl⟩
      exact hcV q'
    have hw : (p : Ω) ^ M j * Y / aeval y (L j) ∈ V := by
      refine (Subring.closure_le (t := V.toSubring)).mpr ?_ (hM j hLj c hc0)
      rintro z ((⟨q', rfl⟩ | ⟨i, rfl⟩) | hz)
      · exact hcV q'
      · exact hSV (Or.inl ⟨i, j, rfl⟩)
      · exact hSV (Or.inr hz)
    have hpV : (p : Ω) ∈ V := natCast_mem V p
    obtain ⟨r, hr⟩ : ∃ r, S = M j + r :=
      ⟨S - M j, (Nat.add_sub_cancel' (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))).symm⟩
    have hZY : Z * Y ^ (q * τ) = 1 := by
      rw [hZ, hY, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one fun k _ => ?_
      rw [← pow_mul, ← zpow_natCast (y _) (e k * (q * τ)), ← zpow_add₀ (hc0 k)]
      have h0 : -((τ : ℤ) * ((q * e k : ℕ) : ℤ)) + ((e k * (q * τ) : ℕ) : ℤ) = 0 := by push_cast; ring
      rw [h0, zpow_zero]
    have heq : (p : Ω) ^ (S * (q * τ)) * (s / aeval y (L j) ^ (q * τ)) =
        (s * Z) * ((p : Ω) ^ r) ^ (q * τ) * ((p : Ω) ^ M j * Y / aeval y (L j)) ^ (q * τ) := by
      rw [hr]
      calc (p : Ω) ^ ((M j + r) * (q * τ)) * (s / aeval y (L j) ^ (q * τ))
          = s * (Z * Y ^ (q * τ)) * (p : Ω) ^ ((M j + r) * (q * τ)) / aeval y (L j) ^ (q * τ) := by
            rw [hZY]; ring
        _ = _ := by ring
    rw [heq]
    exact mul_mem (mul_mem hu (pow_mem (pow_mem hpV _) _)) (pow_mem hw _)
  have hint : (p : Ω) ^ (S * (q * τ)) * (s / aeval y (L j) ^ (q * τ)) ∈
      integralClosure (Subring.closure Sset) Ω := by
    have hmem : (p : Ω) ^ (S * (q * τ)) * (s / aeval y (L j) ^ (q * τ)) ∈
        (integralClosure (Subring.closure Sset) Ω).toSubring := by
      rw [← iInf_valuationSubring_superset]
      exact Subring.mem_iInf.mpr fun V => key V.1 V.2
    exact hmem
  have h := hN Ω D (fun i => aeval y (L i)) (pullField y L) rfl
    (hG K ι Ω y D e L hAr hBir he hhomL hnz) p hp j (S * (q * τ))
    (Module.finrank (pullField y L) Ω * (q * τ)) (s / aeval y (L j) ^ (q * τ)) c
    (hhom _ le_rfl) hcp hint μ
  have hn : Module.finrank (pullField y L) Ω * (S * (q * τ)) =
      Module.finrank (pullField y L) Ω * S * q * τ := by ring
  rw [hn] at h
  exact h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
