import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfOrthKfin

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

noncomputable section
namespace GlobalTheory.KFinApprox

theorem approx_identity : ∀ (n : ℕ) (ε : Fin n → Bool) (X : Type) [TopologicalSpace X] (F : X → KG ε → ℂ),
    (Continuous fun p : X × KG ε => F p.1 p.2) → ∀ C : Set X, IsCompact C → ∀ δ : ℝ, 0 < δ →
    ∃ e : KG ε → ℂ, KFinFun ε e ∧ ∀ x ∈ C, ‖F x 1 - ∫ k, e k * F x k ∂(muK ε)‖ < δ := by
  intro n ε X _ F hF C hC δ hδ

  have hFx : ∀ x, Continuous (F x) := fun x =>
    hF.comp (Continuous.prodMk continuous_const continuous_id)
  have hintC : ∀ g : KG ε → ℂ, Continuous g → Integrable g (muK ε) := fun g hg =>
    hg.integrable_of_hasCompactSupport (isClosed_tsupport g).isCompact
  have hintR : ∀ g : KG ε → ℝ, Continuous g → Integrable g (muK ε) := fun g hg =>
    hg.integrable_of_hasCompactSupport (isClosed_tsupport g).isCompact

  have hG : Continuous fun z : KG ε × X => ‖F z.2 z.1 - F z.2 1‖ :=
    ((hF.comp (Continuous.prodMk continuous_snd continuous_fst)).sub
      (hF.comp (Continuous.prodMk continuous_snd continuous_const))).norm
  have hev : ∀ᶠ k in 𝓝 (1 : KG ε), ∀ x ∈ C, ‖F x k - F x 1‖ < δ / 3 := by
    refine hC.eventually_forall_of_forall_eventually (fun y _ => ?_)
    have ht := hG.tendsto ((1 : KG ε), y)
    simp only [sub_self, norm_zero] at ht
    exact ht.eventually_lt_const (by positivity)
  obtain ⟨U, hUP, hUo, hU1⟩ := eventually_nhds_iff.1 hev

  obtain ⟨f, hf0, hf1, hf01⟩ := exists_continuous_zero_one_of_isClosed hUo.isClosed_compl
    (isClosed_singleton (x := (1 : KG ε))) (Set.disjoint_singleton_right.2 (fun h => h hU1))
  have hf1' : f 1 = 1 := by simpa using hf1 (Set.mem_singleton (1 : KG ε))
  have hfnn : ∀ k, 0 ≤ f k := fun k => (hf01 k).1
  have hfU : ∀ k, k ∉ U → f k = 0 := fun k hk => by simpa using hf0 hk
  have hIpos : 0 < ∫ k, f k ∂(muK ε) :=
    Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero f.continuous
      (isClosed_tsupport _).isCompact (fun k => hfnn k) (x := 1) (by rw [hf1']; norm_num)
  obtain ⟨I, hIdef⟩ : ∃ I, ∫ k, f k ∂(muK ε) = I := ⟨_, rfl⟩
  rw [hIdef] at hIpos

  let ψ : C(KG ε, ℂ) := ⟨fun k => ((f k / I : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (f.continuous.div_const I)⟩
  have hψ : ∀ k, ψ k = ((f k / I : ℝ) : ℂ) := fun k => rfl
  have hψint : ∫ k, ψ k ∂(muK ε) = 1 := by
    simp only [hψ]
    rw [integral_complex_ofReal, integral_div, hIdef, div_self hIpos.ne']
    simp
  have hψnorm : ∀ k, ‖ψ k‖ = f k / I := fun k => by
    rw [hψ, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (hfnn k) hIpos.le)]
  have h7 := GlobalTheory.KFinSep.finAlg_dense ε

  obtain ⟨M, hM⟩ := (hC.prod isCompact_univ).exists_bound_of_continuousOn hF.continuousOn
  obtain ⟨A, hA, hMA⟩ : ∃ A : ℝ, 0 < A ∧ M * (muK ε).real Set.univ ≤ A := by
    have hm : 0 ≤ (muK ε).real Set.univ := measureReal_nonneg
    refine ⟨(|M| + 1) * ((muK ε).real Set.univ + 1), by positivity, ?_⟩
    nlinarith [le_abs_self M, abs_nonneg M]
  have hη : 0 < δ / (3 * A) := div_pos hδ (by linarith)

  have hmem : ψ ∈ (GlobalTheory.KFinSep.finAlg ε).topologicalClosure := by
    rw [h7]; exact StarSubalgebra.mem_top
  have hmem' : ψ ∈ closure ((GlobalTheory.KFinSep.finAlg ε : Set C(KG ε, ℂ))) := hmem
  obtain ⟨p, hp, hpd⟩ := Metric.mem_closure_iff.1 hmem' (δ / (3 * A)) hη
  have hpK : KFinFun ε p := hp.1
  have hpk : ∀ k, ‖ψ k - p k‖ ≤ δ / (3 * A) := fun k => by
    have h := ContinuousMap.norm_coe_le_norm (ψ - p) k
    rw [← dist_eq_norm] at h
    simpa using h.trans hpd.le
  refine ⟨p, hpK, fun x hx => ?_⟩
  have i1 : Integrable (fun k => ψ k * F x 1) (muK ε) := hintC _ (ψ.continuous.mul continuous_const)
  have i2 : Integrable (fun k => ψ k * F x k) (muK ε) := hintC _ (ψ.continuous.mul (hFx x))
  have i3 : Integrable (fun k => p k * F x k) (muK ε) := hintC _ (p.continuous.mul (hFx x))
  have e1 : ∫ k, ψ k * (F x 1 - F x k) ∂(muK ε) = F x 1 - ∫ k, ψ k * F x k ∂(muK ε) := by
    simp_rw [mul_sub]
    rw [integral_sub i1 i2, integral_mul_const, hψint, one_mul]
  have e2 : ∫ k, (ψ k - p k) * F x k ∂(muK ε) =
      ∫ k, ψ k * F x k ∂(muK ε) - ∫ k, p k * F x k ∂(muK ε) := by
    simp_rw [sub_mul]
    exact integral_sub i2 i3
  have e3 : F x 1 - ∫ k, p k * F x k ∂(muK ε) =
      ∫ k, ψ k * (F x 1 - F x k) ∂(muK ε) + ∫ k, (ψ k - p k) * F x k ∂(muK ε) := by
    rw [e1, e2]; ring
  have b1 : ‖∫ k, ψ k * (F x 1 - F x k) ∂(muK ε)‖ ≤ δ / 3 := by
    have hg : Integrable (fun k => f k / I * (δ / 3)) (muK ε) :=
      hintR _ ((f.continuous.div_const I).mul continuous_const)
    refine (norm_integral_le_of_norm_le hg (Filter.Eventually.of_forall fun k => ?_)).trans_eq ?_
    · rw [norm_mul, hψnorm]
      by_cases hk : k ∈ U
      · have := hUP k hk x hx
        rw [norm_sub_rev] at this
        exact mul_le_mul_of_nonneg_left this.le (div_nonneg (hfnn k) hIpos.le)
      · rw [hfU k hk]; simp
    · rw [integral_mul_const, integral_div, hIdef, div_self hIpos.ne', one_mul]
  have b2 : ‖∫ k, (ψ k - p k) * F x k ∂(muK ε)‖ ≤ δ / 3 := by
    refine (norm_integral_le_of_norm_le_const (C := δ / (3 * A) * M)
      (Filter.Eventually.of_forall fun k => ?_)).trans ?_
    · rw [norm_mul]
      exact mul_le_mul (hpk k) (hM (x, k) ⟨hx, Set.mem_univ _⟩) (norm_nonneg _) hη.le
    · calc δ / (3 * A) * M * (muK ε).real Set.univ
          = δ / (3 * A) * (M * (muK ε).real Set.univ) := by ring
        _ ≤ δ / (3 * A) * A := mul_le_mul_of_nonneg_left hMA hη.le
        _ = δ / 3 := by field_simp
  rw [e3]
  calc ‖∫ k, ψ k * (F x 1 - F x k) ∂(muK ε) + ∫ k, (ψ k - p k) * F x k ∂(muK ε)‖
      ≤ δ / 3 + δ / 3 := (norm_add_le _ _).trans (add_le_add b1 b2)
    _ < δ := by linarith

end GlobalTheory.KFinApprox
