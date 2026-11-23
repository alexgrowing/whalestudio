import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicHeightBlockDiagonalEmbeddingLeMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTopSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalEmbeddingPreservesRationalPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactStabDbl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

noncomputable section

namespace UpperTheory.KDiv

private theorem tsum_norm_le {G : Type} [Group G] {P Γ : Subgroup G} {a : G → ℝ≥0} (ha : ∀ g, 0 < a g) {H₀ : G → ℝ}
    (hH : ∀ g, 1 ≤ H₀ g) {σ₀ ρ τ : ℝ} (hτ : σ₀ < τ) {f Ei : ℂ → G → ℂ}
    (hf : ∀ (t : ℝ) g, f t g = (((a g : ℝ) ^ (t + ρ) : ℝ) : ℂ))
    (h1 : ∀ s : ℂ, σ₀ < s.re → ∀ g, GlobalTheory.Eis.CosetConv P Γ (f s) g ∧ Ei s g = GlobalTheory.Eis.cosetSum P Γ (f s) g)
    {k : ℕ} {r : ℝ} {H : ℂ → G → ℂ} (hr : 0 < r)
    (h2 : ∀ s ∈ Metric.ball (τ : ℂ) r, s ≠ τ → ∀ g, H s g = (s - τ) ^ k * Ei s g) {C : ℝ} {N : ℕ}
    (h3 : ∀ s ∈ Metric.ball (τ : ℂ) r, ∀ g, ‖H s g‖ ≤ C * H₀ g ^ N) {Φ : G → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (hΦ : ∀ g, ‖Φ g‖ ≤ M * (a g : ℝ) ^ (τ + ρ)) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ g, ∑' q, ‖GlobalTheory.Eis.term P Γ Φ g q‖ ≤ C' * H₀ g ^ N := by
  obtain ⟨ε, hε, hεr, hετ⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < r ∧ ε < τ - σ₀ :=
    ⟨min r (τ - σ₀) / 2, by have := lt_min hr (sub_pos.2 hτ); linarith,
      by have := lt_min hr (sub_pos.2 hτ); have := min_le_left r (τ - σ₀); linarith,
      by have := lt_min hr (sub_pos.2 hτ); have := min_le_right r (τ - σ₀); linarith⟩
  have key : ∀ t : ℝ, |t - τ| = ε → ∀ g, Summable (fun q => ((GlobalTheory.Eis.term P Γ a g q : ℝ≥0) : ℝ) ^ (t + ρ)) ∧
      ∑' q, ((GlobalTheory.Eis.term P Γ a g q : ℝ≥0) : ℝ) ^ (t + ρ) ≤ max C 0 / ε ^ k * H₀ g ^ N := by
    intro t ht g
    have hn : ‖(t : ℂ) - τ‖ = ε := by rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, ht]
    have hb : (t : ℂ) ∈ Metric.ball (τ : ℂ) r := by rw [mem_ball_iff_norm, hn]; exact hεr
    have hne : (t : ℂ) ≠ τ := fun h => by rw [h, sub_self, norm_zero] at hn; exact hε.ne hn
    have hσ : σ₀ < (t : ℂ).re := by
      have := neg_abs_le (t - τ)
      rw [Complex.ofReal_re]; linarith
    have e : ∀ q, GlobalTheory.Eis.term P Γ (f t) g q = ((((GlobalTheory.Eis.term P Γ a g q : ℝ≥0) : ℝ) ^ (t + ρ) : ℝ) : ℂ) :=
      fun q => hf t _
    have hs : Summable (fun q => ((GlobalTheory.Eis.term P Γ a g q : ℝ≥0) : ℝ) ^ (t + ρ)) := by
      refine (h1 t hσ g).1.congr fun q => ?_
      rw [e, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    refine ⟨hs, ?_⟩
    have e2 : ‖Ei t g‖ = ∑' q, ((GlobalTheory.Eis.term P Γ a g q : ℝ≥0) : ℝ) ^ (t + ρ) := by
      rw [(h1 t hσ g).2, GlobalTheory.Eis.cosetSum, tsum_congr e, ← Complex.ofReal_tsum, Complex.norm_real,
        Real.norm_of_nonneg (tsum_nonneg fun q => by positivity)]
    have e3 := h3 t hb g
    rw [h2 t hb hne, norm_mul, norm_pow, hn, e2] at e3
    have hp : 0 ≤ H₀ g ^ N := pow_nonneg (zero_le_one.trans (hH g)) N
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hε k), mul_comm]
    exact e3.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hp)
  refine ⟨M * (2 * (max C 0 / ε ^ k)), by positivity, fun g => ?_⟩
  obtain ⟨s1, b1⟩ := key (τ - ε) (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hε]) g
  obtain ⟨s2, b2⟩ := key (τ + ε) (by rw [add_sub_cancel_left, abs_of_pos hε]) g
  have hle : ∀ q, ‖GlobalTheory.Eis.term P Γ Φ g q‖ ≤ M * (((GlobalTheory.Eis.term P Γ a g q : ℝ≥0) : ℝ) ^ (τ - ε + ρ) +
      ((GlobalTheory.Eis.term P Γ a g q : ℝ≥0) : ℝ) ^ (τ + ε + ρ)) := fun q =>
    (hΦ _).trans (mul_le_mul_of_nonneg_left (GlobalTheory.Eis.rpow_le_add (ha _) (by linarith) (by linarith)) hM)
  have s3 := (s1.add s2).mul_left M
  refine (Summable.tsum_le_tsum hle (.of_nonneg_of_le (fun _ => norm_nonneg _) hle s3) s3).trans ?_
  rw [tsum_mul_left, s1.tsum_add s2, mul_assoc]
  exact mul_le_mul_of_nonneg_left (by linarith) hM

set_option maxHeartbeats 1000000 in

theorem absConvPair : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ → 1 ≤ d →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
    ∀ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ K : Subgroup (UA σ W₂.J), IsStab B K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K →
    ∀ φ₀ ∈ degPSOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K χX (((n : ℂ) - (d : ℂ)) / 2),
    (∀ s : ℂ, (d : ℝ) / 2 < s.re →
        GlobalTheory.AutomorphicL2Unitary.LeftInv ((siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) ⊓ ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) ∧
        ∀ g, GlobalTheory.Eis.CosetConv (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) g) →
    ∀ μ : Measure (UA σ W.J), μ.IsHaarMeasure →
    ∃ R₂ : ℝ, ∀ s : ℂ, R₂ < s.re → ∀ 𝓕 : Set (UA σ W.J), IsFundamentalDomain (ratU σ W.J) 𝓕 μ →
      ∀ f : UA σ W.J → ℂ, Continuous f → (∀ γ ∈ ratU σ W.J, ∀ h, f (γ * h) = f h) →
      (∀ N : ℕ, ∃ C : ℝ, ∀ h, ‖f h‖ * (qht h : ℝ) ^ N ≤ C) → ∀ h, ∫⁻ x in 𝓕, ‖f x‖ₑ * ∑' q, ‖GlobalTheory.Eis.term (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) (i (h, x)) q‖ₑ ∂μ ≠ ⊤ := by
  intro hKP F E _ _ _ _ _ σ B n d Xs W M χX χW om r s' r₁ s₁ hP hd W₂ hJ hL hθ i hi K hK hIw φ₀ hφ₀ hLI μ hμ
  refine ⟨(d : ℝ) / 2, fun s hs 𝓕 h𝓕 f _ _ hdec h => ?_⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨eh⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := eh.isEmbedding.t2Space
  haveI := (GlobalTheory.UnipCT.topFacts σ W₂.J).1
  have hW := hP.skew
  have hcm := hP.base.cm
  have hKc : IsCompact (K : Set (UA σ W₂.J)) := GlobalTheory.DblStabSkewCpt.isCompact_stab_dbl hKP F E σ B d r₁ s₁ W hP.base hW W₂ hJ hL hθ K hK
  have hsph := hIw.spherical_mem continuous_subtype_val continuous_absE hKc 0
  obtain ⟨Ei, hE1, hE2⟩ := hKP.siegelEisensteinDoubled F E σ hcm hP.base.unram B d hd W hW.skew hW.lat hW.dual hW.cartan
    W₂ hJ hL hθ K hK hIw 1 ⟨continuous_const, fun _ => rfl⟩ 0 _ hsph
  obtain ⟨k, ρ, H, hρ, h2, -, -, C, N, h3⟩ := hE2 (s.re : ℂ)
  have hΦ := hIw.flatOf_mem continuous_subtype_val continuous_absE hKc hφ₀ s
  obtain ⟨M₀, hM₀⟩ := hKc.exists_bound_of_continuousOn (mem_degPSOf.1 hΦ).2.1.continuousOn
  have hb : ∀ g, ‖flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s g‖ ≤
      max M₀ 0 * (hgtOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K g : ℝ) ^ (s.re + (d : ℝ) / 2) := fun g => by
    have := IsIwasawa.norm_le hIw hΦ.1 (C := max M₀ 0) (fun x hx => (hM₀ x hx).trans (le_max_left _ _)) g
    have e : (s + (Fintype.card (Fin d) : ℂ) / 2).re = s.re + (d : ℝ) / 2 := by simp
    rw [e] at this
    exact this
  have hone : ∀ {m : ℕ} {J : Matrix (Fin m) (Fin m) E} (g : UA σ J), (1 : ℝ≥0) ≤ ht g := fun g => one_le_heightGL F _
  obtain ⟨C', hC', hS⟩ := tsum_norm_le (H₀ := fun g : UA σ W₂.J => (ht g : ℝ)) (ρ := (d : ℝ) / 2) (fun g => hgtOf_pos g)
    (fun g => by exact_mod_cast hone g) hs (fun t g => by
      rw [flatOf_apply, ← npow_add (hgtOf_pos g), Complex.ofReal_cpow (NNReal.coe_nonneg _)]
      unfold GlobalTheory.Doubling.npow
      congr 1
      simp only [Fintype.card_fin]
      push_cast
      ring) hE1 hρ h2 h3 (le_max_right _ _) hb
  have hi' : ∀ h h', (i (h, h')).1 = blkGL finSumFinEquiv (h.1, h'.1) := fun h h' => Units.ext (hi h h')
  have hht : ∀ h h', ht (i (h, h')) ≤ ht h * ht h' := fun h h' => by
    unfold ht
    rw [hi']
    exact GlobalTheory.BlockHeight.heightGL_blk_le F finSumFinEquiv _ _ _ rfl rfl
  obtain ⟨hinv, hconv⟩ := hLI s hs
  set Φ := flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s with hΦd
  set P := siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype with hPd
  have hq : ∀ x, ∑' q, ‖GlobalTheory.Eis.term P (ratU σ W₂.J) Φ (i (h, x)) q‖ ≤ max (C' * (ht h : ℝ) ^ N) 0 * (qht x : ℝ) ^ N := fun x => by
    have h0 : ∀ y, 0 ≤ ∑' q, ‖GlobalTheory.Eis.term P (ratU σ W₂.J) Φ (i (h, y)) q‖ := fun y => tsum_nonneg fun _ => norm_nonneg _
    have := GlobalTheory.ThKOrthVInt.norm_le_qht_of_le_ht (σ := σ) (J := W.J)
      (g := fun y => ((∑' q, ‖GlobalTheory.Eis.term P (ratU σ W₂.J) Φ (i (h, y)) q‖ : ℝ) : ℂ)) (C := C' * (ht h : ℝ) ^ N) (k := N)
      (fun γ hγ y => by
        have hr : i (1, γ) ∈ ratU σ W₂.J := GlobalTheory.ThK.DblKer.RatPair.blk_mem_ratU F E σ d W W₂ hJ i hi 1 (one_mem _) γ hγ
        have e : i (h, γ * y) = i (1, γ) * i (h, y) := by rw [← map_mul, Prod.mk_mul_mk, one_mul]
        congr 1
        rw [e, tsum_congr fun q => congrArg norm (GlobalTheory.Eis.term_mul_left hinv ⟨_, hr⟩ (i (h, y)) q)]
        exact (GlobalTheory.Eis.rmulEquiv P (ratU σ W₂.J) ⟨_, hr⟩).tsum_eq fun q => ‖GlobalTheory.Eis.term P (ratU σ W₂.J) Φ (i (h, y)) q‖)
      (fun y => by
        rw [Complex.norm_real, Real.norm_of_nonneg (h0 y), mul_assoc, ← mul_pow]
        refine (hS _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (ht _).2 ?_ N) hC')
        exact_mod_cast hht h y) x
    rwa [Complex.norm_real, Real.norm_of_nonneg (h0 x)] at this
  obtain ⟨Cf, hCf⟩ := hdec N
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  have hdet : W.J.det ≠ 0 := by
    intro h0
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have hd : (W.J.map (B.emb w).1).det = 0 := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    have hx : star v ≠ 0 := by simpa using hv
    have := (hW.cartan w).2.2 (star v) hx
    rw [star_star, Matrix.smul_mulVec, hMv, smul_zero, dotProduct_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  obtain ⟨c, hc, hcs⟩ : ∃ c : E, c ≠ 0 ∧ σ c = -c := GlobalTheory.CMImag.exists_imag_ne_zero F E σ hcm
  haveI := hμ
  have hv : μ 𝓕 < ⊤ := GlobalTheory.ThKOrthVInt.measure_fundDom_lt_top_smul hKP.siegelSetUnitary hcm hc
    (GlobalTheory.ThKOrthVInt.isHermND_smul_of_skew hσ hW.skew hdet hc hcs) h𝓕
  refine ne_top_of_le_ne_top (b := ∫⁻ _ in 𝓕, ENNReal.ofReal (max (C' * (ht h : ℝ) ^ N) 0 * Cf) ∂μ) ?_
    (lintegral_mono fun x => ?_)
  · rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hv.ne
  · simp_rw [← ofReal_norm_eq_enorm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hconv _), ← ENNReal.ofReal_mul (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left (hq x) (norm_nonneg _)).trans ?_)
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (hCf x) (le_max_right _ _)

end UpperTheory.KDiv

end
