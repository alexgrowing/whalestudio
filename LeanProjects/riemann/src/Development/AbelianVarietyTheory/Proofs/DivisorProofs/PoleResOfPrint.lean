import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinResidueLine
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwiningConstEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoConstTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinDerivativeBoundSetting
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EisRes.PoleRes

theorem exists_analyticAt_of_tendsto {f : ℂ → ℂ} {z₀ R : ℂ} {S : Set ℂ} (hf : MeromorphicAt f z₀) (hS : z₀ ∉ S)
    [(𝓝[S] z₀).NeBot] (hR : R ≠ 0) (hlim : Tendsto f (𝓝[S] z₀) (𝓝 R)) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧ g z₀ = R ∧ ∀ᶠ z in 𝓝[≠] z₀, f z = g z := by
  have hle : 𝓝[S] z₀ ≤ 𝓝[≠] z₀ := nhdsWithin_mono _ (Set.subset_compl_singleton_iff.2 hS)
  cases ho : meromorphicOrderAt f z₀ with
  | top =>
    exfalso
    have h0 : Tendsto f (𝓝[≠] z₀) (𝓝 0) := tendsto_const_nhds.congr' (by
      filter_upwards [meromorphicOrderAt_eq_top_iff.1 ho] with y hy using hy.symm)
    exact hR (tendsto_nhds_unique hlim (h0.mono_left hle))
  | coe m =>
    rcases lt_trichotomy m 0 with hm | rfl | hm
    · exfalso
      have hc := tendsto_cobounded_of_meromorphicOrderAt_neg (f := f) (x := z₀) (by rw [ho]; exact_mod_cast hm)
      exact not_tendsto_atTop_of_tendsto_nhds hlim.norm (tendsto_norm_cobounded_atTop.comp (hc.mono_left hle))
    · obtain ⟨g, hg, -, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).1 ho
      have hfg' : ∀ᶠ z in 𝓝[≠] z₀, f z = g z := by
        filter_upwards [hfg] with z hz using by simpa using hz
      refine ⟨g, hg, ?_, hfg'⟩
      have : Tendsto f (𝓝[S] z₀) (𝓝 (g z₀)) :=
        (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' (EventuallyEq.symm (hfg'.filter_mono hle))
      exact tendsto_nhds_unique this hlim
    · exfalso
      have h0 := tendsto_zero_of_meromorphicOrderAt_pos (f := f) (x := z₀) (by rw [ho]; exact_mod_cast hm)
      exact hR (tendsto_nhds_unique hlim (h0.mono_left hle))

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def lineStab (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) :
    Subgroup (ratPts σ J) where
  carrier := {p | ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p.1).1 * adMat F x = l.1 • adMat F x}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a b ⟨la, ha⟩ ⟨lb, hb⟩
    refine ⟨lb * la, ?_⟩
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul]
    rw [Matrix.mul_assoc, hb, Matrix.mul_smul, ha, smul_smul]
  inv_mem' := by
    rintro a ⟨l, ha⟩
    refine ⟨l⁻¹, ?_⟩
    have e : (matHom _ σ J (a⁻¹ : ratPts σ J).1).1 * (matHom _ σ J a.1).1 = 1 := by
      rw [← Units.val_mul, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Units.val_one]
    calc (matHom _ σ J (a⁻¹ : ratPts σ J).1).1 * adMat F x
        = (l⁻¹).1 • (l.1 • ((matHom _ σ J (a⁻¹ : ratPts σ J).1).1 * adMat F x)) := by
          rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
      _ = (l⁻¹).1 • adMat F x := by
          rw [← Matrix.mul_smul, ← ha, ← Matrix.mul_assoc, e, Matrix.one_mul]

theorem exists_reps (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Matrix (Fin n) (Fin 1) E) :
    ∃ T : Set (ratPts σ J), ∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l : (AF F ⊗[F] E)ˣ,
      (matHom _ σ J (γ * t⁻¹ : ratPts σ J).1).1 * adMat F x = l.1 • adMat F x := by
  let s : Setoid (ratPts σ J) := QuotientGroup.rightRel (lineStab σ J x)
  refine ⟨Set.range fun q : Quotient s => q.out, fun γ => ⟨(Quotient.mk s γ).out, ⟨⟨_, rfl⟩, ?_⟩, ?_⟩⟩
  · exact QuotientGroup.rightRel_apply.1 (Quotient.mk_out (s := s) γ)
  · rintro t ⟨⟨q, rfl⟩, ht⟩
    have h : s.r q.out γ := QuotientGroup.rightRel_apply.2 ht
    have : q = Quotient.mk s γ := (Quotient.out_eq q).symm.trans (Quotient.sound h)
    rw [this]

end GlobalTheory.EisRes.PoleRes

end

noncomputable section

namespace GlobalTheory.EisRes.PoleRes

theorem poleRes_of_eisensteinResidue : GlobalTheory.Published.EisensteinResidueLine → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ),
    HidaSetting σ J X Y L a h → EisensteinHyp σ J (col0 X) (col0 Y) h Eis c → ∀ mid : ℂ → GAd σ J → ℂ, (∀ g, DifferentiableOn ℂ (mid · g) {s : ℂ | ((n : ℝ) - 1) / 2 - 1 < s.re}) → (∀ (μ : Measure (unipRad σ J (col0 X))) (𝓕 : Set (unipRad σ J (col0 X))), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J (col0 X))) 𝓕 μ → μ 𝓕 = 1 →
      ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → ∀ g, ∫ u in 𝓕, Eis s (u.1 * g) ∂μ =
        (h g : ℂ) ^ (s + (((n : ℂ) - 1) / 2)) + mid s g + c s * (h g : ℂ) ^ (-s + (((n : ℂ) - 1) / 2))) →
      ∃ (u : ℂ → ℂ) (U₀ U : Set ℂ) (Hol : ℂ → GAd σ J → ℂ) (C : ℝ) (N : ℕ),
        (U₀ ∈ 𝓝 (((n : ℂ) - 1) / 2) ∧ DifferentiableOn ℂ u U₀ ∧ u (((n : ℂ) - 1) / 2) ≠ 0 ∧ ∀ s ∈ U₀, s ≠ (((n : ℂ) - 1) / 2) → c s = u s / (s - (((n : ℂ) - 1) / 2))) ∧ U ∈ 𝓝 (((n : ℂ) - 1) / 2) ∧
        (∀ s ∈ U, s ≠ (((n : ℂ) - 1) / 2) → ∀ g, Hol s g = (s - (((n : ℂ) - 1) / 2)) * Eis s g) ∧ (∀ g, DifferentiableOn ℂ (Hol · g) U) ∧
        (∀ s ∈ U, ∀ g, ‖Hol s g‖ ≤ C * (height σ J g : ℝ) ^ N) ∧ ∀ g, Hol (((n : ℂ) - 1) / 2) g = u (((n : ℂ) - 1) / 2) := by
  intro hPr F E _ _ _ _ _ σ n J r X Y L a h Eis c hS hP mid hmid hCT
  set ρ : ℂ := ((n : ℂ) - 1) / 2 with hρ
  have hρre : ρ.re = ((n : ℝ) - 1) / 2 := by
    have : ρ = ((((n : ℝ) - 1) / 2 : ℝ) : ℂ) := by rw [hρ]; push_cast; ring
    rw [this, Complex.ofReal_re]

  set P : Set ℂ := {s : ℂ | ((n : ℝ) - 1) / 2 < s.re} with hPdef
  have hρP : ρ ∉ P := by
    intro hm; rw [hPdef, Set.mem_setOf_eq, hρre] at hm; exact lt_irrefl _ hm
  haveI hNB : (𝓝[P] ρ).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [hPdef, Complex.closure_setOf_lt_re, Set.mem_setOf_eq, hρre])
  have hevP : ∀ᶠ s in 𝓝[P] ρ, s ≠ ρ ∧ ((n : ℝ) - 1) / 2 < s.re := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact ⟨fun e => hρP (e ▸ hs), hs⟩
  have hsub : Tendsto (fun s : ℂ => s - ρ) (𝓝[P] ρ) (𝓝 0) := by
    have : Tendsto (fun s : ℂ => s - ρ) (𝓝 ρ) (𝓝 (ρ - ρ)) := (continuous_id.sub continuous_const).tendsto ρ
    simpa using this.mono_left (nhdsWithin_le_nhds (s := P))

  obtain ⟨T, hT⟩ := exists_reps σ J (col0 X)
  obtain ⟨R, hR0, hRlim⟩ := hPr F E σ hS.1 hS.2.1 n J hS.2.2.1 r X Y hS.2.2.2.2.1 (col0 X) rfl L a
    hS.2.2.2.2.2.1 h hS.2.2.2.2.2.2.1 hS.2.2.2.2.2.2.2 T hT
  have hEl : ∀ g, Tendsto (fun s => (s - ρ) * Eis s g) (𝓝[P] ρ) (𝓝 R) := fun g =>
    (hRlim g).congr' (eventually_nhdsWithin_of_forall fun s hs => by rw [(hP.1 T hT s hs g).tsum_eq])

  have val : ∀ (k : ℕ) (U : Set ℂ) (H : ℂ → GAd σ J → ℂ), U ∈ 𝓝 ρ → (∀ g, DifferentiableOn ℂ (H · g) U) →
      (∀ s ∈ U, s ≠ ρ → ∀ g, H s g = (s - ρ) ^ k * Eis s g) → ∀ g, k ≠ 0 ∧ H ρ g = 0 ^ (k - 1) * R := by
    intro k U H hU hd hH g
    have hc : Tendsto (fun s => H s g) (𝓝[P] ρ) (𝓝 (H ρ g)) :=
      ((hd g).continuousOn.continuousAt hU).tendsto.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ s in 𝓝[P] ρ, H s g = (s - ρ) ^ k * Eis s g := by
      filter_upwards [hevP, nhdsWithin_le_nhds hU] with s hs hsU using hH s hsU hs.1 g
    rcases k with _ | j
    · exfalso
      have h1 : Tendsto (fun s => (s - ρ) * H s g) (𝓝[P] ρ) (𝓝 (0 * H ρ g)) := hsub.mul hc
      have h2 : Tendsto (fun s => (s - ρ) * H s g) (𝓝[P] ρ) (𝓝 R) := (hEl g).congr' (by
        filter_upwards [hev] with s hs; rw [hs, pow_zero, one_mul])
      rw [zero_mul] at h1
      exact hR0 (tendsto_nhds_unique h2 h1)
    · refine ⟨Nat.succ_ne_zero j, ?_⟩
      have h2 : Tendsto (fun s => H s g) (𝓝[P] ρ) (𝓝 (0 ^ j * R)) :=
        ((hsub.pow j).mul (hEl g)).congr' (by
          filter_upwards [hev] with s hs; rw [hs, pow_succ, mul_assoc])
      simpa using tendsto_nhds_unique hc h2
  have main : ∀ (k : ℕ) (U : Set ℂ) (H : ℂ → GAd σ J → ℂ), U ∈ 𝓝 ρ → (∀ g, DifferentiableOn ℂ (H · g) U) →
      (∀ s ∈ U, s ≠ ρ → ∀ g, H s g = (s - ρ) ^ k * Eis s g) →
      ∃ H₁ : ℂ → GAd σ J → ℂ, (∀ g, DifferentiableOn ℂ (H₁ · g) U) ∧
        (∀ s ∈ U, s ≠ ρ → ∀ g, H₁ s g = (s - ρ) ^ 1 * Eis s g) ∧ ∀ g, H₁ ρ g = R := by
    intro k
    induction k with
    | zero =>
      intro U H hU hd hH
      exact ((val 0 U H hU hd hH 1).1 rfl).elim
    | succ k ih =>
      intro U H hU hd hH
      have hval : ∀ g, H ρ g = 0 ^ k * R := fun g => by simpa using (val (k + 1) U H hU hd hH g).2
      rcases k with _ | k
      · exact ⟨H, hd, hH, fun g => by simpa using hval g⟩
      · refine ih U (fun s g => dslope (H · g) ρ s) hU (fun g => (Complex.differentiableOn_dslope hU).2 (hd g)) ?_
        intro s hs hsρ g
        rw [dslope_of_ne _ hsρ, slope_def_field, hval g, hH s hs hsρ g]
        simp only [zero_pow (Nat.succ_ne_zero k), zero_mul, sub_zero]
        rw [pow_succ]
        field_simp [sub_ne_zero.2 hsρ]
  obtain ⟨k, U, H, hU, hH, -, hwh⟩ := hP.2.2.2.1 ρ
  have hd : ∀ g, DifferentiableOn ℂ (H · g) U := fun g => hwh _ (GlobalTheory.EisLine.isModerateForm_proj σ J g)
  obtain ⟨H₁, hd₁, hH₁, hv₁⟩ := main k U H hU hd hH
  obtain ⟨V, hV, C, N, hb⟩ := GlobalTheory.EisRes.laurentMul_locally_uniform_moderate F E σ n J r X Y L a h Eis c hS hP 1 U H₁ hU hd₁ hH₁

  obtain ⟨-, -, -, μ, 𝓕, hμ, h𝓕, h1𝓕, -⟩ := GlobalTheory.EisRes.CReduce.intertwiningConst_eq F E σ n J r X Y L a h Eis c hS hP
  have h1 : h 1 = 1 := by
    have e := hS.2.2.2.2.2.2.2 1 1 (by simp) 1 (one_mem _)
    rw [mul_one, map_one] at e
    simpa using e
  obtain ⟨-, hCTl⟩ := GlobalTheory.EisCT.LimCT.tendsto_constTerm F E σ n J r X Y L a h Eis c hS hP 1 U H₁ hU hd₁ hH₁ μ 𝓕 hμ h𝓕 h1𝓕 1
  have hI : ∫ x in 𝓕, H₁ ρ (x.1 * 1) ∂μ = R := by
    simp only [hv₁, setIntegral_const]
    simp [Measure.real, h1𝓕]
  rw [hI] at hCTl
  have hle : 𝓝[P] ρ ≤ 𝓝[≠] ρ := nhdsWithin_mono _ (Set.subset_compl_singleton_iff.2 hρP)
  have hmidc : ContinuousAt (mid · 1) ρ :=
    (hmid 1).continuousOn.continuousAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by rw [Set.mem_setOf_eq, hρre]; linarith))
  have hA : Tendsto (fun s => (s - ρ) * (1 + mid s 1)) (𝓝[P] ρ) (𝓝 0) := by
    simpa using hsub.mul ((tendsto_const_nhds.add hmidc.tendsto).mono_left nhdsWithin_le_nhds)
  have hfl : Tendsto (fun s => (s - ρ) * c s) (𝓝[P] ρ) (𝓝 R) := by
    have := (hCTl.mono_left hle).sub hA
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [hevP, nhdsWithin_le_nhds hU] with s hs hsU
    rw [show (fun x : unipRad σ J (col0 X) => H₁ s (x.1 * 1)) =
        fun x => (s - ρ) ^ 1 * Eis s (x.1 * 1) from funext fun x => hH₁ s hsU hs.1 _,
      integral_const_mul, hCT μ 𝓕 hμ h𝓕 h1𝓕 s hs.2 1, h1]
    simp only [Complex.ofReal_one, Complex.one_cpow, pow_one]
    ring

  have hmc : MeromorphicAt (fun s => (s - ρ) * c s) ρ :=
    ((analyticAt_id.sub analyticAt_const).meromorphicAt).mul (hP.2.2.1 ρ (Set.mem_univ _))
  obtain ⟨u, hua, huR, hfu⟩ := exists_analyticAt_of_tendsto hmc hρP hR0 hfl
  have hU₀ : {s | AnalyticAt ℂ u s} ∩ {s | s ≠ ρ → (s - ρ) * c s = u s} ∈ 𝓝 ρ :=
    inter_mem hua.eventually_analyticAt (eventually_nhdsWithin_iff.1 hfu)
  refine ⟨u, _, U ∩ V, H₁, C, N, ⟨hU₀, fun s hs => hs.1.differentiableAt.differentiableWithinAt, by rw [huR]; exact hR0,
    fun s hs hsρ => ?_⟩, inter_mem hU hV, fun s hs hsρ g => by rw [hH₁ s hs.1 hsρ g, pow_one],
    fun g => (hd₁ g).mono Set.inter_subset_left, fun s hs g => hb s hs.2 g, fun g => by rw [hv₁, huR]⟩
  rw [eq_div_iff (sub_ne_zero.2 hsρ), ← hs.2 hsρ, mul_comm]

end GlobalTheory.EisRes.PoleRes

end
