import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsUnitApprox
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNonvanishingDense
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwistMetric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter NumberField Topology

noncomputable section

set_option linter.unusedSectionVars false

section Lemmas

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem isClosed_liesOver {F : Type} [Field F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (sg : F →+* ℂ) :
    IsClosed {z | LiesOver y sg z} := by
  have : {z | LiesOver y sg z} = ⋂ (d : K → ℕ) (g : MRing ι) (h : MRing ι) (θ : F)
      (_ : IsMultiHomog g d) (_ : IsMultiHomog h d) (_ : aeval y g = algebraMap F Ω θ * aeval y h),
      {z : (Σ k, ι k) → ℂ | eval z (map (Int.castRingHom ℂ) g) = sg θ * eval z (map (Int.castRingHom ℂ) h)} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rfl
  rw [this]
  refine isClosed_iInter fun d => isClosed_iInter fun g => isClosed_iInter fun h => isClosed_iInter fun θ =>
    isClosed_iInter fun _ => isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
  exact isClosed_eq (MvPolynomial.continuous_eval _) (continuous_const.mul (MvPolynomial.continuous_eval _))

theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem not_mem_mCoordIdeal {y : (Σ k, ι k) → Ω} {f : MRing ι} {d : K → ℕ} (hf : IsMultiHomog f d)
    (h0 : aeval y f ≠ 0) : f ∉ mCoordIdeal y := by
  intro hmem
  rw [mCoordIdeal, RingHom.mem_ker, ProjLine.mConeMap_eq_of_isMultiHomog y hf] at hmem
  rcases mul_eq_zero.1 hmem with h | h
  · exact h0 (MvPolynomial.C_eq_zero.1 h)
  · exact (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (MvPolynomial.X_ne_zero k)) h

theorem isMultiHomog_mul {f g : MRing ι} {df dg : K → ℕ} (hf : IsMultiHomog f df)
    (hg : IsMultiHomog g dg) : IsMultiHomog (f * g) (df + dg) := by
  classical
  intro m hm k
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf a ha k, hg b hb k]

theorem norm_le_of_isSmallH {F : Type} [Field F] [Fintype (F →+* ℂ)] [Algebra F Ω]
    (hND : NonvanishingDense.Statement) {y : (Σ k, ι k) → Ω} {d : ℕ} {A : HermLine ι} {τ : ℕ} {s : Ω}
    (θ : F) (har : IsArithVar (mCoordIdeal y) d) (hb : Birational y) (hA : IsSmoothHerm A)
    (hex : ∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z)
    (hs : IsSmallH (mCoordIdeal y) y A τ s)
    {dg dh : K → ℕ} {g h : MRing ι} (hg : IsMultiHomog g dg) (hh : IsMultiHomog h dh)
    (hdeg : ∀ k, (dg k : ℤ) = dh k + τ * A.a k) (hgh : aeval y g = algebraMap F Ω θ * s * aeval y h)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {sg : F →+* ℂ} (hzs : LiesOver y sg z) :
    ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤
      ‖sg θ‖ * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := by
  obtain ⟨e, g1, h1, hg1, hh1, hne, hrep⟩ := hb (algebraMap F Ω θ)
  set ev : MRing ι → ((Σ k, ι k) → ℂ) → ℂ := fun f z => eval z (map (Int.castRingHom ℂ) f) with hev

  have hpt : ∀ z' ∈ mcPts (mCoordIdeal y), LiesOver y sg z' → ev h1 z' ≠ 0 →
      ‖ev g z'‖ ≤ ‖sg θ‖ * ‖ev h z'‖ * A.h z' ^ τ := by
    intro z' hz' hl hh0
    have hsm := hs (dg + e) (e + dh) (g * h1) (g1 * h) z' (isMultiHomog_mul hg hh1)
      (isMultiHomog_mul hg1 hh) (fun k => by simp only [Pi.add_apply, Nat.cast_add, hdeg k]; ring)
      (by rw [map_mul, map_mul, hgh, hrep]; ring) hz'
    have hrel := hl e g1 h1 θ hg1 hh1 hrep
    simp only [map_mul, norm_mul] at hsm
    change ‖ev g z'‖ * ‖ev h1 z'‖ ≤ ‖ev g1 z'‖ * ‖ev h z'‖ * A.h z' ^ τ at hsm
    rw [show ev g1 z' = sg θ * ev h1 z' from hrel, norm_mul] at hsm
    have hp : 0 < ‖ev h1 z'‖ := norm_pos_iff.2 hh0
    nlinarith [hsm, hp]

  set R : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  set U : Set ((Σ k, ι k) → ℂ) := R ∩ ⋂ sg' : {sg' : F →+* ℂ // sg' ≠ sg}, {z | LiesOver y sg'.1 z}ᶜ
  have hUo : IsOpen U := isOpen_blockNonzero.inter
    (isOpen_iInter_of_finite fun sg' => (isClosed_liesOver y sg'.1).isOpen_compl)
  have hzU : z ∈ U := ⟨hz.1, Set.mem_iInter.2 fun sg' hl => sg'.2 ((hex z hz).unique hl hzs)⟩
  set φ : ((Σ k, ι k) → ℂ) → ℝ := fun z => ‖ev g z‖ - ‖sg θ‖ * ‖ev h z‖ * A.h z ^ τ
  have hφ : ContinuousAt φ z := by
    have hAc : ContinuousAt A.h z :=
      (hA.continuousOn).continuousAt (isOpen_blockNonzero.mem_nhds hz.1)
    exact ((MvPolynomial.continuous_eval _).norm.continuousAt).sub
      ((continuousAt_const.mul (MvPolynomial.continuous_eval _).norm.continuousAt).mul (hAc.pow τ))
  by_contra hcon
  have hpos : 0 < φ z := by simp only [φ]; linarith [not_le.1 hcon]
  have hnb : {z' | 0 < φ z'} ∩ U ∈ 𝓝 z :=
    Filter.inter_mem (hφ.eventually (lt_mem_nhds hpos)) (hUo.mem_nhds hzU)
  have hcl := hND K ι (mCoordIdeal y) d h1 har (not_mem_mCoordIdeal hh1 hne) hz
  obtain ⟨z', ⟨hφ', hU'⟩, hz'P, hz'h⟩ := mem_closure_iff_nhds.1 hcl _ hnb
  obtain ⟨sg'', hl'', -⟩ := hex z' hz'P
  have hsg : sg'' = sg := by
    by_contra hne'
    exact (Set.mem_iInter.1 hU'.2 ⟨sg'', hne'⟩) hl''
  subst hsg
  have := hpt z' hz'P hl'' hz'h
  simp only [Set.mem_ofPred_eq, φ] at hφ'
  linarith

theorem isSmallH_mul {F : Type} [Field F] [Fintype (F →+* ℂ)] [Algebra F Ω]
    (hND : NonvanishingDense.Statement) {y : (Σ k, ι k) → Ω} {d : ℕ} {A A' : HermLine ι} {τ : ℕ}
    (har : IsArithVar (mCoordIdeal y) d) (hb : Birational y) (hA : IsSmoothHerm A)
    (hex : ∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) (ha : A'.a = A.a) (θ : F)
    (hkey : ∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z →
      ‖sg θ‖ * A.h z ^ τ ≤ A'.h z ^ τ)
    {s : Ω} (hs : IsSmallH (mCoordIdeal y) y A τ s) :
    IsSmallH (mCoordIdeal y) y A' τ (algebraMap F Ω θ * s) := by
  intro dg dh g h z hg hh hdeg hgh hz
  obtain ⟨sg, hsg, -⟩ := hex z hz
  have h1 := norm_le_of_isSmallH hND θ har hb hA hex hs hg hh (fun k => by rw [← ha]; exact hdeg k)
    (by rw [hgh]) hz hsg
  calc ‖eval z (map (Int.castRingHom ℂ) g)‖
      ≤ ‖sg θ‖ * ‖eval z (map (Int.castRingHom ℂ) h)‖ * A.h z ^ τ := h1
    _ = ‖eval z (map (Int.castRingHom ℂ) h)‖ * (‖sg θ‖ * A.h z ^ τ) := by ring
    _ ≤ ‖eval z (map (Int.castRingHom ℂ) h)‖ * A'.h z ^ τ :=
        mul_le_mul_of_nonneg_left (hkey z hz sg hsg) (norm_nonneg _)

theorem mul_mem_chartLatNm {F : Type} [Field F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ)
    {θ : F} (hθ : IsIntegral ℤ θ) {s : Ω} (hs : s ∈ chartLatNm y a τ) :
    algebraMap F Ω θ * s ∈ chartLatNm y a τ := by
  intro c hc
  have h := hs c hc
  rw [mul_assoc]
  have hθ' : IsIntegral (chartRingZ y c) (algebraMap F Ω θ) := (hθ.algebraMap).tower_top
  exact (integralClosure (chartRingZ y c) Ω).mul_mem hθ' h

theorem smallSectionCount_le_of_integral_mul {F : Type} [Field F] [Algebra F Ω] {y : (Σ k, ι k) → Ω} {A A' : HermLine ι}
    (ha : A'.a = A.a) {τ : ℕ}
    (hfin : {s : chartLatNm y A'.a τ | IsSmallH (mCoordIdeal y) y A' τ (s : Ω)}.Finite)
    {θ : F} (hθ : IsIntegral ℤ θ) (hθ0 : θ ≠ 0)
    (hmul : ∀ s : Ω, IsSmallH (mCoordIdeal y) y A τ s →
      IsSmallH (mCoordIdeal y) y A' τ (algebraMap F Ω θ * s)) :
    smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ ≤
      smallSectionCount (IsSmallH (mCoordIdeal y) y A') (chartLatNm y A'.a) τ := by
  unfold smallSectionCount
  have : Finite {s : chartLatNm y A'.a τ // IsSmallH (mCoordIdeal y) y A' τ (s : Ω)} := hfin.to_subtype
  have hθ0' : algebraMap F Ω θ ≠ 0 := (map_ne_zero _).2 hθ0
  have hc : Nat.card {s : chartLatNm y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)} ≤
      Nat.card {s : chartLatNm y A'.a τ // IsSmallH (mCoordIdeal y) y A' τ (s : Ω)} := by
    refine Nat.card_le_card_of_injective
      (fun s => (⟨⟨algebraMap F Ω θ * (s.1 : Ω), by rw [ha]; exact mul_mem_chartLatNm y A.a τ hθ s.1.2⟩,
        hmul _ s.2⟩ : {s : chartLatNm y A'.a τ // IsSmallH (mCoordIdeal y) y A' τ (s : Ω)})) ?_
    intro s t hst
    have h := congrArg (fun u : {s : chartLatNm y A'.a τ // IsSmallH (mCoordIdeal y) y A' τ (s : Ω)} =>
      ((u.1 : chartLatNm y A'.a τ) : Ω)) hst
    exact Subtype.ext (Subtype.ext (mul_left_cancel₀ hθ0' h))
  rcases Nat.eq_zero_or_pos (Nat.card {s : chartLatNm y A.a τ // IsSmallH (mCoordIdeal y) y A τ (s : Ω)})
    with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hc)

end Lemmas

theorem ArithmeticVolumeNefDual.proof (hG7p : ArithmeticVolumeNef.Statement) (hPk : PackingStatement) (hU : UnitApprox.Statement)
    (hND : NonvanishingDense.Statement) (hTw : TwistMetric.Statement) : ArithmeticVolumeNefDual.Statement := by
  intro K _ ι _ Ω _ F _ _ _ y D a A P0 Λ II hD hII har hb ha hP0 hsp hconj hΛpos hΛconj hΛsum hex hmon

  have hn : (0 : ℝ) < Fintype.card (F →+* ℂ) := by
    rw [NumberField.Embeddings.card]; exact_mod_cast Module.finrank_pos
  set m : ℝ := (∑ sg, Real.log (Λ sg)) / Fintype.card (F →+* ℂ) with hm_def
  have hm : m ≤ 0 := div_nonpos_of_nonpos_of_nonneg hΛsum hn.le
  set u : (F →+* ℂ) → ℝ := fun sg => Real.log (Λ sg) - m with hu_def
  have hu_conj : ∀ sg, u (ComplexEmbedding.conjugate sg) = u sg := fun sg => by simp only [u, hΛconj]
  have hu_sum : ∑ sg, u sg = 0 := by
    simp only [u]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hm_def,
      mul_div_cancel₀ _ hn.ne', sub_self]
  obtain ⟨C, hC⟩ := hU F u hu_conj hu_sum
  obtain ⟨c, hc⟩ := hTw K ι Ω F y D A P0 II u hD hII har hb hP0 hsp hconj hex hu_conj hu_sum
  have hden : ∀ τ : ℕ, 0 ≤ ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := fun τ => by positivity

  have hδ : ∀ δ : ℝ, 0 < δ →
      limsup (fun τ : ℕ => smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLatNm y A.a) τ /
        ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))) atTop ≤
        II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + c * δ := by
    intro δ hδ
    obtain ⟨A', ha', hsp', hconj', hpt, hII'⟩ := hc δ hδ
    have ha'' : A'.a = fun k => (a k : ℤ) := ha'.trans ha

    have hmon' : MonomialsBounded (mCoordIdeal y) A' a := by
      intro z hz μ hμ
      obtain ⟨sg, hsg, -⟩ := hex z hz
      have hAz : 0 < A.h z := A.pos z hz.1
      rw [hpt z hz sg hsg]
      calc ‖∏ p, z p ^ μ p‖ ≤ Λ sg * A.h z := hmon z hz sg hsg μ hμ
        _ = Real.exp (u sg + m) * A.h z := by
            rw [show u sg + m = Real.log (Λ sg) by simp only [u]; ring, Real.exp_log (hΛpos sg)]
        _ ≤ Real.exp (u sg + δ) * A.h z :=
            mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith)) hAz.le
    have hG := hG7p K ι Ω y D a A' P0 II hD hII har hb ha'' hP0 hsp' hmon' hconj'
    obtain ⟨hfin, C', hC'⟩ := hPk K ι Ω y D A' (chartLatNm y A'.a) har hb hsp'.1 (fun _ => le_rfl)
    refine le_trans ?_ (hG.trans hII')
    refine limsup_le_limsup ?_ ?_ ?_
    ·
      refine eventually_atTop.2 ⟨⌈C / δ⌉₊, fun τ hτ => div_le_div_of_nonneg_right ?_ (hden τ)⟩
      obtain ⟨ε, hε⟩ := hC τ
      have hCτ : C ≤ τ * δ := (div_le_iff₀ hδ).1 (Nat.ceil_le.1 hτ)
      have hε0 : ((ε : 𝓞 F) : F) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.2 ε.ne_zero
      refine smallSectionCount_le_of_integral_mul ha' (hfin τ) (RingOfIntegers.isIntegral_coe _) hε0 fun s hs => ?_
      refine isSmallH_mul hND har hb hsp.1 hex ha' _ ?_ hs
      intro z hz sg hsg
      have hAz : 0 < A.h z := A.pos z hz.1
      have hpos : 0 < ‖sg ((ε : 𝓞 F) : F)‖ := norm_pos_iff.2 ((map_ne_zero sg).2 hε0)
      have hlog : Real.log ‖sg ((ε : 𝓞 F) : F)‖ ≤ τ * u sg + τ * δ := by
        linarith [(abs_le.1 (hε sg)).2]
      rw [← mul_add, Real.log_le_iff_le_exp hpos, Real.exp_nat_mul] at hlog
      rw [hpt z hz sg hsg, mul_pow]
      exact mul_le_mul_of_nonneg_right hlog (pow_nonneg hAz.le τ)
    · exact isCoboundedUnder_le_of_le atTop (fun k => div_nonneg (Real.log_natCast_nonneg _) (hden k))
    · refine isBoundedUnder_of_eventually_le (a := |C'| * 2 ^ (D + 1) * ((D + 1).factorial : ℝ))
        (eventually_atTop.2 ⟨1, fun k hk => ?_⟩)
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have hkp : (0 : ℝ) < (k : ℝ) ^ (D + 1) := by positivity
      rw [div_le_iff₀ (by positivity)]
      have h2 : C' * ((k : ℝ) + 1) ^ (D + 1) ≤ |C'| * (2 * (k : ℝ)) ^ (D + 1) :=
        calc C' * ((k : ℝ) + 1) ^ (D + 1) ≤ |C'| * ((k : ℝ) + 1) ^ (D + 1) :=
              mul_le_mul_of_nonneg_right (le_abs_self C') (by positivity)
          _ ≤ |C'| * (2 * (k : ℝ)) ^ (D + 1) :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _) (abs_nonneg C')
      calc smallSectionCount (IsSmallH (mCoordIdeal y) y A') (chartLatNm y A'.a) k
          ≤ |C'| * (2 * (k : ℝ)) ^ (D + 1) := (hC' k).trans h2
        _ = |C'| * 2 ^ (D + 1) * ((D + 1).factorial : ℝ) *
              ((k : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
            rw [mul_pow]; field_simp

  refine le_of_forall_pos_lt_add fun η hη => ?_
  have hδ0 : 0 < η / (|c| + 1) := by positivity
  have hcη : c * (η / (|c| + 1)) < η := by
    calc c * (η / (|c| + 1)) ≤ |c| * (η / (|c| + 1)) := mul_le_mul_of_nonneg_right (le_abs_self c) hδ0.le
      _ < (|c| + 1) * (η / (|c| + 1)) := mul_lt_mul_of_pos_right (by linarith) hδ0
      _ = η := by field_simp
  linarith [hδ _ hδ0]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
