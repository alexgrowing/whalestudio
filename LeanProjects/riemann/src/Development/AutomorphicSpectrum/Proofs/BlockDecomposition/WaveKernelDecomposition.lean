import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelExistence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EventuallyEqOfAgreeGLs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqSumOfKernel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InnerIntegralLeft
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionOrthCptZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveCptBoundedTime
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorPairingAdjointStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WavePairingTimeSymmetryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterOperatorPreservesWaveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterOperatorCommutesIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelActionEquivariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelAdjointRegularStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveTimeAverageIsWaveStatement

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.KerAdj

variable {n : ℕ}

theorem cpt_zOp (hL : LgFacts) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (w : List (Bool × ℕ)) {f : Mat n → V} (hf : Cpt f) : Cpt (zOp w f) := by
  obtain ⟨R, hR⟩ := hf
  refine ⟨R, fun y hy hlt => ?_⟩
  have hO : IsOpen (GLs n ∩ lg ⁻¹' Set.Ioi R) :=
    (hL n).2.2.2.1.continuousOn.isOpen_inter_preimage (GlobalTheory.CompanionTheory.WaveKer.isOpen_GLs n) isOpen_Ioi
  have h0 : f =ᶠ[𝓝 y] 0 := by
    filter_upwards [hO.mem_nhds ⟨hy, hlt⟩] with x hx
    exact hR x hx.1 hx.2
  exact (GlobalTheory.CompanionTheory.WaveKer.zOp_germ w h0).self_of_nhds

theorem cont_val {W : Type} [TopologicalSpace W] {φ : Mat n → W} (hφ : ContinuousOn φ (GLs n)) :
    Continuous fun y : G n => φ y.val :=
  hφ.comp_continuous Units.continuous_val PairAdj.val_mem_GLs

section Pair

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

theorem pair_integrable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (hL : LgFacts) {a b : Mat n → V} (ha : ContinuousOn a (GLs n))
    (hb : ContinuousOn b (GLs n)) (cb : Cpt b) :
    Integrable (fun y : G n => ⟪a y.val, b y.val⟫_ℂ) μ := by
  obtain ⟨R, hR⟩ := cb
  refine Continuous.integrable_of_hasCompactSupport ((cont_val ha).inner (cont_val hb)) ?_
  refine HasCompactSupport.intro ((hL n).2.2.2.2.1 R) fun y hy => ?_
  simp [hR _ (PairAdj.val_mem_GLs y) (not_le.1 hy)]

theorem pair_avg {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    (hL : LgFacts) {a : Mat n → V} {W : ℝ → Mat n → V} {g : ℝ → ℝ} {T : ℝ}
    (ha : ContinuousOn a (GLs n)) (ca : Cpt a)
    (hW : ContinuousOn (Function.uncurry W) (Set.univ ×ˢ GLs n)) (hg : IsBump g T) :
    ∫ y : G n, ⟪a y.val, ∫ t, (g t : ℂ) • W t y.val⟫_ℂ ∂μ
      = ∫ t, (g t : ℂ) * ∫ y : G n, ⟪a y.val, W t y.val⟫_ℂ ∂μ := by
  have hc : ∀ R, IsCompact {y : G n | lg y.val ≤ R} := (hL n).2.2.2.2.1
  haveI : SigmaFinite μ := ⟨⟨⟨fun m : ℕ => {y : G n | lg y.val ≤ m}, fun _ => trivial,
    fun m => (hc m).measure_lt_top,
    Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 (exists_nat_ge (lg y.val))⟩⟩⟩
  obtain ⟨R, hR⟩ := ca
  have hgc : Continuous fun t : ℝ => (g t : ℂ) := Complex.continuous_ofReal.comp hg.1.continuous
  have hWc : Continuous fun p : G n × ℝ => W p.2 p.1.val := by
    have h1 : Continuous fun p : G n × ℝ => ((p.2, p.1.val) : ℝ × Mat n) :=
      continuous_snd.prodMk (Units.continuous_val.comp continuous_fst)
    exact hW.comp_continuous h1 (fun p => ⟨Set.mem_univ _, PairAdj.val_mem_GLs _⟩)
  have hgz : ∀ t, t ∉ Set.Icc (-T) T → (g t : ℂ) = 0 := by
    intro t ht
    have h1 : T < |t| := by
      by_contra h
      exact ht (abs_le.1 (not_lt.1 h))
    simp [hg.2.2 t h1]
  have i1 : ∀ y : G n, Integrable (fun t => (g t : ℂ) • W t y.val) volume := by
    intro y
    refine Continuous.integrable_of_hasCompactSupport
      (hgc.smul (hWc.comp (Continuous.prodMk_right y))) ?_
    refine HasCompactSupport.intro (isCompact_Icc (a := -T) (b := T)) fun t ht => ?_
    simp [hgz t ht]
  have j : Integrable (Function.uncurry fun (y : G n) (t : ℝ) =>
      ⟪a y.val, (g t : ℂ) • W t y.val⟫_ℂ) (μ.prod volume) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((cont_val ha).comp continuous_fst).inner ((hgc.comp continuous_snd).smul hWc)
    · refine HasCompactSupport.intro ((hc R).prod (isCompact_Icc (a := -T) (b := T))) fun p hp => ?_
      by_cases h1 : lg p.1.val ≤ R
      · have h2 : p.2 ∉ Set.Icc (-T) T := fun h2 => hp ⟨h1, h2⟩
        simp [Function.uncurry, hgz _ h2]
      · simp [Function.uncurry, hR _ (PairAdj.val_mem_GLs p.1) (not_le.1 h1)]
  calc _ = ∫ y : G n, ∫ t, ⟪a y.val, (g t : ℂ) • W t y.val⟫_ℂ ∂volume ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        exact (integral_inner (i1 y) (a y.val)).symm
    _ = ∫ t, ∫ y : G n, ⟪a y.val, (g t : ℂ) • W t y.val⟫_ℂ ∂μ ∂volume :=
        integral_integral_swap j
    _ = _ := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        simp only [inner_smul_right]
        exact integral_const_mul _ _

end Pair

section Chain

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]

theorem term_eq (hL : LgFacts) (hR : RCalc) (hS : WaveSpeed) {E : KMod n}
    {w' : List (Bool × ℕ)} {g : ℝ → ℝ} {T : ℝ} {K' : Mat n → (E.V →L[ℂ] E.V)}
    (hb : IsBump g T) (hK : IsKer μ E w' g K') {f h : Mat n → E.V} {u v : ℝ → Mat n → E.V}
    (hu : IsWave E u) (hv : IsWave E v) (hu0 : ∀ y ∈ GLs n, u 0 y = f y)
    (hv0 : ∀ y ∈ GLs n, v 0 y = h y) (cf : Cpt f) (ch : Cpt h) :
    ∫ y : G n, ⟪zOp w' f y.val, ∫ t, (g t : ℂ) • v t y.val⟫_ℂ ∂μ
      = ∫ y : G n, ⟪act μ E K' f y.val, h y.val⟫_ℂ ∂μ := by
  haveI := FiniteDimensional.complete ℂ E.V
  have hui : IsWave E (fun t => zOp w' (u t)) := GlobalTheory.T.center_operator_preserves_wave hR n E u w' hu
  have cu0 : Cpt (u 0) := by
    obtain ⟨R, hR'⟩ := cf
    exact ⟨R, fun y hy hl => by rw [hu0 y hy]; exact hR' y hy hl⟩
  have cv0 : Cpt (v 0) := by
    obtain ⟨R, hR'⟩ := ch
    exact ⟨R, fun y hy hl => by rw [hv0 y hy]; exact hR' y hy hl⟩
  have cui0 : Cpt ((fun t => zOp w' (u t)) 0) := cpt_zOp hL w' cu0
  have c1 : ContinuousOn ((fun t => zOp w' (u t)) 0) (GLs n) := (hui.2.1 0).1.continuousOn
  have c2 : ContinuousOn (v 0) (GLs n) := (hv.2.1 0).1.continuousOn
  have L : ∫ y : G n, ⟪zOp w' f y.val, ∫ t, (g t : ℂ) • v t y.val⟫_ℂ ∂μ
      = ∫ t, (g t : ℂ) * ∫ y : G n, ⟪zOp w' (u t) y.val, v 0 y.val⟫_ℂ ∂μ := by
    calc _ = ∫ y : G n, ⟪zOp w' (u 0) y.val, ∫ t, (g t : ℂ) • v t y.val⟫_ℂ ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          simp only
          rw [zOp_agree_GLs n w' (u 0) f hu0 _ (PairAdj.val_mem_GLs y)]
      _ = ∫ t, (g t : ℂ) * ∫ y : G n, ⟪zOp w' (u 0) y.val, v t y.val⟫_ℂ ∂μ :=
          pair_avg μ hL c1 cui0 hv.1.continuousOn hb
      _ = _ := by
          refine integral_congr_ae (Eventually.of_forall fun t => ?_)
          simp only
          rw [GlobalTheory.T.wave_pairing_time_symmetry hL hR hS n μ E _ v hui hv cui0 cv0 t]
  have Rr : ∫ y : G n, ⟪act μ E K' f y.val, h y.val⟫_ℂ ∂μ
      = ∫ t, (g t : ℂ) * ∫ y : G n, ⟪zOp w' (u t) y.val, v 0 y.val⟫_ℂ ∂μ := by
    have hF := pair_avg μ hL c2 cv0 hui.1.continuousOn hb
    calc _ = ∫ y : G n, ⟪∫ t, (g t : ℂ) • zOp w' (u t) y.val, v 0 y.val⟫_ℂ ∂μ := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          have hy := PairAdj.val_mem_GLs y
          have e1 : act μ E K' f y.val = act μ E K' (u 0) y.val := by
            simp only [act]
            refine integral_congr_ae (Eventually.of_forall fun z => ?_)
            simp only
            rw [hu0 _ (GlobalTheory.CompanionTheory.WaveKer.mul_mem_GLs hy (PairAdj.val_mem_GLs z))]
          simp only
          rw [e1, hK.2.2.2 u hu _ hy, GlobalTheory.T.center_operator_commutes_integral n u g T w' hu.1 hb _ hy, hv0 _ hy]
      _ = conj (∫ y : G n, ⟪v 0 y.val, ∫ t, (g t : ℂ) • zOp w' (u t) y.val⟫_ℂ ∂μ) := by
          rw [← integral_conj]
          simp only [inner_conj_symm]
      _ = conj (∫ t, (g t : ℂ) * ∫ y : G n, ⟪v 0 y.val, zOp w' (u t) y.val⟫_ℂ ∂μ) := by
          rw [hF]
      _ = _ := by
          rw [← integral_conj]
          refine integral_congr_ae (Eventually.of_forall fun t => ?_)
          simp only
          rw [map_mul, Complex.conj_ofReal, ← integral_conj]
          simp only [inner_conj_symm]
  rw [L, Rr]

theorem chain (hL : LgFacts) (hU : Unimod) (hR : RCalc) (hS : WaveSpeed) (hE : WaveEx) {E : KMod n}
    {w : List (Bool × ℕ)} {g : ℝ → ℝ} {T : ℝ} {k : Mat n → (E.V →L[ℂ] E.V)}
    (hb : IsBump g T) (hk : IsKer μ E w g k) {N : ℕ} {c : Fin N → ℂ}
    {w₁ : Fin N → List (Bool × ℕ)} {K : Fin N → Mat n → (E.V →L[ℂ] E.V)}
    (hw : ∀ a b : Mat n → E.V, ContDiffOn ℝ ∞ a (GLs n) → ContDiffOn ℝ ∞ b (GLs n) → Cpt a → Cpt b →
      ∫ y : G n, ⟪zOp w a y.val, b y.val⟫_ℂ ∂μ = ∑ i, c i * ∫ y : G n, ⟪a y.val, zOp (w₁ i) b y.val⟫_ℂ ∂μ)
    (hK : ∀ i, IsKer μ E (w₁ i) g (K i)) {f h : Mat n → E.V} (hf : f ∈ CE E) (cf : Cpt f)
    (hh : h ∈ CE E) (ch : Cpt h) :
    (haveI := FiniteDimensional.complete ℂ E.V
     ∫ y : G n, ⟪act μ E (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) f y.val, h y.val⟫_ℂ ∂μ
      = ∑ i, conj (c i) * ∫ y : G n, ⟪act μ E (K i) f y.val, h y.val⟫_ℂ ∂μ) := by
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨u, hu, hu0⟩ := hE n E f hf
  obtain ⟨v, hv, hv0⟩ := hE n E h hh
  have hHs : ContDiffOn ℝ ∞ (fun x => ∫ t, (g t : ℂ) • v t x) (GLs n) := by
    have h1 := ((GlobalTheory.T.wave_time_average_is_wave hS n E v g T hv hb).2.1 0).1
    simpa only [zero_add] using h1
  have cv0 : Cpt (v 0) := by
    obtain ⟨R, hR'⟩ := ch
    exact ⟨R, fun y hy hl => by rw [hv0 y hy]; exact hR' y hy hl⟩
  have cH : Cpt (fun x => ∫ t, (g t : ℂ) • v t x) := by
    obtain ⟨R, hRv⟩ := wave_cpt_bounded_time hL hS n E v hv cv0 T
    refine ⟨R, fun y hy hl => ?_⟩
    have h0 : ∀ t, (g t : ℂ) • v t y = 0 := by
      intro t
      by_cases ht : |t| ≤ T
      · rw [hRv t ht y hy hl, smul_zero]
      · rw [hb.2.2 t (not_le.1 ht)]
        simp
    simp [h0]
  have e1 := PairAdj.pairAdj hL hU n μ E k f h ⟨hk.1.continuousOn, hk.2.1⟩ hf.1.continuousOn
    hh.1.continuousOn cf ch
  have e2 : ∫ y : G n, ⟪f y.val, act μ E k h y.val⟫_ℂ ∂μ
      = ∫ y : G n, ⟪f y.val, zOp w (fun x => ∫ t, (g t : ℂ) • v t x) y.val⟫_ℂ ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have hy := PairAdj.val_mem_GLs y
    have e : act μ E k h y.val = act μ E k (v 0) y.val := by
      simp only [act]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only
      rw [hv0 _ (GlobalTheory.CompanionTheory.WaveKer.mul_mem_GLs hy (PairAdj.val_mem_GLs z))]
    simp only
    rw [e, hk.2.2.2 v hv _ hy]
  have e3 : ∫ y : G n, ⟪f y.val, zOp w (fun x => ∫ t, (g t : ℂ) • v t x) y.val⟫_ℂ ∂μ
      = conj (∫ y : G n, ⟪zOp w (fun x => ∫ t, (g t : ℂ) • v t x) y.val, f y.val⟫_ℂ ∂μ) := by
    rw [← integral_conj]
    simp only [inner_conj_symm]
  rw [e1, e2, e3, hw _ f hHs hf.1 cH cf, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← term_eq μ hL hR hS hb (hK i) hu hv hu0 hv0 cf ch, ← integral_conj]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [inner_conj_symm]

end Chain

theorem kernel_adjoint : LgFacts → Unimod → RCalc → WaveSpeed → WaveEx → KerUniq → KerOne → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (w : List (Bool × ℕ)) (g : ℝ → ℝ) (T : ℝ) (k : Mat n → (E.V →L[ℂ] E.V)), IsBump g T → IsKer μ E w g k → ∃ (N : ℕ) (c : Fin N → ℂ) (w₁ : Fin N → List (Bool × ℕ)) (K : Fin N → Mat n → (E.V →L[ℂ] E.V)), (∀ i, IsKer μ E (w₁ i) g (K i)) ∧ (haveI := FiniteDimensional.complete ℂ E.V; ∀ y ∈ GLs n, ContinuousLinearMap.adjoint (k y⁻¹) = ∑ i, c i • K i y) ∧ ∀ χ : Inf n, IsHerm χ → conj (zVal w χ) = ∑ i, c i * zVal (w₁ i) χ := by
  intro hL hU hR hS hE hQ hO n _ _ μ _ E w g T k hb hk
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨N, c, w₁, hval, hop⟩ := GlobalTheory.T.gelfand_operator_pairing_adjoint n w
  choose K hK using fun i => hO n μ E (w₁ i) g T hb
  refine ⟨N, c, w₁, K, hK, ?_, hval⟩
  have hw := hop hL hR μ E.V
  obtain ⟨regp, eqvp⟩ := GlobalTheory.T.kernel_adjoint_regular hL n E k ⟨hk.1.continuousOn, hk.2.1⟩ hk.2.2.1
  have regK : ∀ i, KReg (K i) := fun i => ⟨(hK i).1.continuousOn, (hK i).2.1⟩
  have rp : ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ,
      ContinuousLinearMap.adjoint (k (y * k₂.1)⁻¹) = ContinuousLinearMap.adjoint (k y⁻¹) * E.ρ k₂ := by
    intro y hy k₂
    simpa using eqvp y hy 1 k₂
  have lp : ∀ y ∈ GLs n, ∀ k₁ : Matrix.unitaryGroup (Fin n) ℂ,
      ContinuousLinearMap.adjoint (k (k₁.1 * y)⁻¹) = E.ρ k₁ * ContinuousLinearMap.adjoint (k y⁻¹) := by
    intro y hy k₁
    simpa using eqvp y hy k₁ 1
  have rK : ∀ i, ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, K i (y * k₂.1) = K i y * E.ρ k₂ := by
    intro i y hy k₂
    simpa using (hK i).2.2.1 y hy 1 k₂
  have lK : ∀ i, ∀ y ∈ GLs n, ∀ k₁ : Matrix.unitaryGroup (Fin n) ℂ, K i (k₁.1 * y) = E.ρ k₁ * K i y := by
    intro i y hy k₁
    simpa using (hK i).2.2.1 y hy k₁ 1
  have hD : ∀ y ∈ GLs n, ContinuousLinearMap.adjoint (k y⁻¹) - ∑ i, c i • K i y = 0 := by
    refine hQ n μ E (fun y => ContinuousLinearMap.adjoint (k y⁻¹) - ∑ i, c i • K i y) (GLs n)
      (GlobalTheory.CompanionTheory.WaveKer.isOpen_GLs n) subset_rfl
      (fun y hy k₂ => GlobalTheory.CompanionTheory.WaveKer.mul_mem_GLs hy (GlobalTheory.CompanionTheory.WaveKer.unitary_mem_GLs k₂)) ?_ ?_ ?_
    · exact regp.1.sub (continuousOn_finset_sum _ fun i _ => (regK i).1.const_smul (c i))
    · intro y hy k₂
      simp only [rp y hy k₂, rK _ y hy k₂, sub_mul, Finset.sum_mul, smul_mul_assoc]
    · intro f hf cf _
      have hfc := hf.1.continuousOn
      have ap := GlobalTheory.T.kernel_action_equivariant hL n μ E _ f regp hfc lp
      have aK := fun i => GlobalTheory.T.kernel_action_equivariant hL n μ E (K i) f (regK i) hfc (lK i)
      have hA0 := section_orth_cpt_zero hQ n μ E
        (fun x => act μ E (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) f x - ∑ i, c i • act μ E (K i) f x)
        (ap.1.sub (continuousOn_finset_sum _ fun i _ => (aK i).1.const_smul (c i)))
        (by
          intro y hy k₂
          simp only [ap.2 y hy k₂, (aK _).2 y hy k₂, map_sub, map_sum, map_smul])
        (by
          intro h hh ch
          have int1 := pair_integrable μ hL ap.1 hh.1.continuousOn ch
          have int2 := fun i => (pair_integrable μ hL (aK i).1 hh.1.continuousOn ch).const_mul (conj (c i))
          have hpt : ∀ y : G n, ⟪act μ E (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) f y.val - ∑ i, c i • act μ E (K i) f y.val, h y.val⟫_ℂ
              = ⟪act μ E (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) f y.val, h y.val⟫_ℂ
                - ∑ i, conj (c i) * ⟪act μ E (K i) f y.val, h y.val⟫_ℂ := by
            intro y
            simp only [inner_sub_left, sum_inner, inner_smul_left]
          simp only [hpt]
          rw [integral_sub int1 (integrable_finset_sum _ fun i _ => int2 i),
            integral_finset_sum _ fun i _ => int2 i]
          simp only [integral_const_mul]
          rw [chain μ hL hU hR hS hE hb hk hw hK hf cf hh ch, sub_self])
      have h1 := hA0 1 (GlobalTheory.CompanionTheory.WaveKer.one_mem_GLs n)
      have h2 := act_eq_sum_of_kernel hL n μ E (ι := Option (Fin N))
        (fun o => o.elim 1 fun i => -c i)
        (fun o => o.elim (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) K)
        (fun y => ContinuousLinearMap.adjoint (k y⁻¹) - ∑ i, c i • K i y) f
        (by rintro (_ | i); exacts [regp, regK i])
        (by intro y _; simp [Fintype.sum_option, sub_eq_add_neg])
        hfc 1 (GlobalTheory.CompanionTheory.WaveKer.one_mem_GLs n)
      rw [h2]
      simpa [Fintype.sum_option, sub_eq_add_neg] using h1
  intro y hy
  exact sub_eq_zero.1 (hD y hy)

end GlobalTheory.CompanionTheory.WaveMult.KerAdj
