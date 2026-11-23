import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightLowerBoundChartNorm
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsVerticalBound
import Development.WeilBound.CoreStatements.AmpleLineBundles.PtsIntegralMap

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

noncomputable section

namespace CoverDenseAlt.HtF

open CoverDenseAlt.Rename₂
open GroundTheory.Heights₂.Heights (blockIdx flatCone unflatCone Cone BlockNonzero orbitIdeal coordField coordVec height
  blockNonzero_unflatCone_iff chartMonomial)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def stdLine (m : K → ℕ) : HermLine ι where
  a k := ((2 * m k : ℕ) : ℤ)
  h z := ∏ k, (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ m k
  pos z hz := Finset.prod_pos fun k _ => pow_pos (by
    obtain ⟨i, hi⟩ := hz k
    exact Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hi) 2⟩) _
  smul c z _ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [norm_mul, mul_pow, zpow_natCast]
    rw [← Finset.mul_sum, mul_pow, pow_mul]

theorem stdLine_smooth (m : K → ℕ) : IsSmoothHerm (stdLine (ι := ι) m) := by
  refine ContDiff.contDiffOn ?_
  refine contDiff_prod fun k _ => ContDiff.pow (ContDiff.sum fun i _ => ?_) _
  exact (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ (⟨k, i⟩ : Σ k, ι k))

theorem tensor_smooth {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) := ContDiffOn.mul hA hB

theorem lineHt_tensor (A B : HermLine ι) (L : Type) [Field L] [NumberField L] (w : (Σ k, ι k) → L)
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) : lineHt (A.tensor B) L w = lineHt A L w + lineHt B L w := by
  have hA := SecLow.support_finite w hw fun k => (A.a k : ℝ)
  have hB := SecLow.support_finite w hw fun k => (B.a k : ℝ)
  have hfin : (∑ᶠ v : FinitePlace L, ∑ k, ((A.tensor B).a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))) =
      (∑ᶠ v : FinitePlace L, ∑ k, (A.a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))) +
      ∑ᶠ v : FinitePlace L, ∑ k, (B.a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩)) := by
    rw [← finsum_add_distrib hA hB]
    refine finsum_congr fun v => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [HermLine.tensor, Pi.add_apply, Int.cast_add]
    ring
  have hinf : (∑ σ : L →+* ℂ, Real.log ((A.tensor B).h fun p => σ (w p))) =
      (∑ σ : L →+* ℂ, Real.log (A.h fun p => σ (w p))) + ∑ σ : L →+* ℂ, Real.log (B.h fun p => σ (w p)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hz : ∀ k, ∃ i, (fun p => σ (w p)) ⟨k, i⟩ ≠ 0 := fun k =>
      let ⟨i, hi⟩ := hw k; ⟨i, (map_ne_zero σ).2 hi⟩
    exact Real.log_mul (A.pos _ hz).ne' (B.pos _ hz).ne'
  unfold lineHt ptHt
  beta_reduce
  rw [hfin, hinf]
  ring

variable [DecidableEq K] {n : K → ℕ} (e : ∀ k, ι k ≃ blockIdx n k)

def toNum (A : HermLine ι) (hA : IsSmoothHerm A) : GroundTheory.Heights₂.Heights.HermLine n where
  deg := A.a
  metric z := A.h (pull e (flatCone z))
  metric_pos z hz := A.pos _ ((nz_pull e _).2 ((blockNonzero_unflatCone_iff (flatCone z)).1 hz))
  metric_smul c z hc _ := A.smul c (pull e (flatCone z)) hc
  metric_smooth := by
    have hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Cone n ℂ => pull e (flatCone z)) :=
      contDiff_pi.2 fun p => contDiff_pi.1 (contDiff_pi.1 contDiff_id p.1) (e p.1 p.2)
    exact ContDiffOn.comp hA hu.contDiffOn fun z hz =>
      (nz_pull e _).2 ((blockNonzero_unflatCone_iff (flatCone z)).1 hz)

theorem height_toNum (A : HermLine ι) (hA : IsSmoothHerm A) (x : Cone n (AlgebraicClosure ℚ)) :
    height (toNum e A hA) x = lineHt A (coordField x) (pull e (flatCone (coordVec x))) := by
  have h : ∀ (v : FinitePlace (coordField x)) (k : K),
      (⨆ i, v (coordVec x k i)) = ⨆ i, v (pull e (flatCone (coordVec x)) ⟨k, i⟩) :=
    fun v k => ((e k).iSup_comp (g := fun i => v (coordVec x k i))).symm
  unfold height lineHt ptHt
  simp only [h]
  rfl

omit [DecidableEq K] in
theorem coordIdeal_eq (x : Cone n (AlgebraicClosure ℚ)) (f : MRing ι) :
    f ∈ mCoordIdeal (pull e (flatCone (coordVec x))) ↔ ren e f ∈ orbitIdeal x := by
  classical
  have key : (MvPolynomial.map (algebraMap (coordField x) (AlgebraicClosure ℚ))).comp
      (mConeMap (pull e (flatCone (coordVec x)))).toRingHom =
      (mConeMap (flatCone x)).toRingHom.comp (ren e).toRingHom := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => ?_
    simp [mConeMap, ren, pull, flatCone, coordVec]
  have hf : MvPolynomial.map (algebraMap (coordField x) (AlgebraicClosure ℚ))
      (mConeMap (pull e (flatCone (coordVec x))) f) = mConeMap (flatCone x) (ren e f) :=
    RingHom.congr_fun key f
  simp only [mCoordIdeal, orbitIdeal, RingHom.mem_ker]
  constructor
  · intro h
    rw [← hf, h, map_zero]
  · intro h
    refine MvPolynomial.map_injective _ (algebraMap (coordField x) (AlgebraicClosure ℚ)).injective ?_
    rw [hf, h, map_zero]

end CoverDenseAlt.HtF

open CoverDenseAlt.Rename₂ CoverDenseAlt.HtF in
open GroundTheory.Heights₂.Heights (blockIdx flatCone unflatCone Cone BlockNonzero orbitIdeal coordField coordVec height
  blockNonzero_unflatCone_iff chartMonomial) in
theorem CoverDenseAlt.intersection_number_eq_line_height : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (II : IntersectionSystem), IsIntersectionSystem II → ∀ W : Ideal (MRing ι), IsArithVar W 1 → ∃ (L : Type) (_ : Field L) (_ : NumberField L) (w : (Σ k, ι k) → L), W = mCoordIdeal w ∧ w ∈ ptsOver L W ∧ ∀ A : HermLine ι, IsSmoothHerm A → II K ι W 1 ![A] / (degC W : ℝ) = lineHt A L w := by
  intro K _ ι _ II hII W hW
  classical
  obtain ⟨hK, ⟨-, hhomW, hrelW⟩, -, -⟩ := id hW
  haveI := hK
  obtain ⟨-, hadd, hrec⟩ : IsIntersectionFamily (II K ι) := hII K ι
  have hne : ∀ k, Nonempty (ι k) := fun k => let ⟨i, _⟩ := hrelW k; ⟨i⟩
  obtain ⟨n, hn⟩ : ∃ n : K → ℕ, ∀ k, Fintype.card (ι k) = n k + 1 :=
    ⟨fun k => Fintype.card (ι k) - 1, fun k => by
      have := Fintype.card_pos_iff.2 (hne k)
      show Fintype.card (ι k) = Fintype.card (ι k) - 1 + 1
      omega⟩
  obtain ⟨e⟩ : Nonempty (∀ k, ι k ≃ blockIdx n k) :=
    ⟨fun k => (Fintype.equivFin (ι k)).trans (finCongr (hn k))⟩
  obtain ⟨x, hx, hWx⟩ := GroundTheory.Heights₂.Heights.CurveIsOrbit.full K n (Ideal.map (ren e) W) (arithVar_map e hW)
  have hxc : ∀ k, ∃ i, x k i ≠ 0 := fun k => by
    by_contra h
    push_neg at h
    exact hx k (funext h)
  choose c hc using hxc
  have hdeg : degC W = degC (orbitIdeal x) := by rw [← hWx, degC_map]
  have hdpos : 0 < degC W := hdeg ▸ GroundTheory.Heights₂.Heights.OrbitDegree.full K n x hx
  have hfin : Finite (GroundTheory.Heights₂.Heights.projPts W) :=
    Nat.finite_of_card_ne_zero (by rw [← GroundTheory.Heights₂.Heights.degC_eq_card_projPts]; omega)
  have hWeq : W = mCoordIdeal (pull e (flatCone (coordVec x))) := by
    ext f
    rw [coordIdeal_eq e x f, ← hWx]
    constructor
    · exact fun h => Ideal.mem_map_of_mem _ h
    · intro h
      rw [Ideal.mem_map_of_equiv] at h
      obtain ⟨g, hg, hge⟩ := h
      rwa [← (ren e).injective hge]
  have hwnz : ∀ k, ∃ i, pull e (flatCone (coordVec x)) ⟨k, i⟩ ≠ 0 := fun k =>
    ⟨(e k).symm (c k), fun h => hc k (by
      have h' := congrArg (fun y : coordField x => (y : AlgebraicClosure ℚ)) h
      simpa [pull, flatCone, coordVec] using h')⟩
  have hsnoc : ∀ B : HermLine ι, (Fin.snoc (Fin.elim0 : Fin 0 → HermLine ι) B : Fin 1 → HermLine ι) = ![B] :=
    fun B => by
      funext i
      fin_cases i
      rfl
  have key : ∀ A : HermLine ι, IsSmoothHerm A → ∀ a : K → ℕ, (∀ k, A.a k = a k) →
      II K ι W 1 ![A] = degC W * lineHt A (coordField x) (pull e (flatCone (coordVec x))) := by
    intro A hA a ha
    have hsec : IsSectionOn (orbitIdeal x) (toNum e A hA).toGeo (chartMonomial c a) :=
      GroundTheory.Heights₂.Heights.isSectionOn_chartMonomial (toNum e A hA) x c hc a ha
    obtain ⟨a0, ha0, hhom', hnot'⟩ := id hsec
    obtain ⟨s, hsdef⟩ : ∃ s : MRing ι, s = ren (fun k => (e k).symm) (chartMonomial c a) := ⟨_, rfl⟩
    have hid : (⇑(Equiv.sigmaCongrRight e) ∘ ⇑(Equiv.sigmaCongrRight fun k => (e k).symm)) = id :=
      funext fun p => by simp
    have hs : ren e s = chartMonomial c a := by
      rw [hsdef, ren_apply, ren_apply, rename_rename, hid, rename_id]
      rfl
    have hsW : s ∉ W := by
      intro hmem
      apply hnot'
      rw [← hWx, ← hs]
      exact Ideal.mem_map_of_mem _ hmem
    have hhom : IsMultiHomog s a0 := by
      rw [hsdef]
      exact homog_ren _ hhom'
    have h0 : II K ι W 1 ![A] = recR (II K ι) W Fin.elim0 A s := by
      have := hrec W 0 Fin.elim0 A s a0 hW (fun j => j.elim0) hA ha0 hhom hsW
      simpa only [hsnoc] using this
    have h1 : ∀ (c' : K → ℂ) (z : (k : K) × blockIdx n k → ℂ), (∀ k, c' k ≠ 0) →
        z ∈ mcPts (Ideal.map (ren e) W) →
        (logNorm (toNum e A hA).toGeo (ren e s) fun p => c' p.fst * z p) =
          logNorm (toNum e A hA).toGeo (ren e s) z := by
      intro c' z hc' _
      rw [hs]
      unfold logNorm
      have hprod : (∏ k, ‖c' k‖ ^ ((toNum e A hA).toGeo.a k)) = ∏ k, ‖c' k‖ ^ a0 k :=
        Finset.prod_congr rfl fun k _ => by rw [ha0 k, zpow_natCast]
      have hpos : (∏ k, ‖c' k‖ ^ a0 k) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hc' k))
      rw [GroundTheory.Heights₂.Heights.eval_smul_of_isMultiHomog _ a0 hhom' c' z,
        (toNum e A hA).toGeo.smul c' z hc', hprod, norm_mul, norm_prod]
      simp only [norm_pow]
      rw [mul_div_mul_left _ _ hpos]
    have h2 : ∀ z : (k : K) × blockIdx n k → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
        (toNum e A hA).toGeo.h z = A.h (pull e z) := by
      intro z hz
      rw [GroundTheory.Heights₂.Heights.HermLine.toGeo_h_of_blockNonzero (toNum e A hA)
        ((blockNonzero_unflatCone_iff z).2 hz)]
      rfl
    have h3 : ∀ V ∈ divSupp (Ideal.map (ren e) W) (ren e s), ¬IsHorizontal V := by
      intro V hV
      rw [hs, hWx] at hV
      exact GroundTheory.Heights₂.Heights.OrbitDivVertical.proof K n (toNum e A hA) x _ hx hsec V hV
    have h4 : ∀ V ∈ divSupp (Ideal.map (ren e) W) (ren e s), ∀ (c1 c2 : (k : K) → blockIdx n k),
        (∀ k, X ⟨k, c1 k⟩ ∉ V) → (∀ k, X ⟨k, c2 k⟩ ∉ V) →
        Nonempty (MRing (blockIdx n) ⧸ chartId V c1 ≃+* MRing (blockIdx n) ⧸ chartId V c2) := by
      intro V hV c1 c2 hc1 hc2
      rw [hs, hWx] at hV
      exact (CoverDenseAlt.chartDehom_full K n (toNum e A hA) x _ hx hsec V hV c1 c2 hc1 hc2).2
    rw [h0, ← recR_map e (II K ι) (II K (blockIdx n)) W hhomW hfin A (toNum e A hA).toGeo s h1 h2 h3 h4,
      hs, hWx, CoverDenseAlt.heightRecR_full K n (II K (blockIdx n)) (toNum e A hA) x _ hx hsec,
      height_toNum e A hA x, hdeg]
  refine ⟨coordField x, inferInstance, inferInstance, pull e (flatCone (coordVec x)), hWeq, ⟨hwnz, ?_⟩, ?_⟩
  · intro f hf
    have hf' : f ∈ mCoordIdeal (pull e (flatCone (coordVec x))) := hWeq ▸ hf
    have h0 : mConeMap (pull e (flatCone (coordVec x))) f = 0 := RingHom.mem_ker.1 hf'
    have key2 : (MvPolynomial.eval (fun _ : K => (1 : coordField x))).comp
        (mConeMap (pull e (flatCone (coordVec x)))).toRingHom =
        (aeval (pull e (flatCone (coordVec x)))).toRingHom :=
      MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => by simp [mConeMap]
    have h2 : MvPolynomial.eval (fun _ : K => (1 : coordField x)) (mConeMap (pull e (flatCone (coordVec x))) f) =
        aeval (pull e (flatCone (coordVec x))) f := RingHom.congr_fun key2 f
    have h3 : MvPolynomial.eval (fun _ : K => (1 : coordField x)) (mConeMap (pull e (flatCone (coordVec x))) f) = 0 := by
      rw [h0, map_zero]
    exact h2.symm.trans h3
  · intro A hA
    obtain ⟨m, hm⟩ : ∃ m : K → ℕ, m = fun k => (A.a k).natAbs := ⟨_, rfl⟩
    have hS : IsSmoothHerm (stdLine (ι := ι) m) := stdLine_smooth m
    have hAS : IsSmoothHerm (A.tensor (stdLine m)) := tensor_smooth hA hS
    have hnn : ∀ k, 0 ≤ A.a k + ((2 * m k : ℕ) : ℤ) := fun k => by
      rw [hm]
      push_cast
      linarith [neg_abs_le (A.a k), abs_nonneg (A.a k)]
    have e1 := key (A.tensor (stdLine m)) hAS (fun k => (A.a k + ((2 * m k : ℕ) : ℤ)).toNat)
      (fun k => (Int.toNat_of_nonneg (hnn k)).symm)
    have e2 := key (stdLine m) hS (fun k => 2 * m k) (fun k => rfl)
    have hadd' : II K ι W 1 ![A.tensor (stdLine m)] = II K ι W 1 ![A] + II K ι W 1 ![stdLine m] := by
      have := hadd W 0 Fin.elim0 A (stdLine m) hW (fun j => j.elim0) hA hS
      simpa only [hsnoc] using this
    have hl := lineHt_tensor A (stdLine m) (coordField x) (pull e (flatCone (coordVec x))) hwnz
    have hdne : (degC W : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
    rw [div_eq_iff hdne]
    linear_combination e1 - hadd' - e2 + (degC W : ℝ) * hl
