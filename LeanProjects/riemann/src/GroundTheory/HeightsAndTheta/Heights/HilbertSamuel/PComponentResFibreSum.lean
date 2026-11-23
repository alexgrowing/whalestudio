import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PComponentResFibreSumSheet
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartImageNull
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothMetricOfIsSmoothHerm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisorAlt
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PMinimalPrimeMultiHomog
import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeC
import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace ComponentResBridge

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (Res logH)

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}
  (R : Res ι W e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

set_option linter.unusedSectionVars false

theorem isMultiHomogIdeal_of_mem_minimalPrimes {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) :
    IsMultiHomogIdeal W := by
  have hPCh : IsMultiHomogIdeal (P.map (MvPolynomial.map (Int.castRingHom ℂ))) := by
    obtain ⟨T, hT, hPT⟩ := hP.2.1.2.1
    refine ⟨MvPolynomial.map (Int.castRingHom ℂ) '' T, ?_, by rw [hPT, Ideal.map_span]⟩
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨a, ha⟩ := hT f hf
    exact ⟨a, fun d hd k => ha d (MvPolynomial.support_map_subset _ _ hd) k⟩
  exact (GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiHomogIdeal_iff W).mp
    (GroundTheory.Heights₂.Heights.NumbersDVR.MinimalPrimeMultiHomog.proof ℂ K ι _ W
      ((GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiHomogIdeal_iff _).mpr hPCh) hW)

theorem mem_zeroLocus_smul {J : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hJ : IsMultiHomogIdeal J) (c : K → ℂ)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ zeroLocus ℂ J) : (fun q => c q.1 * z q) ∈ zeroLocus ℂ J := by
  intro f hf
  have := ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hJ c z
    (fun g hg => by simpa [MvPolynomial.coe_aeval_eq_eval] using hz g hg) f hf
  simpa [MvPolynomial.coe_aeval_eq_eval] using this

theorem resW_mem_fibre {P : Ideal (MRing ι)} (hP : IsArithVar P (e + 1))
    (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) {x : R.R.M}
    (h0 : Ψ (segre (R.pt x)) 0 ≠ 0) : resW R Ψ x ∈ fibre P Ψ (resProj R Ψ x) := by
  obtain ⟨k0⟩ := hP.1
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre (R.pt x)) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre (R.pt x)) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  refine ⟨fun p => c p.1 * R.pt x p,
    mcPts_smul hP.2.1.2.1 c hc (mem_mcPts_of_conePts hW (pt_mem R x)).1, ?_, ?_⟩
  · rw [segre_smul, hpc]; rfl
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [resW, h0]
    · simp only [resW, map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ, resProj]
      rw [div_eq_inv_mul]

theorem resW_injOn : Set.InjOn (resW R Ψ)
    {x | R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D ∧ Ψ (segre (R.pt x)) 0 ≠ 0} := by
  intro x hx x' hx' hw
  refine R.R.inj _ _ x (R.mem_src_idx x) x' (R.mem_src_idx x') hx.1 ?_
  refine sameOrbit_of_segre (pt_mem R x').1
    (Ψ (segre (R.pt x)) 0 * (Ψ (segre (R.pt x')) 0)⁻¹) (by simp [hx.2, hx'.2]) ?_
  have := congrArg (fun v => Ψ (segre (R.pt x)) 0 • v) hw
  simp only [resW, smul_smul, mul_inv_cancel₀ hx.2, one_smul] at this
  exact this

theorem exists_of_lift {P : Ideal (MRing ι)} {y : Fin e → ℂ} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) (hzW : z ∈ zeroLocus ℂ W) (hzD : z ∉ ReciprocityTheory.AnForm.R.conePts R.D)
    (hΨz : Ψ (segre z) = Fin.cons 1 y) :
    ∃ x, R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D ∧ Ψ (segre (R.pt x)) 0 ≠ 0 ∧
      resProj R Ψ x = y ∧ resW R Ψ x = segre z := by
  have hD : IsMultiHomogIdeal R.D := (GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiHomogIdeal_iff R.D).mp R.homog
  have hzc : z ∈ ReciprocityTheory.AnForm.R.conePts W :=
    ⟨hz.1, fun f hf => by simpa [MvPolynomial.coe_aeval_eq_eval] using hzW f hf⟩
  obtain ⟨i, x, hx, c1, hc1, h1⟩ := R.R.surj z hzc hzD
  obtain ⟨c2, hc2, h2⟩ := R.R.compat i (R.idx x) x ⟨hx, R.mem_src_idx x⟩
  set c : K → ℂ := fun k => c1 k / c2 k with hcdef
  have hc : ∀ k, c k ≠ 0 := fun k => div_ne_zero (hc1 k) (hc2 k)
  have hxc : R.pt x = fun q => c q.1 * z q := by
    funext q
    have e : c2 q.1 * R.pt x q = c1 q.1 * z q := (congrFun h2 q).symm.trans (congrFun h1 q)
    rw [hcdef, div_mul_eq_mul_div, eq_div_iff (hc2 q.1), ← e]
    ring
  have hseg : segre (R.pt x) = (∏ k, c k) • segre z := by rw [hxc, segre_smul]
  have hpc : ∏ k, c k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hΨx : Ψ (segre (R.pt x)) = (∏ k, c k) • Fin.cons 1 y := by rw [hseg, map_smul, hΨz]
  have h0 : Ψ (segre (R.pt x)) 0 = ∏ k, c k := by simp [hΨx]
  refine ⟨x, fun h => hzD ?_, by rw [h0]; exact hpc, ?_, ?_⟩
  · have hz' : z = fun q => (c q.1)⁻¹ * R.pt x q := by
      funext q
      rw [hxc, ← mul_assoc, inv_mul_cancel₀ (hc q.1), one_mul]
    refine ⟨hz.1, ?_⟩
    rw [hz']
    exact ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul hD (fun k => (c k)⁻¹) (R.pt x) h.2
  · funext i
    simp only [resProj, hΨx, h0, Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
    field_simp
  · rw [resW, h0, hseg, smul_smul, inv_mul_cancel₀ hpc, one_smul]

theorem coneD_null (hA : ChartDimLt.Statement) (hB : ChartRatioImageNull.Statement) {P : Ideal (MRing ι)}
    (hP : IsArithVar P (e + 1)) (hW : W ∈ (P.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) :
    volume {y : Fin e → ℂ | ∃ z ∈ zeroLocus ℂ W, z ∈ ReciprocityTheory.AnForm.R.conePts R.D ∧
      Ψ (segre z) = Fin.cons 1 y} = 0 := by
  classical
  set PC : Ideal (MvPolynomial (Σ k, ι k) ℂ) := P.map (MvPolynomial.map (Int.castRingHom ℂ)) with hPC

  have hdimW : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ W) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    set PQ : Ideal (MvPolynomial (Σ k, ι k) ℚ) := P.map (MvPolynomial.map (Int.castRingHom ℚ)) with hPQ
    have hvar := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isProjVarQ_of_isArithVar hP
    have : PQ.IsPrime := hvar.1.isPrime
    have hext : ReciprocityTheory.AnForm.R.extC PQ = PC := by
      rw [ReciprocityTheory.AnForm.R.extC, hPQ, hPC, Ideal.map_map]
      congr 1
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun q => ?_)
      · simp only [RingHom.comp_apply, MvPolynomial.map_C]
        congr 1
      · simp
    rw [← hext] at hW
    rw [ReciprocityTheory.AnForm.R.ringKrullDim_of_mem_minimalPrimes_extC PQ W hW]
    exact hvar.2
  have hWh : IsMultiHomogIdeal W := isMultiHomogIdeal_of_mem_minimalPrimes hP hW
  have hDh : IsMultiHomogIdeal R.D :=
    (GroundTheory.Heights₂.Heights.NumbersDVR.Objects.isMultiHomogIdeal_iff R.D).mp R.homog
  have hsuph : IsMultiHomogIdeal (W ⊔ R.D) := by
    obtain ⟨T, hT, hWT⟩ := hWh
    obtain ⟨T', hT', hDT⟩ := hDh
    exact ⟨T ∪ T', fun f hf => hf.elim (hT f) (hT' f), by rw [Ideal.span_union, ← hWT, ← hDT]⟩

  have hsup : ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ (W ⊔ R.D)) <
      ((e + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    have : W.IsPrime := hW.1.1
    obtain ⟨g, hgD, hgW⟩ : ∃ g ∈ R.D, g ∉ W := by
      by_contra hcon
      push_neg at hcon
      exact R.not_le hcon
    have hg0 : Ideal.Quotient.mk W g ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hg0)
    have eqv : ((MvPolynomial (Σ k, ι k) ℂ ⧸ W) ⧸ Ideal.span {Ideal.Quotient.mk W g}) ≃+*
        MvPolynomial (Σ k, ι k) ℂ ⧸ (W ⊔ Ideal.span {g}) :=
      (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
        (DoubleQuot.quotQuotEquivQuotSup W (Ideal.span {g}))
    rw [ringKrullDim_eq_of_ringEquiv eqv, hdimW] at h1
    have hle : W ⊔ Ideal.span {g} ≤ W ⊔ R.D :=
      sup_le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr hgD) W
    have h2 := ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle)
    generalize ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ (W ⊔ Ideal.span {g})) = a at h1 h2
    generalize ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ (W ⊔ R.D)) = b at h2 ⊢
    refine lt_of_le_of_lt h2 ?_
    induction a using WithBot.recBotCoe with
    | bot => exact WithBot.bot_lt_coe _
    | coe a =>
      induction a using ENat.recTopCoe with
      | top => exact absurd h1 (by exact_mod_cast (show ¬ ((⊤ : ℕ∞) + 1 ≤ ((e + Fintype.card K : ℕ) : ℕ∞)) by simp))
      | coe a =>
        have : a + 1 ≤ e + Fintype.card K := by exact_mod_cast h1
        exact_mod_cast (show a < e + Fintype.card K by omega)

  refine measure_mono_null (t := ⋃ p : (k : K) → ι k,
      {y : Fin e → ℂ | ∃ z ∈ zeroLocus ℂ (ReciprocityTheory.AnForm.R.chartIdeal (W ⊔ R.D) p), Ψ (segre z) 0 ≠ 0 ∧
        (Fin.cons 1 y : Fin (e + 1) → ℂ) = (Ψ (segre z) 0)⁻¹ • Ψ (segre z)}) ?_ ?_
  · rintro y ⟨z, hzW, hzD, hzy⟩
    choose p hp using hzD.1
    simp only [Set.mem_iUnion]
    refine ⟨p, ReciprocityTheory.AnForm.R.affCoord p z, ?_, ?_⟩
    · have hcone : z ∈ ReciprocityTheory.AnForm.R.conePts (W ⊔ R.D) := by
        refine ⟨hzD.1, fun f hf => ?_⟩
        have hker : W ⊔ R.D ≤ RingHom.ker (eval z) := sup_le
          (fun f hf => RingHom.mem_ker.mpr (by simpa [MvPolynomial.coe_aeval_eq_eval] using hzW f hf))
          (fun f hf => RingHom.mem_ker.mpr (hzD.2 f hf))
        exact RingHom.mem_ker.mp (hker hf)
      have h := (ReciprocityTheory.AnForm.R.mem_conePts_iff_chartIdeal hsuph p z hp).1 hcone
      intro f hf
      have hf' := h f hf
      rwa [← MvPolynomial.coe_aeval_eq_eval] at hf'
    · have hc : (∏ k, z ⟨k, p k⟩)⁻¹ ≠ 0 := inv_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => hp k)
      have hseg : segre (ReciprocityTheory.AnForm.R.affCoord p z) = (∏ k, z ⟨k, p k⟩)⁻¹ • segre z := by
        funext i
        simp only [segre, ReciprocityTheory.AnForm.R.affCoord, Pi.smul_apply, smul_eq_mul, Finset.prod_div_distrib]
        rw [div_eq_inv_mul]
      have hΨ : Ψ (segre (ReciprocityTheory.AnForm.R.affCoord p z)) =
          (∏ k, z ⟨k, p k⟩)⁻¹ • (Fin.cons 1 y : Fin (e + 1) → ℂ) := by
        rw [hseg, map_smul, hzy]
      rw [hΨ, Pi.smul_apply, Fin.cons_zero, smul_eq_mul, mul_one, smul_smul, inv_mul_cancel₀ hc, one_smul]
      exact ⟨hc, rfl⟩
  · refine measure_iUnion_null fun p => ?_
    exact hB K ι _ e Ψ (hA K ι (W ⊔ R.D) e p hsuph hsup)

end ComponentResBridge

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M ComponentResBridge

theorem ComponentResFibreSum.proof (h₁ : ComponentResBadNull.Statement) (hA : ChartDimLt.Statement)
    (hB : ChartRatioImageNull.Statement) : ComponentResFibreSum.Statement := by
  classical
  intro K _ _ ι _ P e L W R Ψ hP hL hW hΨ

  let A : HermLine ι := HermLine.ofWeight (fun _ => (1 : ℝ)) (fun _ _ _ => rfl)
  have hA1 : ∀ z, logNorm A 1 z = 1 := fun z => by
    simp [logNorm, A, HermLine.ofWeight, Real.exp_neg]
  have hAs : IsSmoothHerm A := contDiffOn_const
  have hs : IsSectionOn P A 1 := by
    refine ⟨0, fun k => by simp [A, HermLine.ofWeight], fun m hm k => ?_, fun h => ?_⟩
    · rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
      subst hm
      simp
    · exact hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  have hWh : IsMultiHomogIdeal W := isMultiHomogIdeal_of_mem_minimalPrimes hP hW

  have hN : volume (resProj R Ψ '' (resBad R Ψ ∩ {x | Ψ (segre (R.pt x)) 0 ≠ 0}) ∪
      {y : Fin e → ℂ | ∃ z ∈ zeroLocus ℂ W, z ∈ ReciprocityTheory.AnForm.R.conePts R.D ∧
        Ψ (segre z) = Fin.cons 1 y}) = 0 :=
    measure_union_null (resProj_image_null_of R Ψ (h₁ K ι P e W R Ψ hP hW hΨ))
      (coneD_null R Ψ hA hB hP hW)
  filter_upwards [compl_mem_ae_iff.mpr hN, sheetIndep K ι P e Ψ L A 1 hP hΨ hL hAs hs] with y hyN hind
  have hy1 : y ∉ resProj R Ψ '' (resBad R Ψ ∩ {x | Ψ (segre (R.pt x)) 0 ≠ 0}) := fun h => hyN (Or.inl h)
  have hy2 : ¬ ∃ z ∈ zeroLocus ℂ W, z ∈ ReciprocityTheory.AnForm.R.conePts R.D ∧ Ψ (segre z) = Fin.cons 1 y :=
    fun h => hyN (Or.inr h)

  have hsub : resW R Ψ '' (resProj R Ψ ⁻¹' {y} \ resBad R Ψ) ⊆ fibre P Ψ y := by
    rintro _ ⟨x, hx, rfl⟩
    have := resW_mem_fibre R Ψ hP hW (projection_ne_zero_of_not_mem_badLocus R Ψ hx.2)
    rwa [show resProj R Ψ x = y from hx.1] at this

  have hzero : ∀ w ∈ fibre P Ψ y, w ∉ resW R Ψ '' (resProj R Ψ ⁻¹' {y} \ resBad R Ψ) →
      sheetDensity P Ψ (pot L) ((mcPts P ∩ zeroLocus ℂ W).indicator fun _ => (1 : ℝ)) y w = 0 := by
    intro w hw hwS
    obtain ⟨-, -, -, hΨw⟩ := hw
    unfold sheetDensity
    split_ifs with hγ
    · rw [Set.indicator_of_notMem, zero_mul]
      rintro ⟨hzP, hzW⟩
      have hseg : segre (hγ.choose y) = w := hγ.choose_spec.1
      have hΨz : Ψ (segre (hγ.choose y)) = Fin.cons 1 y := by rw [hseg]; exact hΨw
      by_cases hzD : hγ.choose y ∈ ReciprocityTheory.AnForm.R.conePts R.D
      · exact hy2 ⟨_, hzW, hzD, hΨz⟩
      · obtain ⟨x, -, hx0, hxy, hxw⟩ := exists_of_lift R Ψ hzP hzW hzD hΨz
        exact hwS ⟨x, ⟨hxy, fun hbad => hy1 ⟨x, ⟨hbad, hx0⟩, hxy⟩⟩, hxw.trans hseg⟩
    · rfl
  rw [finsum_mem_inter_support_eq' _ (fibre P Ψ y) (resW R Ψ '' (resProj R Ψ ⁻¹' {y} \ resBad R Ψ))
    fun w hw => ⟨fun h => by_contra fun h' => hw (hzero w h h'), fun h => hsub h⟩]
  rw [finsum_mem_image ((resW_injOn R Ψ).mono fun x hx => show _ ∧ _ from
    ⟨notMem_cone_of_notMem_resBad R Ψ hx.2, projection_ne_zero_of_not_mem_badLocus R Ψ hx.2⟩)]
  refine finsum_mem_congr rfl fun x hx => ?_
  obtain ⟨γ, hγ, hval⟩ := exists_sheet_resW R Ψ L hP hW hL x hx.2
  rw [show resProj R Ψ x = y from hx.1] at hγ hval
  have hex : ∃ γ, IsSheet P Ψ y (resW R Ψ x) γ := ⟨γ, hγ⟩
  unfold sheetDensity
  rw [dif_pos hex]
  have hc := hex.choose_spec

  have hmem : hex.choose y ∈ mcPts P ∩ zeroLocus ℂ W := by
    refine ⟨hc.2.self_of_nhds.2.1, ?_⟩
    have hseg : segre (hex.choose y) = (Ψ (segre (R.pt x)) 0)⁻¹ • segre (R.pt x) := hc.1
    obtain ⟨c, -, hcz⟩ := sameOrbit_of_segre (pt_mem R x).1 _
      (inv_ne_zero (projection_ne_zero_of_not_mem_badLocus R Ψ hx.2)) hseg
    rw [hcz]
    exact mem_zeroLocus_smul hWh c (mem_mcPts_of_conePts hW (pt_mem R x)).2
  rw [Set.indicator_of_mem hmem, one_mul]
  have := hind _ _ _ hc hγ
  rw [hA1, hA1, one_mul, one_mul] at this
  exact this.trans hval

end GroundTheory.Heights₂.Heights.HilbertSamuel
