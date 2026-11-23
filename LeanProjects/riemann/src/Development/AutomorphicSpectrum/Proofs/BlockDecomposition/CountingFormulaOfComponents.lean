import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
import Formalism.SharpRestriction.Divisibility.SlopeExcess.SummableAbsNormRpow

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open GroundTheory.Global PositivityTheory.SiegelWeilFormula.Densx PositivityTheory.Rg.Base1
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.RgBaseCnt

section Ideles

variable {F : Type} [Field F] [NumberField F]

theorem md_mul (a b : (AF F)ˣ) : md (a * b) = md a * md b := by
  simp [md, map_mul]

theorem md_pr (t : Fˣ) : md (pr t) = 1 := by
  have h := IdeleGroup.ideleModule_diagonal (K := F) t
  have h2 : pr t = IdeleGroup.diagonal F t := rfl
  simp [md, h2, h]

theorem md_pr_mul (t : Fˣ) (a : (AF F)ˣ) : md (pr t * a) = md a := by
  rw [md_mul, md_pr, one_mul]

theorem th_pr_mul (f : (AF F)ˣ → ℝ≥0∞) (t : Fˣ) (a : (AF F)ˣ) : th f (pr t * a) = th f a := by
  unfold th
  have h : ∀ u : Fˣ, pr u * (pr t * a) = pr (u * t) * a := fun u => by
    rw [← mul_assoc]; congr 1; exact (map_mul (Units.map (algebraMap F (AF F)).toMonoidHom) u t).symm
  simp_rw [h]
  exact (Equiv.mulRight t).tsum_eq (fun u => f (pr u * a))

def ray (θ : ℝ →+* Ainf F) (δ : ℝ) : (AF F)ˣ :=
  if h : δ = 0 then 1 else
    ⟨(θ δ, 1), (θ δ⁻¹, 1), by
      refine Prod.ext ?_ (mul_one _)
      change θ δ * θ δ⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ h, map_one], by
      refine Prod.ext ?_ (mul_one _)
      change θ δ⁻¹ * θ δ = 1
      rw [← map_mul, inv_mul_cancel₀ h, map_one]⟩

theorem isRay_ray (θ : ℝ →+* Ainf F) : IsRay θ (ray θ) := fun δ hδ => by
  simp [ray, hδ.ne']

theorem ray_mul_self (θ : ℝ →+* Ainf F) {ε : ℝ} (hε : ε ≠ 0) : ray θ ε * ray θ ε = ray θ (ε ^ 2) := by
  have h2 : ε ^ 2 ≠ 0 := pow_ne_zero 2 hε
  apply Units.ext
  simp only [ray, hε, h2, dite_false, Units.val_mul]
  refine Prod.ext ?_ (mul_one _)
  change θ ε * θ ε = θ (ε ^ 2)
  rw [← map_mul, sq]

end Ideles

section Norms

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isNm_one : IsNm σ (1 : (AF F ⊗[F] E)ˣ) (1 : (AF F)ˣ) := by
  unfold IsNm
  change ((1 : AF F) ⊗ₜ[F] (1 : E)) = sigR (AF F) σ 1 * 1
  rw [map_one, mul_one]
  rfl

theorem isNm_mul {x : (AF F ⊗[F] E)ˣ} {n : (AF F)ˣ} (h : IsNm σ x n) (u : (AF F)ˣ) :
    IsNm σ (x * Units.map (Algebra.TensorProduct.includeLeft : AF F →ₐ[F] AF F ⊗[F] E).toMonoidHom u) (n * (u * u)) := by
  unfold IsNm at h ⊢
  have hs : sigR (AF F) σ ((u : AF F) ⊗ₜ[F] (1 : E)) = (u : AF F) ⊗ₜ[F] (1 : E) := by
    simp [sigR]
  have e : ((Units.map (Algebra.TensorProduct.includeLeft : AF F →ₐ[F] AF F ⊗[F] E).toMonoidHom u : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      (u : AF F) ⊗ₜ[F] (1 : E) := rfl
  rw [Units.val_mul, Units.val_mul, Units.val_mul, e, map_mul, hs]
  have e2 : ((n : AF F) * ((u : AF F) * (u : AF F))) ⊗ₜ[F] (1 : E) =
      ((n : AF F) ⊗ₜ[F] (1 : E)) * (((u : AF F) ⊗ₜ[F] (1 : E)) * ((u : AF F) ⊗ₜ[F] (1 : E))) := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [e2, h]
  ring

theorem pr_mem {H : Subgroup (AF F)ˣ} (hH : IsH σ H) (t : Fˣ) : pr t ∈ H :=
  (hH _).2 ⟨t, 1, 1, isNm_one, by simp⟩

theorem asym_of {H : Subgroup (AF F)ˣ} (hH : IsH σ H) {r : ℝ → (AF F)ˣ} (f : (AF F)ˣ → ℝ≥0∞)
    (hr : ∀ ε : ℝ, 0 < ε → r ε * r ε = r (ε ^ 2))
    (M : (AF F ⊗[F] E)ˣ → ℝ≥0∞) (c : ℝ≥0∞)
    (hM : ∀ x n, IsNm σ x n → M x = th f n) (hoff : ∀ a, a ∉ H → f a = 0)
    (hb : ∃ C : ℝ≥0, ∀ x n, IsNm σ x n → ENNReal.ofReal (md n) * M x ≤ C)
    (hv : ∃ R : ℝ, ∀ x n, IsNm σ x n → R < md n → M x = 0)
    (hl : ∀ x n, IsNm σ x n → Tendsto (fun ε : ℝ => ENNReal.ofReal (md (n * r (ε ^ 2))) *
      M (x * Units.map (Algebra.TensorProduct.includeLeft : AF F →ₐ[F] AF F ⊗[F] E).toMonoidHom (r ε))) (𝓝[>] 0) (𝓝 c)) :
    Asym r H f c := by
  have hth0 : ∀ a, a ∉ H → th f a = 0 := fun a ha => by
    unfold th
    refine ENNReal.tsum_eq_zero.2 fun t => hoff _ fun h => ha ?_
    have := H.mul_mem (H.inv_mem (pr_mem hH t)) h
    simpa using this
  obtain ⟨C, hC⟩ := hb
  obtain ⟨R, hR⟩ := hv
  refine ⟨⟨C, fun a => ?_⟩, ⟨R, fun a ha => ?_⟩, hth0, fun a haH => ?_⟩
  · by_cases h : a ∈ H
    · obtain ⟨t, x, n, hn, rfl⟩ := (hH a).1 h
      rw [md_pr_mul, th_pr_mul, ← hM x n hn]
      exact hC x n hn
    · simp [hth0 a h]
  · by_cases h : a ∈ H
    · obtain ⟨t, x, n, hn, rfl⟩ := (hH a).1 h
      rw [md_pr_mul] at ha
      rw [th_pr_mul, ← hM x n hn]
      exact hR x n hn ha
    · exact hth0 a h
  · obtain ⟨t, x, n, hn, rfl⟩ := (hH a).1 haH
    have hsq : Tendsto Real.sqrt (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have := (Real.continuous_sqrt.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with δ hδ
        exact Real.sqrt_pos.2 hδ
    refine ((hl x n hn).comp hsq).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hδ' : (0:ℝ) < δ := hδ
    have hε : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ'
    have e1 : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ'.le
    have hN := isNm_mul hn (r (Real.sqrt δ))
    rw [hr _ hε, e1] at hN
    simp only [Function.comp, e1]
    rw [hM _ _ hN, mul_assoc, md_pr_mul, th_pr_mul]

end Norms

section Euler

variable {F : Type} [Field F] [NumberField F] (E : Type) [Field E] [NumberField E] [Algebra F E]

theorem eR_cases (v : HeightOneSpectrum (𝓞 F)) : eR E v = 1 ∨ eR E v = -1 := by
  unfold eR PositivityTheory.SiegelWeilFormula.Gen.eSp
  split_ifs <;> simp

theorem eSp_eq (v : HeightOneSpectrum (𝓞 F)) : PositivityTheory.SiegelWeilFormula.Gen.eSp E v = ((eR E v : ℝ) : ℂ) := by
  unfold eR PositivityTheory.SiegelWeilFormula.Gen.eSp
  split_ifs <;> simp

omit [Field E] [NumberField E] [Algebra F E] in
theorem one_lt_q (v : HeightOneSpectrum (𝓞 F)) : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  exact_mod_cast Nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨h0, h1⟩

def fac (s : ℝ) (v : HeightOneSpectrum (𝓞 F)) : ℝ := 1 - eR E v * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s)

theorem fac_pos {s : ℝ} (hs : 0 < s) (v : HeightOneSpectrum (𝓞 F)) : 0 < fac E s v := by
  have h1 : (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (one_lt_q v) (by linarith)
  have h2 : 0 < (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by linarith [one_lt_q v]) _
  unfold fac
  rcases eR_cases E v with h | h <;> rw [h] <;> linarith

theorem fac_mult_sub {s : ℝ} (hs : 1 < s) (T : Set (HeightOneSpectrum (𝓞 F))) :
    Multipliable (fun v : T => fac E s v.1) := by
  have hsum := Formalism.MainNotions.DIV.Proofs.QuadraticNormBounds.summable_absNorm_rpow F hs
  have h : Summable fun v : HeightOneSpectrum (𝓞 F) => ‖-(eR E v * (Ideal.absNorm v.asIdeal : ℝ) ^ (-s))‖ := by
    refine hsum.congr fun v => ?_
    have h2 : 0 < (Ideal.absNorm v.asIdeal : ℝ) ^ (-s) := Real.rpow_pos_of_pos (by linarith [one_lt_q v]) _
    rcases eR_cases E v with e | e <;> rw [e] <;> simp [abs_of_pos h2]
  have := multipliable_one_add_of_summable (h.subtype T)
  refine this.congr fun v => ?_
  simp [fac, sub_eq_add_neg]

theorem fac_mult {s : ℝ} (hs : 1 < s) : Multipliable (fac E s : HeightOneSpectrum (𝓞 F) → ℝ) :=
  ((Equiv.Set.univ _).multipliable_iff (f := fac E s)).1 (fac_mult_sub E hs Set.univ)

theorem tot_eq {s : ℝ} (hs : 1 < s) : ∏' v : HeightOneSpectrum (𝓞 F),
      (1 - PositivityTheory.SiegelWeilFormula.Gen.eSp E v * (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))) =
    ((∏' v : HeightOneSpectrum (𝓞 F), fac E s v : ℝ) : ℂ) := by
  have h := (fac_mult (F := F) E hs).map_tprod Complex.ofRealHom Complex.continuous_ofReal
  simp only [Complex.ofRealHom_eq_coe] at h
  rw [h]
  refine tprod_congr fun v => ?_
  have hq : (0 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by positivity
  simp only [fac, eSp_eq]
  push_cast [Complex.ofReal_cpow hq]
  rfl

theorem tot_split {s : ℝ} (hs : 1 < s) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∏' v : HeightOneSpectrum (𝓞 F), fac E s v = (∏ v ∈ S, fac E s v) * ∏' v : {v // v ∉ S}, fac E s v.1 :=
  by
  have h := Multipliable.tprod_mul_tprod_compl (f := fac E s) (s := (S : Set (HeightOneSpectrum (𝓞 F))))
    (fac_mult_sub E hs _) (fac_mult_sub E hs _)
  have h1 : ∏' v : (S : Set (HeightOneSpectrum (𝓞 F))), fac E s v.1 = ∏ v ∈ S, fac E s v := Finset.tprod_subtype' S (fac E s)
  have h2 : ∏' v : ((S : Set (HeightOneSpectrum (𝓞 F)))ᶜ : Set _), fac E s v.1 = ∏' v : {v // v ∉ S}, fac E s v.1 :=
    (Equiv.subtypeEquivRight (fun v => by simp)).tprod_eq (fun v : {v // v ∉ S} => fac E s v.1)
  rw [← h, h1, h2]

theorem lam_tendsto (S : Finset (HeightOneSpectrum (𝓞 F))) {Λ : ℂ} (h : IsLamLim F E Λ) :
    Λ.im = 0 ∧ 0 ≤ Λ.re ∧ Tendsto (fun s : ℝ => ENNReal.ofReal
      (∏' v : {v // v ∉ S}, (1 - eR E v.1 * (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-s)))) (𝓝[>] 1)
      (𝓝 (ENNReal.ofReal Λ.re * ∏ v ∈ S, (cfac E v : ℝ≥0∞))) := by
  have hev : ∀ᶠ s : ℝ in 𝓝[>] 1, 1 < s := self_mem_nhdsWithin
  have hC : Tendsto (fun s : ℝ => ((∏' v : HeightOneSpectrum (𝓞 F), fac E s v : ℝ) : ℂ)) (𝓝[>] 1) (𝓝 Λ) := by
    refine Tendsto.congr' ?_ h
    filter_upwards [hev] with s hs using tot_eq E hs
  have him : Λ.im = 0 := by
    have := (Complex.continuous_im.tendsto Λ).comp hC
    simp only [Function.comp_def, Complex.ofReal_im] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hre : Tendsto (fun s : ℝ => ∏' v : HeightOneSpectrum (𝓞 F), fac E s v) (𝓝[>] 1) (𝓝 Λ.re) := by
    have := (Complex.continuous_re.tendsto Λ).comp hC
    simpa only [Function.comp_def, Complex.ofReal_re] using this
  have hnn : 0 ≤ Λ.re := by
    refine ge_of_tendsto hre ?_
    filter_upwards [hev] with s hs
    exact ge_of_tendsto' (fac_mult (F := F) E hs).hasProd
      fun u => Finset.prod_nonneg fun v _ => (fac_pos E (by linarith) v).le
  refine ⟨him, hnn, ?_⟩
  have hc0 : 0 < ∏ v ∈ S, fac E 1 v := Finset.prod_pos fun v _ => fac_pos E one_pos v
  have hQ : Tendsto (fun s : ℝ => ∏ v ∈ S, fac E s v) (𝓝[>] 1) (𝓝 (∏ v ∈ S, fac E 1 v)) := by
    refine tendsto_finsetProd _ fun v _ => ?_
    have hq : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by linarith [one_lt_q (F := F) v]
    have hc : Continuous fun s : ℝ => fac E s v := by
      unfold fac
      exact continuous_const.sub (continuous_const.mul (Real.continuous_const_rpow hq |>.comp continuous_neg))
    exact (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  have hP : Tendsto (fun s : ℝ => ∏' v : {v // v ∉ S}, (1 - eR E v.1 * (Ideal.absNorm v.1.asIdeal : ℝ) ^ (-s))) (𝓝[>] 1)
      (𝓝 (Λ.re / ∏ v ∈ S, fac E 1 v)) := by
    refine (hre.div hQ hc0.ne').congr' ?_
    filter_upwards [hev] with s hs
    have hq0 : ∏ v ∈ S, fac E s v ≠ 0 := (Finset.prod_pos fun v _ => fac_pos E (by linarith) v).ne'
    simp only [Pi.div_apply]
    rw [tot_split E hs S, mul_div_cancel_left₀ _ hq0]
    rfl
  have hL : ENNReal.ofReal (Λ.re / ∏ v ∈ S, fac E 1 v) = ENNReal.ofReal Λ.re * ∏ v ∈ S, (cfac E v : ℝ≥0∞) := by
    rw [div_eq_mul_inv, ENNReal.ofReal_mul hnn, ← Finset.prod_inv_distrib,
      ENNReal.ofReal_prod_of_nonneg fun v _ => (inv_pos.2 (fac_pos E one_pos v)).le]
    congr 1
    refine Finset.prod_congr rfl fun v _ => ?_
    simp only [fac, cfac, Real.rpow_neg_one, div_eq_mul_inv]
    rfl
  rw [← hL]
  exact (ENNReal.continuous_ofReal.tendsto _).comp hP

theorem cfac_ne_zero (v : HeightOneSpectrum (𝓞 F)) : cfac E v ≠ 0 := by
  have h := inv_pos.2 (fac_pos (F := F) E one_pos v)
  simp only [fac, Real.rpow_neg_one, ← div_eq_mul_inv] at h
  simpa [cfac] using h

end Euler

theorem limit_cancel {κ : ℝ≥0} {pc vol V L : ℝ≥0∞} {P a b : ℝ → ℝ≥0∞}
    (h0 : pc ≠ 0) (h1 : pc ≠ ⊤) (hv0 : vol ≠ 0) (hvt : vol ≠ ⊤) (hV0 : V ≠ 0) (hVt : V ≠ ⊤)
    (hP : Tendsto P (𝓝[>] 1) (𝓝 (L * pc)))
    (hLt : L ≠ ⊤)
    (hA : Tendsto (fun s : ℝ => ENNReal.ofReal (s - 1) * ((κ : ℝ≥0∞) * a s)) (𝓝[>] 1) (𝓝 (vol * V / 2)))
    (hB : Tendsto (fun s : ℝ => ENNReal.ofReal (s - 1) * b s) (𝓝[>] 1) (𝓝 (pc * vol * V)))
    (hR : ∀ s : ℝ, 1 < s → P s * a s = b s) : L / 2 = κ := by
  have hW0 : vol * V ≠ 0 := mul_ne_zero hv0 hV0
  have hWt : vol * V ≠ ⊤ := ENNReal.mul_ne_top hvt hVt
  have hLp : L * pc ≠ ⊤ := ENNReal.mul_ne_top hLt h1
  have hWh : vol * V / 2 ≠ ⊤ := ENNReal.div_ne_top hWt (by norm_num)
  have e1 := ENNReal.Tendsto.mul hP (Or.inr hWh) hA (Or.inr hLp)
  have e2 := ENNReal.Tendsto.const_mul (a := (κ : ℝ≥0∞)) hB (Or.inr ENNReal.coe_ne_top)
  have e3 : (L * pc) * (vol * V / 2) = (κ : ℝ≥0∞) * (pc * vol * V) := by
    refine tendsto_nhds_unique e1 (e2.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [← hR s hs]
    ring
  have hpw : pc * (vol * V) ≠ 0 := mul_ne_zero h0 hW0
  have hpwt : pc * (vol * V) ≠ ⊤ := ENNReal.mul_ne_top h1 hWt
  have e4 : (L / 2) * (pc * (vol * V)) = (κ : ℝ≥0∞) * (pc * (vol * V)) := by
    rw [mul_assoc pc vol V] at e3
    rw [← e3, div_eq_mul_inv, div_eq_mul_inv]
    ring
  exact (ENNReal.mul_left_inj hpw hpwt).1 e4

theorem cnt_of : Tate → PsiSide → Ratio → HEx → TestEx → Dens → LSide → ThetaId → Cnt := by
  intro hTate hPsi hRatio hHEx hTest hDens hLS hTI F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hCM hJ hli hlam hμ h𝓕 hmi hm κ hκ Λ hΛ
  have hF : IsTotallyReal F := hCM.1
  obtain ⟨⟨θ, hθc⟩, -⟩ := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_real F hF
  have hr : IsRay θ (ray θ) := isRay_ray θ
  obtain ⟨S, hS⟩ := hTI F E σ J d b li lam μ 𝓕 mi m hCM hJ hli hlam hμ h𝓕 hmi hm κ hκ
  obtain ⟨φ, A, htest, hv0, hvt⟩ := hTest F E σ J d b li lam μ 𝓕 mi m hCM hJ hli hlam hμ h𝓕 hmi hm S
  obtain ⟨hmean, hoff⟩ := hS S (Finset.Subset.refl _) φ A htest
  obtain ⟨hGc, hGs, hgS, hdens⟩ := hDens F E σ J d b li lam μ 𝓕 mi m hCM hJ hli hlam hμ h𝓕 hmi hm S φ A htest
  obtain ⟨hb, hv, hl⟩ := hLS F E σ J d b li lam μ 𝓕 mi m hCM hJ hli hlam hμ h𝓕 hmi hm θ hθc (ray θ) hr S φ A htest
  obtain ⟨H, hH, hHo, hHi⟩ := hHEx F E σ hCM
  obtain ⟨V, hV0, hVt, hT⟩ := hTate F hF θ hθc (ray θ) hr
  have hG0 : ∀ y, 0 ≤ Gi mi φ y := fun y => integral_nonneg fun X => htest.2.2.1 X
  have hg0 : ∀ v y, 0 ≤ gv m A v y := fun v y => mul_nonneg (NNReal.coe_nonneg _) ENNReal.toReal_nonneg
  obtain ⟨hDm, hRat⟩ := hRatio F S (Gi mi φ) (gv m A) (eR E) hGc hG0 hg0 (fun v hv => (hgS v hv).1) (eR_cases E)
  have hf : Measurable fun a => (κ : ℝ≥0∞) * pure S (Gi mi φ) (gv m A) (fun v => rv v (eR E v)) a := hDm.const_mul _
  have hth : ∀ n, th (fun a => (κ : ℝ≥0∞) * pure S (Gi mi φ) (gv m A) (fun v => rv v (eR E v)) a) n =
      κ * th (pure S (Gi mi φ) (gv m A) fun v => rv v (eR E v)) n := fun n => ENNReal.tsum_mul_left
  have hAs : Asym (ray θ) H (fun a => (κ : ℝ≥0∞) * pure S (Gi mi φ) (gv m A) (fun v => rv v (eR E v)) a) (vol b li lam S φ A) :=
    asym_of hH _ (fun ε hε => ray_mul_self θ hε.ne') (mean σ J μ 𝓕 φ A) _
      (fun x n hn => by rw [hth]; exact hmean x n hn) (fun a ha => by simp [hoff H hH a ha]) hb hv hl
  have hrH : ∀ δ : ℝ, 0 < δ → ray θ δ ∈ H := fun δ hδ => by
    have hε : Real.sqrt δ ≠ 0 := (Real.sqrt_pos.2 hδ).ne'
    have e : ray θ δ = pr (1 : Fˣ) * (1 * (ray θ (Real.sqrt δ) * ray θ (Real.sqrt δ))) := by
      rw [ray_mul_self θ hε, Real.sq_sqrt hδ.le]
      simp [pr]
    exact (hH _).2 ⟨1, _, _, isNm_mul isNm_one _, e⟩
  obtain ⟨-, hA⟩ := hT H hHo (by rw [hHi]; norm_num) (pr_mem hH) hrH _ _ hf hAs
  obtain ⟨hPm, hPas⟩ := hPsi F hF θ hθc (ray θ) hr li lam hli hlam S (Gi mi φ) (gv m A) hGc hGs hG0 hg0 hgS
  obtain ⟨hfin, hB⟩ := hT ⊤ (by simp) (by simp) (fun _ => trivial) (fun _ _ => trivial) _ _ hPm hPas
  obtain ⟨him, hre, hP⟩ := lam_tendsto E S hΛ
  rw [hdens] at hB
  have hzi : ∀ s : ℝ, zi (fun a => (κ : ℝ≥0∞) * pure S (Gi mi φ) (gv m A) (fun v => rv v (eR E v)) a) s =
      κ * zi (pure S (Gi mi φ) (gv m A) fun v => rv v (eR E v)) s := fun s => by
    unfold zi
    simp_rw [mul_assoc]
    exact lintegral_const_mul' _ _ ENNReal.coe_ne_top
  simp_rw [hzi] at hA
  rw [hHi] at hA
  have hpc0 : ∏ v ∈ S, (cfac E v : ℝ≥0∞) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun v _ => ENNReal.coe_ne_zero.2 (cfac_ne_zero E v)
  have hpct : ∏ v ∈ S, (cfac E v : ℝ≥0∞) ≠ ⊤ := by
    rw [← ENNReal.ofNNReal_finsetProd]; exact ENNReal.coe_ne_top
  have key := limit_cancel (κ := κ) hpc0 hpct hv0 hvt hV0 hVt hP ENNReal.ofReal_ne_top
    (by simpa using hA) (by simpa using hB) (fun s hs => hRat s hs (hfin s hs))
  have hk : Λ.re / 2 = (κ : ℝ) := by
    have := congrArg ENNReal.toReal key
    simpa [ENNReal.toReal_div, ENNReal.toReal_ofReal hre] using this
  apply Complex.ext
  · simp [← hk]
  · simp [him]

end GlobalTheory.CompanionTheory.RgBaseCnt

end
