import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.EvalPB

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

open CapelliMinorRestriction in
theorem evalP : EvalPStatement := by
  intro k r ε u lam h H _ _ _ σ D E V T μ ι hσ hD hV hcas hK hμ hψ hp hq hgap hHC hGap z c Vp _ _ _ π μW μN P hP hB x₀ w v ξ s g hx₀ hg hu hne
  have hE : IsGlRep E := hD.1
  have hB2 := hB
  unfold IsBData at hB2
  obtain ⟨-, hTz, -, -, hW, hN⟩ := hB2
  have hP2 := hP
  unfold Formalism.MainNotions.S.IsCayley at hP2
  obtain ⟨hPunit, hPJ⟩ := hP2
  have hPu : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hPunit
  have hGN := gapNeed k r ε h hp hq hgap
  have hdec := S0.DecDeriv.decDeriv _ ε lam h T μ hHC hGap hGN.2 hGN.1 hμ
  set a := aExp ε h with ha_def
  have hb : S0.bS k r < a - 1 := CurveContinuity.per_gap hgap
  have hh : 0 ≤ h := by
    have h1 := hgap
    unfold StepGap at h1
    have h2 : (0 : ℝ) < h - 2 := lt_of_le_of_lt (by positivity) (lt_of_le_of_lt (le_max_left _ _) h1.1)
    linarith
  have ha0 : 0 ≤ a := by
    rw [ha_def]; unfold aExp; positivity
  set S := genSub E V with hS
  have hgood : ∀ f : D, f ∈ S → TmGood ε σ x₀ ((w : D) : H) a ((f : D) : H) :=
    fun f hf => tmC_good_genSub hσ hD hμ hψ ha0 hdec hx₀ w hf
  set ψg := Formalism.MainNotions.S.psiGen k r z c with hψg
  obtain ⟨L, hLdef⟩ : ∃ L : H → Vp, L = fun m => per P μW μN ψg π (coefX σ x₀ ((w : D) : H) m) ξ g :=
    ⟨_, rfl⟩
  have hlin : ∀ m m' : D, m ∈ S → m' ∈ S → ∀ t : ℂ,
      L ((m : H) + t • (m' : H)) = L m + t • L m' := by
    intro m m' hm hm' t
    rw [hLdef]
    exact EvaluationEquivalence.per_lin hP hB hg hb ξ (hgood m hm) (hgood m' hm') t
  have hL0 : L 0 = 0 := by
    have h1 := hlin 0 0 S.zero_mem S.zero_mem 1
    simp only [ZeroMemClass.coe_zero, smul_zero, add_zero, one_smul] at h1
    simpa using h1
  let l : S →ₗ[ℂ] Vp :=
    { toFun := fun m => L ((m : D) : H)
      map_add' := fun m m' => by
        have h1 := hlin m m' m.2 m'.2 1
        simpa using h1
      map_smul' := fun t m => by
        have h1 := hlin 0 m S.zero_mem m.2 t
        simpa [hL0] using h1 }
  have hl : ∀ m : S, l m = L ((m : D) : H) := fun m => rfl

  obtain ⟨g₀, Dk, ψ', hfr, hup, hzero, hkap, hWW, hCD⟩ :=
    frameLaw k r ε u lam h H σ D E V T μ ι hσ hD hV hcas hK hμ hψ hp hq hgap hHC hGap z c Vp π μW μN P hP hB
      x₀ w ξ g hx₀ hg
  have hfr2 := hfr
  unfold Formalism.MainNotions.S.IsFrameW at hfr2
  have hg₀u : IsUnit g₀.det := TransportGeo.uh_det hfr2.1
  have hgu : IsUnit g.det := TransportGeo.uh_det hg
  set Q : Mat k r := g₀⁻¹ * g * P⁻¹ with hQdef
  have hQu : IsUnit Q.det := by
    rw [hQdef, Matrix.det_mul, Matrix.det_mul]
    exact ((Matrix.isUnit_nonsing_inv_det _ hg₀u).mul hgu).mul (Matrix.isUnit_nonsing_inv_det _ hPu)
  have hQQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQu
  have hQQ' : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hQu
  have hgQ : g * P⁻¹ = g₀ * Q := by
    rw [hQdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv g₀ hg₀u, Matrix.one_mul]
  obtain ⟨c₀, hc₀, hcJ⟩ := CapelliMinorRestriction.beta_formula ε P hPJ z hTz g g₀ Q hfr hgQ
  have hSE : ∀ a' b', ∀ x ∈ S, E a' b' x ∈ S := fun a' b' x hx => CapelliMinorRestriction.gen_stable E V a' b' hx
  have hSF : ∀ a' b', ∀ x ∈ S, frameE Q E a' b' x ∈ S :=
    fun a' b' x hx => CapelliMinorRestriction.gen_stable_frame E V Q a' b' hx
  have hvS : (v : D) ∈ S := CapelliMinorRestriction.le_gen E V v.2
  have hcontT : ∀ (x1 : Fin (2 * r + k + 1) → ℂ) (f : Fin (2 * r + k + 1) → D), (∀ c', f c' ∈ S) →
      ContinuousOn (tMap ε σ x1 x₀ ((w : D) : H) (fun c' => ((f c' : D) : H))) (UJset ε) := by
    intro x1 f hf
    unfold tMap
    apply continuousOn_finset_sum
    intro c' _
    apply ContinuousOn.mul
    · rw [← tmD_cJL_coe]
      exact (tmD_cJL ε x1 (Pi.single c' 1)).continuous.continuousOn
    · exact CapelliMinorRestriction.cont_of_smoothOnG (hgood _ (hf c')).1
  have hintT : ∀ f : Fin (2 * r + k + 1) → D, (∀ c', f c' ∈ S) →
      Integrable (CapelliMinorRestriction.perI P ψg π (tMap ε σ (xJ P z) x₀ ((w : D) : H) (fun c' => ((f c' : D) : H))) ξ g)
        (μW.prod μN) := by
    intro f hf
    obtain ⟨C, hC⟩ := (tMap_spec k r ε lam h H σ D E V T μ ι hσ hD hV hcas hK hμ hψ hp hq hgap hHC hGap
      (xJ P z) x₀ w hx₀ f hf).2.2 []
    exact CurveContinuity.int_of_bound hP hB hg ξ a hb _ (hcontT _ f hf) C hC

  set om : ℂ := ((-(LemK.thV lam s) : ℝ) : ℂ) with hom
  have hcmS : ∀ (p : ℕ) (R C : Fin p → Fin (2 * r + k + 1)) (t : ℂ),
      Capelli.cminor (frameE Q E) R C t (v : D) ∈ S :=
    fun p R C t => CapelliMinorMembership.cminor_mem hSF R C t _ hvS
  have key : ∀ j₀ : Fin (2 * r + k + 1),
      per P μW μN ψg π (tMap ε σ (xJ P z) x₀ ((w : D) : H)
        (fun c' => ((Capelli.nnPlus E (Q⁻¹ *ᵥ Pi.single j₀ 1) om (v : D) c' : D) : H))) ξ g =
      (c₀ * (-1 : ℂ) ^ (2 * r + k + (j₀ : ℕ))) •
        L ((Capelli.cminor (frameE Q E) (Fin.last (2 * r + k)).succAbove j₀.succAbove (om - 1) (v : D) : D) : H) := by
    intro j₀
    set y := Q⁻¹ *ᵥ Pi.single j₀ 1 with hy
    have hnnS : ∀ d, Capelli.nnPlus E y om (v : D) d ∈ S := by
      intro d
      unfold Capelli.nnPlus
      apply Submodule.sum_mem
      intro c' _
      exact S.smul_mem _ (CapelliMinorMembership.cminor_mem hSE _ _ _ _ hvS)
    set F : Fin (2 * r + k + 1) → Mat k r → ℂ := fun d =>
      tMap ε σ (xJ P z) x₀ ((w : D) : H) (Pi.single d ((Capelli.nnPlus E y om (v : D) d : D) : H)) with hF
    have hsing : ∀ d, Pi.single d ((Capelli.nnPlus E y om (v : D) d : D) : H) =
        fun c' => (((Pi.single d (Capelli.nnPlus E y om (v : D) d) : Fin (2 * r + k + 1) → D) c' : D) : H) := by
      intro d
      funext c'
      by_cases hc : c' = d
      · subst hc; simp
      · simp [Pi.single_eq_of_ne hc]
    have hint : ∀ d ∈ (Finset.univ : Finset (Fin (2 * r + k + 1))),
        Integrable (CapelliMinorRestriction.perI P ψg π (F d) ξ g) (μW.prod μN) := by
      intro d _
      simp only [hF]
      rw [hsing d]
      apply hintT
      intro c'
      by_cases hc : c' = d
      · subst hc; simpa using hnnS c'
      · simp [Pi.single_eq_of_ne hc]
    have hfs : tMap ε σ (xJ P z) x₀ ((w : D) : H)
        (fun c' => ((Capelli.nnPlus E y om (v : D) c' : D) : H)) = fun G => ∑ d ∈ Finset.univ, F d G :=
      funext fun G => CapelliMinorRestriction.tMap_sum ε σ (xJ P z) x₀ ((w : D) : H) _ G
    rw [hfs, CapelliMinorRestriction.per_sum P μW μN ψg π Finset.univ F ξ g hint]
    rw [Finset.sum_congr rfl (fun d _ => CapelliMinorRestriction.per_tMap_single ε σ z P hPJ μW μN hW hN ψg π x₀ ((w : D) : H) d
      ((Capelli.nnPlus E y om (v : D) d : D) : H) ξ g)]
    simp only [hcJ]
    have hsumS : (∑ d, (c₀ * Q (Fin.last (2 * r + k)) d) • (⟨Capelli.nnPlus E y om (v : D) d, hnnS d⟩ : S)) =
        (c₀ * (-1 : ℂ) ^ (2 * r + k + (j₀ : ℕ))) •
          (⟨Capelli.cminor (frameE Q E) (Fin.last (2 * r + k)).succAbove j₀.succAbove (om - 1) (v : D),
            hcmS _ _ _ _⟩ : S) := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul]
      exact CapelliMinorRestriction.sum_beta_nnPlus (2 * r + k) E hE Q hQQ c₀ j₀ om (v : D)
    have h1 : ∀ d, per P μW μN ψg π (coefX σ x₀ ((w : D) : H) ((Capelli.nnPlus E y om (v : D) d : D) : H)) ξ g =
        l ⟨Capelli.nnPlus E y om (v : D) d, hnnS d⟩ := by
      intro d; rw [hl, hLdef]
    simp only [h1]
    calc ∑ d, (c₀ * Q (Fin.last (2 * r + k)) d) • l ⟨Capelli.nnPlus E y om (v : D) d, hnnS d⟩
        = l (∑ d, (c₀ * Q (Fin.last (2 * r + k)) d) • (⟨Capelli.nnPlus E y om (v : D) d, hnnS d⟩ : S)) := by
          rw [map_sum]; simp only [map_smul]
      _ = _ := by rw [hsumS, map_smul]; rfl

  have hfac : ∀ j, (om - 1 - (r : ℂ) + ((u j : ℝ) : ℂ) - ((k : ℂ) - 1) / 2) ≠ 0 := by
    intro j
    have e : om - 1 - (r : ℂ) + ((u j : ℝ) : ℂ) - ((k : ℂ) - 1) / 2 = ((u j - (lam s + 1 / 2) : ℝ) : ℂ) := by
      rw [hom]; unfold LemK.thV; push_cast; ring
    rw [e, Complex.ofReal_ne_zero, sub_ne_zero]; exact hu j
  have hprod : (∏ j : Fin k, (om - 1 - (r : ℂ) + ((u j : ℝ) : ℂ) - ((k : ℂ) - 1) / 2)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => hfac j
  have hlv : l ⟨(v : D), hvS⟩ ≠ 0 := by
    rw [hl, hLdef]; exact hne
  have hFE : IsGlRep (frameE Q E) := CapelliMinorRestriction.frameGl Q E hQQ' hQQ hE
  have hRE : IsGlRep (CapelliMinorRestriction.resE (frameE Q E) S hSF) := CapelliMinorRestriction.isGlRep_resE (frameE Q E) S hSF hFE
  have hres : ∀ (R C : Fin (2 * r + k) → Fin (2 * r + k + 1)) (x : ℂ),
      l (Capelli.cminor (CapelliMinorRestriction.resE (frameE Q E) S hSF) R C x ⟨(v : D), hvS⟩) =
        L ((Capelli.cminor (frameE Q E) R C x (v : D) : D) : H) := by
    intro R C x
    rw [hl, CapelliMinorRestriction.cminor_resE]
  have hnz : ∃ j₀ : Fin (2 * r + k + 1),
      L ((Capelli.cminor (frameE Q E) (Fin.last (2 * r + k)).succAbove j₀.succAbove (om - 1) (v : D) : D) : H) ≠ 0 := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · refine ⟨Fin.last (2 * r + k), ?_⟩
      have hkn : k = 2 * r + k := by omega
      obtain ⟨e, he_def⟩ : ∃ e : Fin (k + 1) → Fin (2 * r + k + 1), e = Fin.cast (by omega) := ⟨_, rfl⟩
      have he : Function.Injective e := fun a' b' hab => by
        rw [he_def] at hab; exact Fin.cast_injective _ hab
      have hWW' : ∀ i j, l ∘ₗ (fun a' b' => CapelliMinorRestriction.resE (frameE Q E) S hSF (e a') (e b'))
          (Fin.castSucc i) (Fin.castSucc j) = Dk i j ∘ₗ l := by
        intro i j
        apply LinearMap.ext
        intro m
        have hi : e (Fin.castSucc i) = capIdx k r (Capelli.wIdx k r i) :=
          Fin.ext (by simp [he_def, capIdx, Capelli.wIdx, hr])
        have hj : e (Fin.castSucc j) = capIdx k r (Capelli.wIdx k r j) :=
          Fin.ext (by simp [he_def, capIdx, Capelli.wIdx, hr])
        show L (((CapelliMinorRestriction.resE (frameE Q E) S hSF (e (Fin.castSucc i)) (e (Fin.castSucc j)) m : S) : D) : H) =
          Dk i j (L ((m : D) : H))
        rw [hi, hj, hLdef]
        exact hWW i j m m.2
      have hB0 := Capelli.whittakerZeroStatement S Vp k (fun a' b' => CapelliMinorRestriction.resE (frameE Q E) S hSF (e a') (e b')) Dk l
        (om - 1) hWW'
      have hcm : Capelli.cminor (fun a' b' => CapelliMinorRestriction.resE (frameE Q E) S hSF (e a') (e b'))
          Fin.castSucc Fin.castSucc (om - 1) =
          Capelli.cminor (CapelliMinorRestriction.resE (frameE Q E) S hSF) ((Fin.last (2 * r + k)).succAbove ∘ Fin.cast hkn)
            ((Fin.last (2 * r + k)).succAbove ∘ Fin.cast hkn) (om - 1) := by
        rw [CapelliMinorRestriction.cminor_reindex _ e he]
        congr 1 <;> funext i <;> exact Fin.ext (by simp [he_def, Fin.succAbove_last])
      rw [CapelliMinorRestriction.cminor_cast _ hkn] at hcm
      have h1 := LinearMap.congr_fun hB0 ⟨(v : D), hvS⟩
      simp only [LinearMap.comp_apply] at h1
      rw [hcm, hCD, hres] at h1
      rw [h1]
      have hprod0 : (∏ j : Fin k, (om - 1 + ((u j : ℝ) : ℂ) - ((k : ℂ) - 1) / 2)) ≠ 0 := by
        simpa [hr] using hprod
      exact smul_ne_zero hprod0 hlv
    · refine ⟨0, ?_⟩
      have hkn : k + 2 * r = 2 * r + k := by omega
      have hcapinj : Function.Injective (capIdx k r) := fun a' b' hab => by
        unfold capIdx at hab; exact Fin.cast_injective _ hab
      have hup' : ∀ a' b', Capelli.blk k r a' < Capelli.blk k r b' →
          l ∘ₗ (fun a' b' => CapelliMinorRestriction.resE (frameE Q E) S hSF (capIdx k r a') (capIdx k r b')) a' b' =
            ψ' a' b' • l := by
        intro a' b' hab
        apply LinearMap.ext
        intro m
        show L (((CapelliMinorRestriction.resE (frameE Q E) S hSF (capIdx k r a') (capIdx k r b') m : S) : D) : H) =
          ψ' a' b' • L ((m : D) : H)
        rw [hLdef]
        exact hup a' b' hab m m.2
      have hWW' : ∀ i j, l ∘ₗ (fun a' b' => CapelliMinorRestriction.resE (frameE Q E) S hSF (capIdx k r a') (capIdx k r b'))
          (Capelli.wIdx k r i) (Capelli.wIdx k r j) = Dk i j ∘ₗ l := by
        intro i j
        apply LinearMap.ext
        intro m
        show L (((CapelliMinorRestriction.resE (frameE Q E) S hSF (capIdx k r (Capelli.wIdx k r i)) (capIdx k r (Capelli.wIdx k r j)) m :
          S) : D) : H) = Dk i j (L ((m : D) : H))
        rw [hLdef]
        exact hWW i j m m.2
      have hB1 := Capelli.capelliB S Vp k r
        (fun a' b' => CapelliMinorRestriction.resE (frameE Q E) S hSF (capIdx k r a') (capIdx k r b')) Dk ψ' l (om - 1)
        (CapelliMinorRestriction.isGlRep_reindex _ (capIdx k r) hcapinj hRE) hr hup' hzero hWW'
      have hcm : Capelli.cminor (fun a' b' => CapelliMinorRestriction.resE (frameE Q E) S hSF (capIdx k r a') (capIdx k r b'))
          Fin.castSucc Fin.succ (om - 1) =
          Capelli.cminor (CapelliMinorRestriction.resE (frameE Q E) S hSF) ((Fin.last (2 * r + k)).succAbove ∘ Fin.cast hkn)
            ((0 : Fin (2 * r + k + 1)).succAbove ∘ Fin.cast hkn) (om - 1) := by
        rw [CapelliMinorRestriction.cminor_reindex _ (capIdx k r) hcapinj]
        congr 1 <;> funext i <;> exact Fin.ext (by simp [capIdx, Fin.succAbove_last])
      rw [CapelliMinorRestriction.cminor_cast _ hkn] at hcm
      have h1 := LinearMap.congr_fun hB1 ⟨(v : D), hvS⟩
      simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h1
      rw [hcm, hCD, hres] at h1
      rw [h1]
      exact smul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (hkap hr)) (smul_ne_zero hprod hlv)
  obtain ⟨j₀, hj₀⟩ := hnz
  refine ⟨Q⁻¹ *ᵥ Pi.single j₀ 1, ?_⟩
  rw [key j₀]
  exact smul_ne_zero (mul_ne_zero hc₀ (pow_ne_zero _ (by norm_num))) hj₀

end ReciprocityTheory.ChartRestriction.DS.Lap
