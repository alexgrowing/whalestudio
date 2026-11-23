import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.ConvSpec
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFin
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.UiwFin
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.PolyMem
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.NormIntLe
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CommPrj
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.RrTens
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.CompatEx
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.UiwPow
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.HopBasic

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM
open scoped InnerProductSpace

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem cf_mul (w : Pl K) (x y : AdelicGLn.FiniteAdelicGL K n) : cf w (x * y) = cf w x * cf w y := by
  simp only [cf, map_mul, finAt_mul]

private theorem cf_loc (w : Pl K) (y : GL (Fin n) (w.adicCompletion K)) :
    cf w (AdelicGLn.localEmbedding (K := K) (n := n) w y) = y :=
  (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).2.1 y

private theorem cf_loc_ne {w v : Pl K} (h : w ≠ v) (y : GL (Fin n) (v.adicCompletion K)) :
    cf w (AdelicGLn.localEmbedding (K := K) (n := n) v y) = 1 :=
  (UpperTheory.ConvolutionTheory.Tf.locEmb K n v).2.2.1 w h y

private noncomputable def ltr (a : AdelicGLn.FiniteAdelicGL K n) (e : TF K n) : TF K n :=
  ⟨⟨fun x => e (a * x), e.continuous.comp (continuous_const.mul continuous_id)⟩,
    e.hasCompactSupport.comp_homeomorph (Homeomorph.mulLeft a)⟩

private theorem exists_sum (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K)))
    (r : AdelicGLn.FiniteAdelicGL K n → ℂ) (hr : Free w r) (e₀ : TF K n)
    (h₀ : ∀ x, e₀ x = r x * (J : Set (GL (Fin n) (w.adicCompletion K))).indicator 1 (cf w x))
    (Q : Finset (GL (Fin n) (w.adicCompletion K) ⧸ J)) :
    ∃ e : TF K n, ∀ x, e x = r x * ∑ c ∈ Q,
      (J : Set (GL (Fin n) (w.adicCompletion K))).indicator (1 : GL (Fin n) (w.adicCompletion K) → ℂ) (c.out⁻¹ * cf w x) := by
  classical
  induction Q using Finset.induction_on with
  | empty => exact ⟨0, fun x => by simp⟩
  | insert c Q hc ih =>
    obtain ⟨e, he⟩ := ih
    refine ⟨e + ltr (AdelicGLn.localEmbedding w c.out⁻¹) e₀, fun x => ?_⟩
    have h1 : ltr (AdelicGLn.localEmbedding w c.out⁻¹) e₀ x =
        r x * (J : Set (GL (Fin n) (w.adicCompletion K))).indicator (1 : GL (Fin n) (w.adicCompletion K) → ℂ) (c.out⁻¹ * cf w x) := by
      show e₀ (AdelicGLn.localEmbedding w c.out⁻¹ * x) = _
      rw [h₀, hr, cf_mul, cf_loc]
    rw [Finset.sum_insert hc, CompactlySupportedContinuousMap.add_apply, he, h1]
    ring

private theorem exists_mid (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K)))
    (hJ : IsOpen (J : Set (GL (Fin n) (w.adicCompletion K))))
    (S : Set (GL (Fin n) (w.adicCompletion K))) (hS : IsCompact S) (hSJ : ∀ g ∈ S, ∀ k ∈ J, g * k ∈ S)
    (r : AdelicGLn.FiniteAdelicGL K n → ℂ) (hr : Free w r) (e₀ : TF K n)
    (h₀ : ∀ x, e₀ x = r x * (J : Set (GL (Fin n) (w.adicCompletion K))).indicator 1 (cf w x)) :
    ∃ e : TF K n, ∀ x, e x = r x * S.indicator 1 (cf w x) := by
  classical
  haveI : DiscreteTopology (GL (Fin n) (w.adicCompletion K) ⧸ J) := QuotientGroup.discreteTopology hJ
  have hmk : Continuous (QuotientGroup.mk : GL (Fin n) (w.adicCompletion K) → GL (Fin n) (w.adicCompletion K) ⧸ J) :=
    continuous_quotient_mk'
  have hfin : ((QuotientGroup.mk : GL (Fin n) (w.adicCompletion K) → GL (Fin n) (w.adicCompletion K) ⧸ J) '' S).Finite :=
    (hS.image hmk).finite_of_discrete
  obtain ⟨e, he⟩ := exists_sum w J r hr e₀ h₀ hfin.toFinset
  refine ⟨e, fun x => ?_⟩
  rw [he]
  congr 1
  set g := cf w x
  have hcos : ∀ c : GL (Fin n) (w.adicCompletion K) ⧸ J, c.out⁻¹ * g ∈ J ↔ c = QuotientGroup.mk g := fun c => by
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  by_cases hg : g ∈ S
  · rw [Set.indicator_of_mem hg, Finset.sum_eq_single (QuotientGroup.mk g)]
    · have hm : (QuotientGroup.mk g : GL (Fin n) (w.adicCompletion K) ⧸ J).out⁻¹ * g ∈ (J : Set (GL (Fin n) (w.adicCompletion K))) :=
        (hcos _).2 rfl
      rw [Set.indicator_of_mem hm]
      rfl
    · intro c _ hc
      exact Set.indicator_of_notMem (fun h => hc ((hcos c).1 h)) _
    · intro h
      exact absurd (hfin.mem_toFinset.2 ⟨g, hg, rfl⟩) h
  · rw [Set.indicator_of_notMem hg]
    refine Finset.sum_eq_zero fun c hc => Set.indicator_of_notMem (fun h => hg ?_) _
    obtain ⟨t, ht, rfl⟩ := hfin.mem_toFinset.1 hc
    have h2 := (hcos _).1 h
    have h3 : t⁻¹ * g ∈ J := QuotientGroup.eq.1 h2
    simpa using hSJ t ht _ h3

private theorem ofin_left (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure]
    (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure] (u : AdelicGLn.FiniteAdelicGL K n)
    (e : TF K n) (he : ∀ x, e (u * x) = e x) (v : LL μ) : rhoF μ u (Ofin μ m e v) = Ofin μ m e v := by
  have key : ∀ a b : LL μ, ⟪a, Ofin μ m e b⟫_ℂ = ∫ h, e h * ⟪a, rhoF μ h b⟫_ℂ ∂m := by
    intro a b
    unfold Ofin
    rw [UnitaryRep.inner_integrated]
    refine integral_congr_ae ((RightCosetSpace.coeFn_compactSupportToL1 m e).mono fun g hg => ?_)
    exact congrArg (· * _) hg
  refine ext_inner_left ℂ fun a => ?_
  have hadj : ⟪a, rhoF μ u (Ofin μ m e v)⟫_ℂ = ⟪rhoF μ u⁻¹ a, Ofin μ m e v⟫_ℂ := by
    rw [← (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.2.2.1 u, ContinuousLinearMap.adjoint_inner_left]
  rw [hadj, key, key]
  have h1 : ∀ h, e h * ⟪rhoF μ u⁻¹ a, rhoF μ h v⟫_ℂ = (fun h => e h * ⟪a, rhoF μ h v⟫_ℂ) (u * h) := by
    intro h
    have : rhoF μ (u * h) v = rhoF μ u (rhoF μ h v) := by
      rw [(UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.1 u h]; rfl
    show _ = e (u * h) * _
    rw [he, this, ← (UpperTheory.ConvolutionTheory.Tf.commPrj K n μ ⊥).2.2.2.2.2.2.2.1 u, ContinuousLinearMap.adjoint_inner_left]
  simp_rw [h1]
  exact integral_mul_left_eq_self (fun h => e h * ⟪a, rhoF μ h v⟫_ℂ) u

end SlopeTestRemainingChoices

section Aux2

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem iw_left (w : Pl K) (ν : Fin n → ℤ) {a : GL (Fin n) (w.adicCompletion K)}
    (ha : a ∈ GLnLocal.iwahori (w.adicCompletion K) n) (g : GL (Fin n) (w.adicCompletion K)) :
    a * g ∈ iwCoset w ν ↔ g ∈ iwCoset w ν := by
  constructor
  · rintro ⟨c, hc, b, hb, e⟩
    exact ⟨a⁻¹ * c, mul_mem (inv_mem ha) hc, b, hb, by
      simp only [mul_assoc] at e ⊢
      rw [← e, inv_mul_cancel_left]⟩
  · rintro ⟨c, hc, b, hb, rfl⟩
    exact ⟨a * c, mul_mem ha hc, b, hb, by simp only [mul_assoc]⟩

private theorem iw_ind (w : Pl K) (ν : Fin n → ℤ) {a : GL (Fin n) (w.adicCompletion K)}
    (ha : a ∈ GLnLocal.iwahori (w.adicCompletion K) n) (g : GL (Fin n) (w.adicCompletion K)) :
    (iwCoset w ν).indicator (1 : GL (Fin n) (w.adicCompletion K) → ℂ) (a * g) =
      (iwCoset w ν).indicator (1 : GL (Fin n) (w.adicCompletion K) → ℂ) g := by
  classical
  simp only [Set.indicator_apply, iw_left w ν ha g, Pi.one_apply]

private theorem iw_right (w : Pl K) (ν : Fin n → ℤ) {g k : GL (Fin n) (w.adicCompletion K)}
    (hg : g ∈ iwCoset w ν) (hk : k ∈ GLnLocal.iwahori (w.adicCompletion K) n) : g * k ∈ iwCoset w ν := by
  obtain ⟨c, hc, b, hb, rfl⟩ := hg
  exact ⟨c, hc, b * k, mul_mem hb hk, by simp only [mul_assoc]⟩

private theorem iw_compact (w : Pl K) (ν : Fin n → ℤ)
    (hI : IsCompact (GLnLocal.iwahori (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K)))) :
    IsCompact (iwCoset w ν) := by
  have e : iwCoset w ν = (fun q : GL (Fin n) (w.adicCompletion K) × GL (Fin n) (w.adicCompletion K) =>
      q.1 * Cartan.diagPow (w.adicCompletion K) n ν * q.2) ''
      ((GLnLocal.iwahori (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K))) ×ˢ
        (GLnLocal.iwahori (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K)))) := by
    ext g
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
  rw [e]
  exact (hI.prod hI).image ((continuous_fst.mul continuous_const).mul continuous_snd)

private theorem iw_zero (w : Pl K) :
    iwCoset w (0 : Fin n → ℤ) = (GLnLocal.iwahori (w.adicCompletion K) n : Set (GL (Fin n) (w.adicCompletion K))) := by
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [GroundTheory.Automorphic.Parabolic.diagPow_zero, mul_one]
    exact mul_mem ha hb
  · intro hg
    exact ⟨g, hg, 1, one_mem _, by rw [GroundTheory.Automorphic.Parabolic.diagPow_zero, mul_one, mul_one]⟩

variable {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]

private theorem comm_hop (B : LL μ →L[ℂ] LL μ) (hB : ∀ h, Commute B (rhoF μ h)) (w : Pl K)
    (J : Subgroup (GL (Fin n) (w.adicCompletion K))) (x : GL (Fin n) (w.adicCompletion K))
    (ho : IsOpen (J : Set (GL (Fin n) (w.adicCompletion K)))) (hc : IsCompact (J : Set (GL (Fin n) (w.adicCompletion K)))) :
    Commute B (Hop μ w J x) :=
  (UpperTheory.ConvolutionTheory.Tf.hopBasic K n μ w J x ho hc).2.2.2.2.1 B fun g => hB _

private theorem comm_ev (𝔞 : Amp μ) {ev : PR K n →+* (LL μ →L[ℂ] LL μ)} (hev : 𝔞.IsEv ev)
    (B : LL μ →L[ℂ] LL μ) (hB : ∀ h, Commute B (rhoF μ h)) {w : Pl K} (hw : w ∉ 𝔞.S)
    (q : MvPolynomial (Fin n) ℂ) : Commute B (ev (map C (atPl w q))) := by
  induction q using MvPolynomial.induction_on with
  | C a =>
    simp only [atPl, rename_C, map_C]
    rw [hev.const a]
    exact (Commute.one_right B).smul_right a
  | add p q hp hq =>
    simp only [atPl, map_add] at hp hq ⊢
    exact hp.add_right hq
  | mul_X p i hp =>
    simp only [atPl, map_mul, rename_X, map_X] at hp ⊢
    refine hp.mul_right ?_
    rw [hev.hecke w hw i]
    exact (comm_hop B hB w _ _ (GLnLocal.isOpen_integralGL _ n) (GLnLocal.isCompact_integralGL _ n)).smul_right _

end Aux2

set_option maxHeartbeats 1000000 in
theorem UpperTheory.ConvolutionTheory.GM.repOne :
    RepOne := by
  intro K _ _ _ n hn μ _ 𝔞 ev hev w₀ hw₀ ν hν T hT p h hsph r hr₀ hrT hU j wd e₀ e₁ h₀ h₁
  classical
  obtain ⟨m, hm, hC⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx K n hn).2.1 μ 𝔞.ν
  haveI := hm
  have hne : ∀ w ∈ T, w ≠ w₀ := fun w hw e => hT w hw (e ▸ hw₀)
  have hI := UpperTheory.ConvolutionTheory.Tf.uiwPow K n μ w₀ ν ν hν hν
  have hIo := hI.2.2.1
  have hIc := hI.2.2.2.1

  have hcf : ∀ w ∈ T, ∀ (y : GL (Fin n) (w₀.adicCompletion K)) (x : AdelicGLn.FiniteAdelicGL K n),
      cf w (AdelicGLn.localEmbedding w₀ y * x) = cf w x := fun w hw y x => by
    rw [cf_mul, cf_loc_ne (hne w hw), one_mul]
  have hcf' : ∀ w ∈ T, ∀ (y : GL (Fin n) (w.adicCompletion K)) (x : AdelicGLn.FiniteAdelicGL K n),
      cf w₀ (AdelicGLn.localEmbedding w y * x) = cf w₀ x := fun w hw y x => by
    rw [cf_mul, cf_loc_ne (hne w hw).symm, one_mul]
  set ind : AdelicGLn.FiniteAdelicGL K n → ℂ := fun x =>
    ∏ w ∈ T, (GLnLocal.integralGL (w.adicCompletion K) n : Set _).indicator 1 (cf w x) with hind
  have hindF : Free w₀ ind := fun y x =>
    Finset.prod_congr rfl fun w hw => by rw [hcf w hw]
  have hfree : Free w₀ (fun x => r x * ind x) := fun y x => by
    show r _ * ind _ = _
    rw [hr₀ y x, hindF y x]

  obtain ⟨e', he'⟩ := exists_mid w₀ (GLnLocal.iwahori (w₀.adicCompletion K) n) hIo
    (iwCoset w₀ fun i => (j : ℤ) * ν i) (iw_compact w₀ _ hIc) (fun g hg k hk => iw_right w₀ _ hg hk)
    (fun x => r x * ind x) hfree e₀ (fun x => by rw [h₀, iw_zero]; ring)
  have hH := UpperTheory.ConvolutionTheory.GM.heckeFin K n hn μ m 𝔞 ev hev T hT p h hsph
    (fun x => r x * (iwCoset w₀ fun i => (j : ℤ) * ν i).indicator 1 (cf w₀ x))
    (fun w hw y x => by
      show r _ * _ = r _ * _
      rw [hrT w hw y x, hcf' w hw]) e' e₁ (fun x => by rw [he']; ring) h₁
  have hUf := UpperTheory.ConvolutionTheory.GM.uiwFin K n hn μ m w₀ ν hν j (fun x => r x * ind x) hfree e₀ e'
    (fun x => by rw [h₀]; ring) he'

  have cp := UpperTheory.ConvolutionTheory.Tf.commPrj K n μ 𝔞.U
  have hinv : ∀ u ∈ 𝔞.U, ∀ x, e₁ (u * x) = e₁ x := fun u hu x => by
    obtain ⟨hu₁, hu₂⟩ := hU u hu
    have hint : ∀ w, cf w u ∈ GLnLocal.integralGL (w.adicCompletion K) n :=
      (AdelicGLn.mem_integralFiniteGL_iff_forall K n).1 (𝔞.le hu)
    rw [h₁, h₁, hu₂, cf_mul]
    congr 1
    · congr 1
      exact iw_ind w₀ _ hu₁ _
    · refine Finset.prod_congr rfl fun w hw => ?_
      rw [cf_mul]
      exact (((UpperTheory.ConvolutionTheory.GM.sphEx K n hn w).2.2 (p w) (h w) (hsph w hw)).2.2 _ (hint w) _).1
  have hP : prj (fixF μ 𝔞.U) * Ofin μ m e₁ = Ofin μ m e₁ :=
    ContinuousLinearMap.ext fun v => cp.2.2.2.1 _
      ((cp.2.1 _).2 fun u hu => ofin_left μ m u e₁ (hinv u hu) v)
  have hR := fun β : TI K n => (UpperTheory.ConvolutionTheory.Tf.opAlg K n μ 𝔞.ν m).2.2.2.2.2.2.2.2 β
  have hOP : ∀ β : TI K n, Commute (Oinf μ 𝔞.ν β) (prj (fixF μ 𝔞.U)) := fun β =>
    cp.2.2.2.2.2.2.2.2 _ fun u _ => hR β u
  have hconv : ∀ β γ : TI K n, Oinf μ 𝔞.ν (GM.conv 𝔞.ν β γ) = Oinf μ 𝔞.ν β * Oinf μ 𝔞.ν γ := fun β γ =>
    (UpperTheory.ConvolutionTheory.GM.convSpec K n hn 𝔞.ν β γ).2 μ
  have hlet : ∀ x, ev (C (X x)) = Oinf μ 𝔞.ν (letter 𝔞.a₀ x) * prj (fixF μ 𝔞.U) := by
    rintro (_ | x)
    · exact hev.amp
    · exact hev.cen x
  have hW : ∀ wd : List (Option (Ix K n)), Oinf μ 𝔞.ν (word 𝔞.ν 𝔞.a₀ wd) * Ofin μ m e₁ =
      ev (C (mono wd)) * (Oinf μ 𝔞.ν 𝔞.a₀ * Ofin μ m e₁) := by
    intro wd
    induction wd with
    | nil => simp [word, mono]
    | cons x w ih =>
      have hm1 : mono (x :: w) = X x * mono w := by simp [mono]
      calc Oinf μ 𝔞.ν (word 𝔞.ν 𝔞.a₀ (x :: w)) * Ofin μ m e₁
          = Oinf μ 𝔞.ν (letter 𝔞.a₀ x) * (Oinf μ 𝔞.ν (word 𝔞.ν 𝔞.a₀ w) * (prj (fixF μ 𝔞.U) * Ofin μ m e₁)) := by
            rw [hP, word, hconv, mul_assoc]
        _ = ev (C (X x)) * (Oinf μ 𝔞.ν (word 𝔞.ν 𝔞.a₀ w) * Ofin μ m e₁) := by
            rw [hlet, ← mul_assoc (Oinf μ 𝔞.ν (word 𝔞.ν 𝔞.a₀ w)), (hOP _).eq]
            simp only [mul_assoc]
        _ = ev (C (mono (x :: w))) * (Oinf μ 𝔞.ν 𝔞.a₀ * Ofin μ m e₁) := by
            rw [ih, hm1, C_mul, map_mul, mul_assoc]
  have hEv : Commute (Oinf μ 𝔞.ν 𝔞.a₀) (ev (map C (∏ w ∈ T, atPl w (p w)))) := by
    refine Finset.prod_induction _ (fun q => Commute (Oinf μ 𝔞.ν 𝔞.a₀) (ev (map C q))) ?_ ?_ ?_
    · intro a b ha hb
      rw [map_mul, map_mul]
      exact ha.mul_right hb
    · rw [map_one, map_one]
      exact Commute.one_right _
    · exact fun w hw => comm_ev 𝔞 hev _ (hR _) (hT w hw) _
  have hUj : Commute (Oinf μ 𝔞.ν 𝔞.a₀) (Uiw μ w₀ ν ^ j) :=
    (comm_hop _ (hR _) w₀ _ _ hIo hIc).pow_right j
  have hrr := fun β : TI K n => fun e : TF K n => UpperTheory.ConvolutionTheory.Tf.rrTens K n hn μ 𝔞.ν m hC β e
  rw [hrr, hrr]
  show Oinf μ 𝔞.ν (word 𝔞.ν 𝔞.a₀ (none :: wd)) * Ofin μ m e₁ =
    𝔞.A * ((ev (C (mono wd) * map C (∏ w ∈ T, atPl w (p w))) * Uiw μ w₀ ν ^ j) * (Oinf μ 𝔞.ν 𝔞.a₀ * Ofin μ m e₀))
  have hB : Ofin μ m e₁ = ev (map C (∏ w ∈ T, atPl w (p w))) * (Uiw μ w₀ ν ^ j * Ofin μ m e₀) := by
    rw [hH, hUf]; rfl
  have hA : 𝔞.A = Oinf μ 𝔞.ν 𝔞.a₀ * prj (fixF μ 𝔞.U) := rfl
  calc Oinf μ 𝔞.ν (word 𝔞.ν 𝔞.a₀ (none :: wd)) * Ofin μ m e₁
      = Oinf μ 𝔞.ν 𝔞.a₀ * (Oinf μ 𝔞.ν (word 𝔞.ν 𝔞.a₀ wd) * (prj (fixF μ 𝔞.U) * Ofin μ m e₁)) := by
        rw [hP, word, hconv, mul_assoc]; rfl
    _ = 𝔞.A * (Oinf μ 𝔞.ν (word 𝔞.ν 𝔞.a₀ wd) * Ofin μ m e₁) := by
        rw [hA, ← mul_assoc (Oinf μ 𝔞.ν (word 𝔞.ν 𝔞.a₀ wd)), (hOP _).eq]
        simp only [mul_assoc]
    _ = 𝔞.A * (ev (C (mono wd)) * (Oinf μ 𝔞.ν 𝔞.a₀ * Ofin μ m e₁)) := by rw [hW]
    _ = 𝔞.A * (ev (C (mono wd)) * (ev (map C (∏ w ∈ T, atPl w (p w))) * (Uiw μ w₀ ν ^ j * (Oinf μ 𝔞.ν 𝔞.a₀ * Ofin μ m e₀)))) := by
        rw [hB, ← mul_assoc (Oinf μ 𝔞.ν 𝔞.a₀), hEv.eq, mul_assoc, ← mul_assoc (Oinf μ 𝔞.ν 𝔞.a₀), hUj.eq, mul_assoc]
    _ = 𝔞.A * ((ev (C (mono wd) * map C (∏ w ∈ T, atPl w (p w))) * Uiw μ w₀ ν ^ j) * (Oinf μ 𝔞.ν 𝔞.a₀ * Ofin μ m e₀)) := by
        rw [map_mul]
        simp only [mul_assoc]
