import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.RepOne
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.TensF
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.TensHt
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.WordHt
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.PolyMem
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.TensApply
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

section SlopeTestRemainingChoices
open scoped Pointwise
variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem fp_split {ι : Type} [DecidableEq ι] (g : ι → ℂ) (hg : (Function.mulSupport g).Finite) (s : Finset ι) :
    ∏ᶠ v, g v = (∏ᶠ v, if v ∈ s then 1 else g v) * ∏ v ∈ s, g v := by
  have h1 : (Function.mulSupport fun v => if v ∈ s then 1 else g v).Finite :=
    hg.subset fun v hv => by
      by_cases h : v ∈ s
      · simp [h] at hv
      · simpa [h] using hv
  have h2 : (Function.mulSupport fun v => if v ∈ s then g v else 1) ⊆ s := fun v hv => by
    by_contra h
    have h' : v ∉ s := h
    simp [h'] at hv
  have h3 : ∏ v ∈ s, g v = ∏ᶠ v, if v ∈ s then g v else 1 := by
    rw [finprod_eq_prod_of_mulSupport_subset _ h2]
    exact Finset.prod_congr rfl fun v hv => by simp [hv]
  rw [h3, ← finprod_mul_distrib h1 (s.finite_toSet.subset h2)]
  exact finprod_congr fun v => by by_cases h : v ∈ s <;> simp [h]

private theorem fin_supp (S : Finset (Pl K)) (f : ∀ v : Pl K, GL (Fin n) (v.adicCompletion K) → ℂ)
    (hf : ∀ v ∉ S, f v = (GLnLocal.integralGL (v.adicCompletion K) n : Set _).indicator 1) (x : AdelicGLn.FiniteAdelicGL K n) :
    (Function.mulSupport fun v => f v (cf v x)).Finite := by
  have h := Filter.eventually_cofinite.1 (AdelicGLn.eventually_mem_integralGL K n (finEmb K n x))
  refine (h.union S.finite_toSet).subset fun v hv => ?_
  by_contra hc
  rw [Set.mem_union, not_or] at hc
  have h1 : cf v x ∈ GLnLocal.integralGL (v.adicCompletion K) n := not_not.1 hc.1
  apply hv
  simp only [hf v hc.2]
  exact Set.indicator_of_mem (by exact h1) _

private theorem cf_mul (w : Pl K) (x y : AdelicGLn.FiniteAdelicGL K n) : cf w (x * y) = cf w x * cf w y := by
  unfold cf; rw [map_mul, finAt_mul]

private theorem cf_loc {v w : Pl K} (h : w ≠ v) (y) (x : AdelicGLn.FiniteAdelicGL K n) :
    cf w (AdelicGLn.localEmbedding v y * x) = cf w x := by
  rw [cf_mul, cf, (UpperTheory.ConvolutionTheory.Tf.locEmb K n v).2.2.1 w h, one_mul]

private theorem cf_finPart (w : Pl K) (g : AdelicGLn.AdelicGL K n) : cf w (finPart K n g) = finAt w g := by
  ext i j
  rfl

private theorem infAt_finEmb' (w : InfinitePlace K) (x : AdelicGLn.FiniteAdelicGL K n) : infAt w (finEmb K n x) = 1 := by
  show (AdelicGLn.infiniteEquiv K n (AdelicGLn.prodEquiv K n (finEmb K n x)).1) w = 1
  rw [AutomorphicForm.prodEquiv_finEmb, map_one]
  rfl

private theorem iw_eq (w : Pl K) (ν : Fin n → ℤ) : iwCoset w ν =
    (GLnLocal.iwahori (w.adicCompletion K) n : Set _) * {Cartan.diagPow (w.adicCompletion K) n ν} *
      (GLnLocal.iwahori (w.adicCompletion K) n : Set _) := by
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨_, ⟨a, ha, _, rfl, rfl⟩, b, hb, rfl⟩
  · rintro ⟨_, ⟨a, ha, _, rfl, rfl⟩, b, hb, rfl⟩
    exact ⟨a, ha, b, hb, rfl⟩

private theorem iw_test (w : Pl K) (ν : Fin n → ℤ) :
    IsLocallyConstant ((iwCoset w ν).indicator 1 : GL (Fin n) (w.adicCompletion K) → ℂ) ∧ HasCompactSupport ((iwCoset w ν).indicator 1 : GL (Fin n) (w.adicCompletion K) → ℂ) := by
  have hc : IsCompact (iwCoset w ν) := by
    rw [iw_eq]
    exact ((GLnLocal.isCompact_iwahori _ n).mul isCompact_singleton).mul (GLnLocal.isCompact_iwahori _ n)
  have ho : IsOpen (iwCoset w ν) := by
    rw [iw_eq]
    exact (GLnLocal.isOpen_iwahori _ n).mul_left
  refine ⟨?_, HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _⟩
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  by_cases hx : x ∈ iwCoset w ν
  · exact ⟨_, ho, hx, fun y hy => by simp [Set.indicator_of_mem hx, Set.indicator_of_mem hy]⟩
  · exact ⟨_, hc.isClosed.isOpen_compl, hx, fun y hy => by
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]⟩

private theorem det_int (w : Pl K) {g : GL (Fin n) (w.adicCompletion K)} (hg : g ∈ GLnLocal.integralGL (w.adicCompletion K) n) :
    Valued.v (g : Matrix (Fin n) (Fin n) (w.adicCompletion K)).det = 1 := by
  have key : ∀ g ∈ GLnLocal.integralGL (w.adicCompletion K) n,
      Valued.v (g : Matrix (Fin n) (Fin n) (w.adicCompletion K)).det ≤ 1 := by
    intro g hg
    rw [GLnLocal.mem_integralGL_iff] at hg
    simp only [GroundTheory.Global.mem_valuationInteger_iff] at hg
    rw [Matrix.det_apply']
    exact (w.adicCompletionIntegers K).sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => hg.1 _ _)
  have h1 := key g hg
  have h2 := key _ (inv_mem hg)
  have h3 : Valued.v (g : Matrix (Fin n) (Fin n) (w.adicCompletion K)).det *
      Valued.v ((g⁻¹ : GL (Fin n) (w.adicCompletion K)) : Matrix (Fin n) (Fin n) (w.adicCompletion K)).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, map_one]
  refine le_antisymm h1 ?_
  calc (1 : _) = _ := h3.symm
    _ ≤ _ * 1 := mul_le_mul' le_rfl h2
    _ = _ := mul_one _

private theorem det_iw (w : Pl K) {ν : Fin n → ℤ} (hν : ∑ i, ν i = 0) {g : GL (Fin n) (w.adicCompletion K)} (hg : g ∈ iwCoset w ν) :
    Valued.v (g : Matrix (Fin n) (Fin n) (w.adicCompletion K)).det = 1 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, map_mul, map_mul,
    det_int w (GLnLocal.iwahori_le_integralGL _ n ha), det_int w (GLnLocal.iwahori_le_integralGL _ n hb), Cartan.coe_diagPow,
    Matrix.det_diagonal]
  have hz : ∀ (a : w.adicCompletion K), a ≠ 0 → ∀ s : Finset (Fin n), ∏ i ∈ s, a ^ ν i = a ^ ∑ i ∈ s, ν i := by
    intro a ha s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ ha]
  rw [hz _ (Cartan.uniformizer_ne_zero _), hν]
  simp

private theorem loc_bd (w : Pl K) {C : Set (GL (Fin n) (w.adicCompletion K))} (hC : IsCompact C) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ g ∈ C, locHeight g ≤ B := by
  have hc : Continuous (locHeight : GL (Fin n) (w.adicCompletion K) → ℝ) := by
    unfold locHeight
    refine continuous_const.max (NNReal.continuous_coe.comp (Continuous.finset_sup_apply (fun p _ => Continuous.max ?_ ?_)))
    · exact (Units.continuous_val.matrix_elem _ _).nnnorm
    · exact (Units.continuous_coe_inv.matrix_elem _ _).nnnorm
  obtain ⟨B, hB⟩ := (hC.image hc).bddAbove
  exact ⟨max 1 B, le_max_left _ _, fun g hg => (hB ⟨g, hg, rfl⟩).trans (le_max_right _ _)⟩

private theorem pl_self (q : Pl K) (w : PlacesOver K q) : w.1 = q := by
  have h := w.2
  refine HeightOneSpectrum.ext ?_
  have h2 : Ideal.under (𝓞 K) w.1.asIdeal = w.1.asIdeal := Ideal.comap_id _
  exact h2.symm.trans h.over.symm

private theorem below_self (w : Pl K) : AdeleBaseChange.below K w = w := by
  exact HeightOneSpectrum.ext (Ideal.comap_id _)

private theorem ht_le (q : Pl K) (T : Finset (Pl K)) (B : Pl K → ℝ) (hB : ∀ v, 1 ≤ B v) (x : AdelicGLn.FiniteAdelicGL K n)
    (h1 : ∀ v, v ≠ q → v ∈ T → locHeight (cf v x) ≤ B v) (h2 : ∀ v, v ≠ q → v ∉ T → locHeight (cf v x) = 1) :
    heightOff q (finEmb K n x) ≤ ∏ v ∈ T, B v := by
  classical
  unfold heightOff
  have hi : (∏ w : InfinitePlace K, locHeight (infAt w (finEmb K n x)) ^ w.mult) = 1 :=
    Finset.prod_eq_one fun w _ => by rw [infAt_finEmb', locHeight_one, one_pow]
  rw [hi, one_mul]
  have hg : ∀ w : Pl K, (∏ᶠ (_ : AdeleBaseChange.below K w ≠ q), locHeight (finAt w (finEmb K n x))) =
      if w ≠ q then locHeight (cf w x) else 1 := by
    intro w
    rw [below_self, finprod_eq_if]
    rfl
  simp only [hg]
  rw [finprod_eq_prod_of_mulSupport_subset (s := T)]
  · refine Finset.prod_le_prod (fun v _ => ?_) fun v hv => ?_
    · split_ifs
      · exact (locHeight_pos _).le
      · exact zero_le_one
    · split_ifs with hq
      · exact h1 v hq hv
      · exact hB v
  · intro v hv
    by_contra hc
    apply hv
    have hc' : v ∉ T := hc
    by_cases hq : v = q
    · simp [hq]
    · simp only [ne_eq, hq, not_false_eq_true, if_true]
      exact h2 v hq hc'

private theorem ind_inv {G : Type*} [Group G] (H : Subgroup G) {k : G} (hk : k ∈ H) (x : G) :
    (H : Set G).indicator (1 : G → ℂ) (k * x) = (H : Set G).indicator 1 x := by
  by_cases hx : x ∈ H
  · rw [Set.indicator_of_mem (show k * x ∈ (H : Set G) from mul_mem hk hx), Set.indicator_of_mem (show x ∈ (H : Set G) from hx)]
    rfl
  · rw [Set.indicator_of_notMem (show k * x ∉ (H : Set G) from fun h' => hx ((Subgroup.mul_mem_cancel_left _ hk).1 h')),
      Set.indicator_of_notMem (show x ∉ (H : Set G) from hx)]
end SlopeTestRemainingChoices
theorem UpperTheory.ConvolutionTheory.GM.termF :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F] [IsTotallyComplex E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μ : Measure (normOneGL F n)) [μ.IsHaarMeasure] (q : Pl F) (w₀ : PlacesOver E q) (q₀ : PlacesOver F q)
      (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (aF : TI F n) (L : Loc σ n q w₀) (ν : Fin n → ℤ), Good ν →
    ∀ 𝔣 : Side (Twist.id μ) (Module.finrank F E), IsSideF L νF aF ν 𝔣 → ∃ Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ κ : Finset (Pl F), (∀ w ∈ κ, w ∉ 𝔣.S) →
    ∀ (p : Pl F → MvPolynomial (Fin n) ℂ) (h : ∀ w : Pl F, GL (Fin n) (w.adicCompletion F) → ℂ), (∀ w ∈ κ, IsSph w (p w) (h w)) →
      (∀ w ∉ κ, h w = (GLnLocal.integralGL (w.adicCompletion F) n : Set _).indicator 1) → ∃ Y₁ : ℝ, 1 ≤ Y₁ ∧
    ∀ ev, 𝔣.toAmp.IsEv ev → ∀ (j : ℕ) (wd : List (Option (Ix F n))) (φ : ∀ v : Pl F, GL (Fin n) (v.adicCompletion F) → ℂ),
      (∀ v ∈ L.S, φ v = L.f v) → φ q = (iwCoset q fun i => (j : ℤ) * ν i).indicator 1 → (∀ v ∉ L.S, v ≠ q → φ v = h v) →
      ∃ f : TG F n, (∀ x, f x = avg (tensF (onInf (word νF aF (none :: wd))) φ) x) ∧
        Rop μ f = 𝔣.toAmp.A ∘L (ev (C (mono wd) * map C (∏ w ∈ κ, atPl w (p w))) ∘L 𝔣.Uq 0 ^ j) ∘L Rop μ 𝔣.g ∧
        Sup q₀ ν j (Y₁ * Y₀ ^ wd.length) f := by
  classical
  intro F E _ _ _ _ _ _ _ _ σ hσ hp n hn μ _ q w₀ q₀ νF _ aF L ν hν 𝔣 h𝔣
  obtain ⟨rfl, rfl, hS, hU, hg, hUq⟩ := h𝔣
  obtain ⟨q₁, hq₁⟩ := q₀
  obtain rfl : q₁ = q := pl_self q ⟨q₁, hq₁⟩
  have hqS : q₁ ∈ 𝔣.S := (hS _).2 (Or.inr rfl)
  have hLS : ∀ v ∈ L.S, v ∈ 𝔣.S := fun v hv => (hS v).2 (Or.inl hv)
  obtain ⟨Y, hY1, hY⟩ := wordHt F n hn 𝔣.ν 𝔣.a₀ 𝔣.smooth
  obtain ⟨c, hc⟩ := tensHt F F n hn q₁
  refine ⟨Y ^ c, one_le_pow₀ hY1, fun κ hκ p h hsph hoff => ?_⟩
  have hκS : ∀ v ∈ κ, v ∉ L.S := fun v hv hv' => hκ v hv (hLS v hv')
  have hκq : ∀ v ∈ κ, v ≠ q₁ := fun v hv hv' => hκ v hv (hv' ▸ hqS)
  set T : Finset (Pl F) := L.S ∪ κ with hT
  set ψ : ∀ v : Pl F, GL (Fin n) (v.adicCompletion F) → ℂ := fun v => if v ∈ L.S then L.f v else h v with hψ
  have hψt : ∀ v ∈ T, IsLocallyConstant (ψ v) ∧ HasCompactSupport (ψ v) := by
    intro v hv
    by_cases hvS : v ∈ L.S
    · simp only [hψ, hvS, if_true]
      exact ⟨(L.test v hvS).2.2.1, (L.test v hvS).2.2.2⟩
    · have hvk : v ∈ κ := (Finset.mem_union.1 hv).resolve_left hvS
      simp only [hψ, hvS, if_false]
      have := (sphEx F n hn v).2.2 (p v) (h v) (hsph v hvk)
      exact ⟨this.1, this.2.1⟩
  have hBex : ∀ v, ∃ b : ℝ, 1 ≤ b ∧ (v ∈ T → ∀ g, ψ v g ≠ 0 → locHeight g ≤ b) := by
    intro v
    by_cases hv : v ∈ T
    · obtain ⟨b, hb1, hb⟩ := loc_bd v (hψt v hv).2.isCompact
      exact ⟨b, hb1, fun _ g hg => hb g (subset_tsupport _ hg)⟩
    · exact ⟨1, le_rfl, fun h' => absurd h' hv⟩
  choose B hB1 hB using hBex
  obtain ⟨C₁, hC₁, hC⟩ := hc (∏ v ∈ T, B v) (Finset.prod_induction _ (fun x : ℝ => 1 ≤ x) (fun _ _ => one_le_mul_of_one_le_of_one_le) le_rfl fun v _ => hB1 v)
  refine ⟨C₁ * Y ^ (2 * c), one_le_mul_of_one_le_of_one_le hC₁ (one_le_pow₀ hY1), fun ev hev j wd φ hφS hφq hφo => ?_⟩
  set s : Finset (Pl F) := insert q₁ κ with hs
  have hφψ : ∀ v, v ≠ q₁ → φ v = ψ v := by
    intro v hv
    by_cases hvS : v ∈ L.S
    · simp only [hψ, hvS, if_true]; exact hφS v hvS
    · simp only [hψ, hvS, if_false]; exact hφo v hvS hv
  have hφoff : ∀ v ∉ insert q₁ T, φ v = (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1 := by
    intro v hv
    rw [Finset.mem_insert, not_or] at hv
    have hvS : v ∉ L.S := fun h' => hv.2 (Finset.mem_union_left _ h')
    have hvk : v ∉ κ := fun h' => hv.2 (Finset.mem_union_right _ h')
    rw [hφo v hvS hv.1, hoff v hvk]
  have hφt : ∀ v ∈ insert q₁ T, IsLocallyConstant (φ v) ∧ HasCompactSupport (φ v) := by
    intro v hv
    by_cases hvq : v = q₁
    · subst hvq
      rw [hφq]
      exact iw_test _ _
    · rw [hφψ v hvq]
      exact hψt v ((Finset.mem_insert.1 hv).resolve_left hvq)
  have hfoff : ∀ v ∉ insert q₁ L.S, L.f v = (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1 := by
    intro v hv
    rw [Finset.mem_insert, not_or] at hv
    exact (L.off v hv.2 hv.1).2.1
  have hft : ∀ v ∈ insert q₁ L.S, IsLocallyConstant (L.f v) ∧ HasCompactSupport (L.f v) := by
    intro v hv
    by_cases hvq : v = q₁
    · subst hvq
      rw [L.at_q.2.1]
      exact iw_test _ _
    · have := L.test v ((Finset.mem_insert.1 hv).resolve_left hvq)
      exact ⟨this.2.2.1, this.2.2.2⟩
  obtain ⟨e, -, he, hae⟩ := avgF F n hn (insert q₁ T) (word 𝔣.ν 𝔣.a₀ (none :: wd)) φ hφt hφoff
  obtain ⟨e₀, -, he₀, hae₀⟩ := avgF F n hn (insert q₁ L.S) 𝔣.a₀ L.f hft hfoff
  have hg₀ : 𝔣.g = tens 𝔣.a₀ e₀ := by
    ext x
    rw [hg x, hae₀ x]
  have hfs : ∀ x, (Function.mulSupport fun v => L.f v (cf v x)).Finite := fin_supp _ _ hfoff
  have hφs : ∀ x, (Function.mulSupport fun v => φ v (cf v x)).Finite := fin_supp _ _ hφoff
  set r : AdelicGLn.FiniteAdelicGL F n → ℂ := fun x => ∏ᶠ v, if v ∈ s then 1 else L.f v (cf v x) with hr
  have hfree : ∀ w ∈ s, Free w r := by
    intro w hw y x
    refine finprod_congr fun v => ?_
    by_cases hv : v ∈ s
    · simp [hv]
    · have hvw : v ≠ w := fun h' => hv (h' ▸ hw)
      simp only [hv, if_false, cf_loc hvw]
  have hφr : ∀ v ∉ s, φ v = L.f v := by
    intro v hv
    rw [Finset.mem_insert, not_or] at hv
    by_cases hvS : v ∈ L.S
    · exact hφS v hvS
    · rw [hφo v hvS hv.1, hoff v hv.2, (L.off v hvS hv.1).2.1]
  have hkap : ∀ v ∈ κ, L.f v = (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1 :=
    fun v hv => (L.off v (hκS v hv) (hκq v hv)).2.1
  have hq₁κ : q₁ ∉ κ := fun h' => hκq _ h' rfl
  have hform₀ : ∀ x, e₀ x = r x * (iwCoset q₁ 0).indicator 1 (cf q₁ x) *
      ∏ w ∈ κ, (GLnLocal.integralGL (w.adicCompletion F) n : Set _).indicator 1 (cf w x) := by
    intro x
    rw [he₀, fp_split _ (hfs x) s, hs, Finset.prod_insert hq₁κ, L.at_q.2.1, mul_assoc]
    refine congrArg₂ _ rfl (congrArg₂ _ rfl (Finset.prod_congr rfl fun v hv => by rw [hkap v hv]))
  have hform₁ : ∀ x, e x = r x * (iwCoset q₁ fun i => (j : ℤ) * ν i).indicator 1 (cf q₁ x) * ∏ w ∈ κ, h w (cf w x) := by
    intro x
    rw [he, fp_split _ (hφs x) s]
    have hrx : (∏ᶠ v, if v ∈ s then (1 : ℂ) else φ v (cf v x)) = r x := finprod_congr fun v => by
      by_cases hv : v ∈ s
      · simp only [hv, if_true]
      · simp only [hv, if_false]
        rw [hφr v hv]
    rw [hrx, hs, Finset.prod_insert hq₁κ, hφq, mul_assoc]
    refine congrArg₂ _ rfl (congrArg₂ _ rfl (Finset.prod_congr rfl fun v hv => ?_))
    rw [hφψ v (hκq v hv)]
    simp only [hψ, hκS v hv, if_false]
  have hUc : ∀ u ∈ 𝔣.toAmp.U, cf q₁ u ∈ GLnLocal.iwahori (q₁.adicCompletion F) n ∧ ∀ x, r (u * x) = r x := by
    intro u hu
    rw [hU] at hu
    have hu' : ∀ v, cf v u ∈ L.UF v := hu
    refine ⟨L.at_q.2.2.2 ▸ hu' q₁, fun x => finprod_congr fun v => ?_⟩
    by_cases hv : v ∈ s
    · simp [hv]
    · simp only [hv, if_false, cf_mul]
      rw [Finset.mem_insert, not_or] at hv
      by_cases hvS : v ∈ L.S
      · exact (L.inv v hvS).2 _ (hu' v) _
      · obtain ⟨-, h2, -, h4⟩ := L.off v hvS hv.1
        have hk : cf v u ∈ GLnLocal.integralGL (v.adicCompletion F) n := h4 ▸ hu' v
        rw [h2]
        exact ind_inv _ hk _
  have hne : ∀ x, e x ≠ 0 → ∀ v, φ v (cf v x) ≠ 0 := by
    intro x hx v h0
    apply hx
    rw [he]
    exact finprod_eq_zero _ v h0 (hφs x)
  have hsum : ∑ i, (fun i => (j : ℤ) * ν i) i = 0 := by
    simp only [← Finset.mul_sum, hν.2.1, mul_zero]
  have hwq : ∀ x, e x ≠ 0 → cf q₁ x ∈ iwCoset q₁ (fun i => (j : ℤ) * ν i) := by
    intro x hx
    have := hne x hx q₁
    rw [hφq] at this
    exact Set.mem_of_indicator_ne_zero this
  have hsup := hC (word 𝔣.ν 𝔣.a₀ (none :: wd)) e (Y ^ (wd.length + 2)) (one_le_pow₀ hY1)
    (fun g hg => by simpa using hY (none :: wd) g hg) (fun x hx => ⟨?_, ?_⟩)
  · refine ⟨tens (word 𝔣.ν 𝔣.a₀ (none :: wd)) e, hae, ?_, ?_⟩
    · rw [hUq, hg₀]
      exact repOne F n hn μ 𝔣.toAmp ev hev q₁ hqS ν hν.1.antitone κ hκ p h hsph r (hfree q₁ (Finset.mem_insert_self _ _))
        (fun w hw => hfree w (Finset.mem_insert_of_mem hw)) hUc j wd e₀ e hform₀ hform₁
    · intro g hfg
      obtain ⟨h1, h2⟩ := hsup g hfg
      refine ⟨h1.trans (le_of_eq ?_), ?_, fun w hw => absurd (Subtype.ext (pl_self q₁ w)) hw⟩
      · rw [mul_assoc, ← pow_mul, ← pow_mul, ← pow_add]
        congr 2
        ring
      · rw [← cf_finPart]
        exact hwq _ h2
  · refine ht_le q₁ T B hB1 x (fun v hvq hvT => hB v hvT _ ?_) (fun v hvq hvT => ?_)
    · rw [← hφψ v hvq]; exact hne x hx v
    · have h1 := hne x hx v
      rw [hφoff v (by simp [hvq, hvT])] at h1
      exact locHeight_eq_one_of_mem_integralGL (Set.mem_of_indicator_ne_zero h1)
  · intro w
    obtain ⟨w, hw⟩ := w
    obtain rfl : w = q₁ := pl_self q₁ ⟨w, hw⟩
    exact det_iw _ hsum (hwq x hx)
