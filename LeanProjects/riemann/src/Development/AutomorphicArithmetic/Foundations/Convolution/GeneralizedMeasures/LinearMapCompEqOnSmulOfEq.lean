import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.TermEx
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.SideE
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.SmoothStar
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeightDiagPowLe
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.SumSmulApply
import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.G1St

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private theorem numeric_product_inequality (C₁ C₂ Y₀ Q : ℝ) (c₁ c₂ : ℕ) (hY : 1 ≤ Y₀) (hQ : 1 ≤ Q) :
    ∃ (p : ℕ) (C₀ : ℝ), 0 < p ∧ ∀ Y₁ : ℝ, 1 ≤ Y₁ → ∀ᶠ j : ℕ in atTop, ∀ m : ℕ, m ≤ j / p →
      C₁ * (Y₁ * Y₀ ^ m) ^ c₁ < 2 ^ j ∧ C₂ * (Y₁ * Y₀ ^ m * Q ^ j) ^ c₂ ≤ Real.exp (C₀ * j) := by
  obtain ⟨p, hp⟩ := pow_unbounded_of_one_lt (Y₀ ^ c₁) (show (1 : ℝ) < 3 / 2 by norm_num)
  have hpos : 0 < 2 * (Y₀ * Q) ^ c₂ := by positivity
  refine ⟨p + 1, Real.log (2 * (Y₀ * Q) ^ c₂), Nat.succ_pos _, fun Y₁ hY₁ => ?_⟩
  have h1 := (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 4 / 3 by norm_num)).eventually_gt_atTop (|C₁| * Y₁ ^ c₁)
  have h2 := (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)).eventually_gt_atTop (|C₂| * Y₁ ^ c₂)
  filter_upwards [h1, h2] with j h1 h2 m hm
  have hmj : m ≤ j := hm.trans (Nat.div_le_self _ _)
  have hpm : p * m ≤ j := by
    have := (Nat.le_div_iff_mul_le (Nat.succ_pos p)).1 hm
    nlinarith
  constructor
  · have h3 : (Y₀ ^ m) ^ c₁ ≤ (3 / 2 : ℝ) ^ j := by
      calc (Y₀ ^ m) ^ c₁ = (Y₀ ^ c₁) ^ m := by rw [← pow_mul, ← pow_mul, mul_comm]
        _ ≤ ((3 / 2 : ℝ) ^ p) ^ m := pow_le_pow_left₀ (by positivity) hp.le _
        _ = (3 / 2 : ℝ) ^ (p * m) := by rw [← pow_mul]
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) hpm
    calc C₁ * (Y₁ * Y₀ ^ m) ^ c₁ ≤ |C₁| * (Y₁ * Y₀ ^ m) ^ c₁ := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ = (|C₁| * Y₁ ^ c₁) * (Y₀ ^ m) ^ c₁ := by rw [mul_pow, mul_assoc]
      _ ≤ (|C₁| * Y₁ ^ c₁) * (3 / 2 : ℝ) ^ j := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ < (4 / 3 : ℝ) ^ j * (3 / 2 : ℝ) ^ j := mul_lt_mul_of_pos_right h1 (by positivity)
      _ = 2 ^ j := by rw [← mul_pow]; norm_num
  · have h3 : Y₀ ^ m ≤ Y₀ ^ j := pow_le_pow_right₀ hY hmj
    rw [mul_comm (Real.log _), Real.exp_nat_mul, Real.exp_log hpos]
    calc C₂ * (Y₁ * Y₀ ^ m * Q ^ j) ^ c₂ ≤ |C₂| * (Y₁ * Y₀ ^ m * Q ^ j) ^ c₂ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |C₂| * (Y₁ * Y₀ ^ j * Q ^ j) ^ c₂ := by gcongr
      _ = (|C₂| * Y₁ ^ c₂) * ((Y₀ * Q) ^ c₂) ^ j := by
          rw [mul_assoc Y₁, ← mul_pow, mul_pow Y₁, ← pow_mul, ← pow_mul, mul_comm j, mul_assoc]
      _ ≤ 2 ^ j * ((Y₀ * Q) ^ c₂) ^ j := mul_le_mul_of_nonneg_right h2.le (by positivity)
      _ = _ := by rw [← mul_pow]

private theorem sideCondition_split_place (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    (σ : E ≃ₐ[F] E) (hσ : ∀ τ, τ ∈ Subgroup.zpowers σ) (n : ℕ) (hn : 0 < n) (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure]
    (θ : Twist μ) (hθ : IsGalTwist σ θ) (q : Pl F) (w₀ : PlacesOver E q) (hq : Split E q) (ν : Fin n → ℤ) (hν : Good ν)
    (Y₀ : ℝ) (hY : 1 ≤ Y₀) :
    ∃ (p : ℕ) (C₀ : ℝ), 0 < p ∧ ∀ Y₁ : ℝ, 1 ≤ Y₁ → ∀ᶠ j : ℕ in atTop, ∀ m : ℕ, m ≤ j / p → ∀ f : TG E n,
      Sup w₀ ν j (Y₁ * Y₀ ^ m) f → Ell σ f ∧ ∀ x, Real.exp (C₀ * j) < qht x → twK θ f x = 0 := by
  obtain ⟨C₁, c₁, h1⟩ := UpperTheory.ConvolutionTheory.G.g1St F E σ hσ n hn
  obtain ⟨C₂, c₂, h2⟩ := UpperTheory.ConvolutionTheory.G.g2 F E σ hσ n hn
  obtain ⟨Q, hQ, h3⟩ := htTot F E n q w₀ ν
  obtain ⟨p, C₀, hp, h⟩ := numeric_product_inequality C₁ C₂ Y₀ Q c₁ c₂ hY hQ
  refine ⟨p, C₀, hp, fun Y₁ hY₁ => ?_⟩
  filter_upwards [h Y₁ hY₁] with j hj m hm f hf
  have hY' : 1 ≤ Y₁ * Y₀ ^ m := one_le_mul_of_one_le_of_one_le hY₁ (one_le_pow₀ hY)
  have hE : Ell σ f := h1 q w₀ hq ν hν.1.injective hν.2.1 hν.2.2 j _ hY' (hj m hm).1 f hf
  refine ⟨hE, fun x hx => ?_⟩
  by_contra hne
  have := h2 μ θ hθ f _ (one_le_mul_of_one_le_of_one_le hY' (one_le_pow₀ hQ)) (h3 j _ f hf) hE x hne
  exact absurd (this.trans (hj m hm).2) (not_le.2 hx)

private theorem exists_word_monomial {K : Type} [Field K] [NumberField K] {n : ℕ} (α : Option (Ix K n) →₀ ℕ) :
    ∃ wd : List (Option (Ix K n)), mono wd = monomial α 1 ∧ wd.length = α.degree := by
  classical
  refine ⟨α.toMultiset.toList, ?_, ?_⟩
  · rw [mono, Multiset.prod_map_toList, Finsupp.toMultiset_map, Finsupp.prod_toMultiset, monomial_eq, C_1, one_mul,
      Finsupp.prod_mapDomain_index (by simp) (fun _ _ _ => pow_add _ _ _)]
  · rw [Multiset.length_toList, Finsupp.card_toMultiset]; rfl

private theorem monomialDecomposition_eval {σ τ H : Type} [Ring H] [Algebra ℂ H] (ψ : MvPolynomial σ (MvPolynomial τ ℂ) →+* H)
    (hψ : ∀ c : ℂ, ψ (C (C c)) = c • 1) (g R : MvPolynomial σ (MvPolynomial τ ℂ)) :
    ψ (g * R) = ∑ i ∈ R.support.sigma (fun β => (R.coeff β).support),
      (R.coeff i.1).coeff i.2 • ψ (g * monomial i.1 (monomial i.2 1)) := by
  rw [Finset.sum_sigma]
  conv_lhs => rw [R.as_sum, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  conv_lhs => rw [(R.coeff β).as_sum, map_sum, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [← smul_one_mul, ← hψ, ← map_mul, mul_left_comm, C_mul_monomial, C_mul_monomial, mul_one]

private theorem linearMap_comp_eq_on_smul_of_eq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type} (s : Finset ι) (c : ι → ℂ)
    (A B G : V →L[ℂ] V) (P : ι → V →L[ℂ] V) :
    A ∘L ((∑ i ∈ s, c i • P i) ∘L B) ∘L G = ∑ i ∈ s, c i • (A ∘L (P i ∘L B) ∘L G) := by
  ext v
  simp [ContinuousLinearMap.sum_apply, map_sum]

private theorem self_over (F : Type) [Field F] [NumberField F] (q : Pl F) : q.asIdeal.LiesOver q.asIdeal :=
  ⟨by ext x; simp [Ideal.under_def, Ideal.mem_comap]⟩

private theorem split_self (F : Type) [Field F] [NumberField F] (q : Pl F) : Split F q := by
  rintro ⟨w, hw⟩
  have h : w = q := by
    apply HeightOneSpectrum.ext
    have := hw.over
    ext x
    rw [this]
    exact Iff.rfl
  subst h
  have hid : ∀ x, completionMap w w x = x := by
    intro x
    refine (HeightOneSpectrum.denseRange_algebraMap F w).induction_on x
      (isClosed_eq (continuous_completionMap w w) continuous_id) fun k => ?_
    exact completionMap_algebraMap w w k
  exact fun y => ⟨y, hid y⟩

private theorem gal_self (F : Type) [Field F] (τ : F ≃ₐ[F] F) : τ ∈ Subgroup.zpowers (1 : F ≃ₐ[F] F) := by
  have : τ = 1 := by ext x; exact τ.commutes x
  rw [this]; exact one_mem _

private theorem degree_le_totalDegree_of_mem_support {τ R : Type} [CommSemiring R] {p : MvPolynomial τ R} {d : τ →₀ ℕ} (h : d ∈ p.support) :
    d.degree ≤ p.totalDegree := by
  exact le_totalDegree h

set_option maxHeartbeats 1600000 in
theorem UpperTheory.ConvolutionTheory.GM.gm_of_unit :
    LocUnit → GM := by
  classical
  intro hU F E _ _ _ _ _ _ _ _ σ hσ hp n hn μE _ μF _ θ hθ q w₀ hq νE _ νF _ aE aF ci hci hAE hAF hAP
  let q₀ : PlacesOver F q := ⟨q, self_over F q⟩
  obtain ⟨κ₀, hκ₀, hT⟩ := termEx hU F E σ hσ hp n hn μE μF θ q w₀ q₀ hq νE νF aE aF ci hci hAP
  refine ⟨κ₀, hκ₀, fun L ν hν => ?_⟩
  obtain ⟨𝔢, h𝔢⟩ := sideE F E σ hσ hp n hn μE θ hθ q w₀ hq νE aE hAE L ν
  obtain ⟨𝔣, h𝔣⟩ := sideF F E σ hσ hp n hn μF q w₀ νF aF hAF L ν
  refine ⟨𝔢, 𝔣, h𝔢, h𝔣, fun w => (h𝔢.2.2.1 w).trans (h𝔣.2.2.1 _).symm, ?_⟩
  obtain ⟨Y₀, hY₀, hT⟩ := hT L ν hν 𝔢 𝔣 h𝔢 h𝔣
  obtain ⟨pE, CE, hpE, hE⟩ := sideCondition_split_place F E σ hσ n hn μE θ hθ q w₀ hq ν hν Y₀ hY₀
  obtain ⟨pF, CF, hpF, hF⟩ := sideCondition_split_place F F (1 : F ≃ₐ[F] F) (gal_self F) n hn μF (Twist.id μF) (UpperTheory.ConvolutionTheory.G.g0.2 F n μF) q q₀
    (split_self F q) ν hν Y₀ hY₀
  refine ⟨pE * pF, max CE CF, Nat.mul_pos hpE hpF, fun κ hκ t₀ ht₀ D => ?_⟩
  obtain ⟨γ, hγv, hγ0, hβ⟩ := hT κ hκ t₀ ht₀ D
  refine ⟨γ, hγv, hγ0, fun evE evF hvE hvF => ?_⟩
  let B : Finset (Pl E × Fin n →₀ ℕ) :=
    ((κ ×ˢ Finset.univ).finsupp fun _ => Finset.range (D + 1)).filter fun β => β.degree ≤ D
  have hY : ∀ β : Pl E × Fin n →₀ ℕ, ∃ Y₁ : ℝ, 1 ≤ Y₁ ∧ (β ∈ B → ∀ evE evF, 𝔢.toAmp.IsEv evE → 𝔣.toAmp.IsEv evF →
      ∀ (j : ℕ) (wd : List (Option (Ix E n))), ∃ (fE : TG E n) (fF : TG F n),
        Rop μE fE = 𝔢.toAmp.A ∘L (evE (map C γ * monomial β (mono wd)) ∘L 𝔢.Uq 0 ^ j) ∘L Rop μE 𝔢.g ∧
        Rop μF fF = 𝔣.toAmp.A ∘L (evF (bcPR F (map C γ * monomial β (mono wd))) ∘L 𝔣.Uq 0 ^ j) ∘L Rop μF 𝔣.g ∧
        Sup w₀ ν j (Y₁ * Y₀ ^ wd.length) fE ∧ Sup q₀ ν j (Y₁ * Y₀ ^ wd.length) fF ∧
        GMatch σ μE μF (κ₀ * ∏ v ∈ L.S, L.c v) fE fF) := by
    intro β
    by_cases hB : β ∈ B
    · obtain ⟨hB', hBd⟩ := Finset.mem_filter.1 hB
      have hB' := Finset.mem_finsupp_iff.1 hB'
      obtain ⟨Y₁, h1, h⟩ := hβ β (fun x hx => (Finset.mem_product.1 (hB'.1 hx)).1) hBd
      exact ⟨Y₁, h1, fun _ => h⟩
    · exact ⟨1, le_rfl, fun h => absurd h hB⟩
  choose Y₁ hY₁ hYs using hY
  have hev : ∀ᶠ j : ℕ in atTop, ∀ β ∈ B,
      (∀ m : ℕ, m ≤ j / pE → ∀ f : TG E n, Sup w₀ ν j (Y₁ β * Y₀ ^ m) f →
        Ell σ f ∧ ∀ x, Real.exp (CE * j) < qht x → twK θ f x = 0) ∧
      (∀ m : ℕ, m ≤ j / pF → ∀ f : TG F n, Sup q₀ ν j (Y₁ β * Y₀ ^ m) f →
        Ell (1 : F ≃ₐ[F] F) f ∧ ∀ x, Real.exp (CF * j) < qht x → twK (Twist.id μF) f x = 0) :=
    (Filter.eventually_all_finset B).2 fun β _ => (hE _ (hY₁ β)).and (hF _ (hY₁ β))
  filter_upwards [hev] with j hj R hRv hRd hRc
  set s := R.support.sigma fun β => (R.coeff β).support with hs
  set c : (Σ _ : Pl E × Fin n →₀ ℕ, Option (Ix E n) →₀ ℕ) → ℂ := fun i => (R.coeff i.1).coeff i.2 with hc
  have hZ : ∀ (C' : ℝ), C' ≤ max CE CF → Real.exp (C' * j) ≤ Real.exp (max CE CF * j) := fun C' h =>
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg _))
  have key : ∀ i : (Σ _ : Pl E × Fin n →₀ ℕ, Option (Ix E n) →₀ ℕ), ∃ (fE : TG E n) (fF : TG F n), i ∈ s →
      Rop μE fE = 𝔢.toAmp.A ∘L (evE (map C γ * monomial i.1 (monomial i.2 1)) ∘L 𝔢.Uq 0 ^ j) ∘L Rop μE 𝔢.g ∧
      Rop μF fF = 𝔣.toAmp.A ∘L (evF (bcPR F (map C γ * monomial i.1 (monomial i.2 1))) ∘L 𝔣.Uq 0 ^ j) ∘L Rop μF 𝔣.g ∧
      (∀ x, Real.exp (max CE CF * j) < qht x → twK θ fE x = 0) ∧
      (∀ x, Real.exp (max CE CF * j) < qht x → twK (Twist.id μF) fF x = 0) ∧
      twInt θ fE = (κ₀ * ∏ v ∈ L.S, L.c v) * twInt (Twist.id μF) fF := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨h1, h2⟩ := Finset.mem_sigma.1 hi
      have hdeg : i.1.degree ≤ D := (degree_le_totalDegree_of_mem_support h1).trans hRd
      have hβB : i.1 ∈ B := by
        refine Finset.mem_filter.2 ⟨Finset.mem_finsupp_iff.2 ⟨fun x hx => ?_, fun x _ => ?_⟩, hdeg⟩
        · exact Finset.mem_product.2 ⟨hRv x (mem_vars x |>.2 ⟨_, h1, hx⟩), Finset.mem_univ _⟩
        · exact Finset.mem_range.2 (Nat.lt_succ_of_le ((Finsupp.le_degree x i.1).trans hdeg))
      obtain ⟨wd, hwd, hlen⟩ := exists_word_monomial i.2
      have hm : wd.length ≤ j / (pE * pF) := by
        rw [hlen]
        exact (degree_le_totalDegree_of_mem_support h2).trans (hRc i.1)
      have hmE : wd.length ≤ j / pE := hm.trans (Nat.div_le_div_left (Nat.le_mul_of_pos_right _ hpF) hpE)
      have hmF : wd.length ≤ j / pF := hm.trans (Nat.div_le_div_left (Nat.le_mul_of_pos_left _ hpE) hpF)
      obtain ⟨fE, fF, e1, e2, e3, e4, e5⟩ := hYs i.1 hβB evE evF hvE hvF j wd
      rw [hwd] at e1 e2
      obtain ⟨l1, l2⟩ := (hj i.1 hβB).1 _ hmE fE e3
      obtain ⟨l3, l4⟩ := (hj i.1 hβB).2 _ hmF fF e4
      exact ⟨fE, fF, fun _ => ⟨e1, e2, fun x hx => l2 x ((hZ _ (le_max_left _ _)).trans_lt hx),
        fun x hx => l4 x ((hZ _ (le_max_right _ _)).trans_lt hx),
        UpperTheory.ConvolutionTheory.G.g3 F E σ hσ n hn μE μF θ hθ _ fE fF l1 l3 e5⟩⟩
    · exact ⟨0, 0, fun h => absurd h hi⟩
  choose fE fF hf using key
  obtain ⟨r1, r2, r3⟩ := twLin E n hn μE θ _ s c fE (Real.exp (max CE CF * j)) fun i hi => (hf i hi).2.2.1
  obtain ⟨t1, t2, t3⟩ := twLin F n hn μF (Twist.id μF) _ s c fF (Real.exp (max CE CF * j)) fun i hi => (hf i hi).2.2.2.1
  refine ⟨∑ i ∈ s, c i • fE i, ∑ i ∈ s, c i • fF i, ⟨?_, r2⟩, ⟨?_, t2⟩, ?_⟩
  · rw [r1, monomialDecomposition_eval evE hvE.const, linearMap_comp_eq_on_smul_of_eq]
    exact Finset.sum_congr rfl fun i hi => by rw [(hf i hi).1]
  · have hb : ∀ a : ℂ, (evF.comp (bcPR F : PR E n →+* PR F n)) (C (C a)) = a • 1 := fun a => by
      simpa [bcPR] using hvF.const a
    have := monomialDecomposition_eval (evF.comp (bcPR F : PR E n →+* PR F n)) hb (map C γ) R
    simp only [RingHom.comp_apply] at this
    rw [t1, this, linearMap_comp_eq_on_smul_of_eq]
    exact Finset.sum_congr rfl fun i hi => by rw [(hf i hi).2.1]
  · rw [r3, t3, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => by rw [(hf i hi).2.2.2.2, mul_left_comm]
