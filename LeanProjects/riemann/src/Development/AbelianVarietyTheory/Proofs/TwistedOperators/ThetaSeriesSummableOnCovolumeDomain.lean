import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictIsotropicQuotientWittTowerPropertieStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilator
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SymplecticAdelicFormBiadditiveAlternatingRationa
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ThetaNormSqSumHeisenbergTranslatesDistinctChars
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsInvariantForm

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.OrientedHeis GlobalTheory.FockCompare
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwFour

theorem hasSum_coefficients (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G)
    [DiscreteTopology Γ] (K : Set G) (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K) (A : Type) [AddCommGroup A]
    [Countable A] (χ : A → G → ℂ) (hc : ∀ a, Continuous (χ a)) (hx : ∀ a x y, χ a (x + y) = χ a x * χ a y)
    (ha : ∀ a b x, χ (a + b) x = χ a x * χ b x) (h0 : ∀ x, χ 0 x = 1) (hn : ∀ a x, ‖χ a x‖ = 1)
    (hker : ∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) (hinj : ∀ a, (∀ x, χ a x = 1) → a = 0) (μ : Measure G) (𝓕 : Set G)
    (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ) (h1 : μ 𝓕 = 1) (Φ : G → ℂ) (hΦ : Continuous Φ)
    (hper : ∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) (hs : Summable fun a => ‖∫ x in 𝓕, χ a x * Φ x ∂μ‖) :
    HasSum (fun a => ∫ x in 𝓕, χ a x * Φ x ∂μ) (Φ 0) := by
  classical
  have hΓc : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hfin : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  set c : A → ℂ := fun a => ∫ x in 𝓕, χ a x * Φ x ∂μ with hcdef
  have hχ0 : ∀ a, χ a 0 = 1 := fun a => by
    have h2 := hx a 0 0
    rw [add_zero] at h2
    have hne : χ a 0 ≠ 0 := fun h => by simpa [h] using hn a 0
    have h3 : χ a 0 * χ a 0 = χ a 0 * 1 := by rw [mul_one]; exact h2.symm
    exact mul_left_cancel₀ hne h3
  have hperχ : ∀ a, ∀ γ ∈ Γ, ∀ x, χ a (γ + x) = χ a x := fun a γ hγ x => by
    rw [hx, (hker γ).2 hγ a, one_mul]
  have hbound : ∀ a x, ‖c a * χ (-a) x‖ = ‖c a‖ := fun a x => by rw [norm_mul, hn, mul_one]
  let S : G → ℂ := fun x => ∑' a, c a * χ (-a) x
  have hSc : Continuous S := continuous_tsum (fun a => continuous_const.mul (hc _)) hs fun a x => (hbound a x).le
  have hSper : ∀ γ ∈ Γ, ∀ x, S (γ + x) = S x := fun γ hγ x => by
    simp only [S, hperχ _ γ hγ]
  have horth : ∀ d, d ≠ 0 → ∫ x in 𝓕, χ d x ∂μ = 0 := fun d hd => by
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, χ d x₀ ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact hd (hinj d hcon)
    have e := GlobalTheory.HeisOrtho.setIntegral_add_right Γ μ 𝓕 h𝓕 (χ d) (hperχ d) x₀
    simp only [hx, integral_mul_const] at e
    have : (∫ x in 𝓕, χ d x ∂μ) * (χ d x₀ - 1) = 0 := by rw [mul_sub, e, mul_one, sub_self]
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hx₀)
  have hvol : ∫ _ in 𝓕, (1 : ℂ) ∂μ = 1 := by simp [Measure.real, h1]
  have hbddint : ∀ (g : G → ℂ) (C : ℝ), Continuous g → (∀ x, ‖g x‖ ≤ C) → Integrable g (μ.restrict 𝓕) :=
    fun g C hg hC => Integrable.of_bound hg.aestronglyMeasurable C (.of_forall hC)
  have hΦb : ∃ C, ∀ x, ‖Φ x‖ ≤ C := by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΦ.continuousOn
    refine ⟨C, fun x => ?_⟩
    obtain ⟨γ, hγ, h⟩ := hcov x
    rw [← hper γ hγ x]
    exact hC _ h
  obtain ⟨CΦ, hCΦ⟩ := hΦb
  have hSb : ∀ x, ‖S x‖ ≤ ∑' a, ‖c a‖ := fun x => by
    refine (norm_tsum_le_tsum_norm ?_).trans_eq (tsum_congr fun a => hbound a x)
    simpa only [hbound] using hs.congr fun a => (hbound a x).symm ▸ rfl
  have hcoefS : ∀ b, ∫ x in 𝓕, χ b x * S x ∂μ = c b := fun b => by
    have hF : ∀ a, Integrable (fun x => c a * (χ (b + -a) x)) (μ.restrict 𝓕) := fun a =>
      hbddint _ ‖c a‖ (continuous_const.mul (hc _)) fun x => by rw [norm_mul, hn, mul_one]
    have hsum : Summable fun a => ∫ x, ‖c a * χ (b + -a) x‖ ∂(μ.restrict 𝓕) := by
      have e : ∀ a, ∫ x, ‖c a * χ (b + -a) x‖ ∂(μ.restrict 𝓕) = ‖c a‖ := fun a => by
        simp only [norm_mul, hn, mul_one]
        simp [Measure.real, h1]
      simpa only [e] using hs
    have key := hasSum_integral_of_summable_integral_norm hF hsum
    have e2 : (fun x => ∑' a, c a * χ (b + -a) x) = fun x => χ b x * S x := by
      funext x
      simp only [S, ← tsum_mul_left, ha]
      exact tsum_congr fun a => by ring
    rw [e2] at key
    refine key.unique ?_
    have e3 : (fun a => ∫ x in 𝓕, c a * χ (b + -a) x ∂μ) = fun a => if a = b then c b else 0 := by
      funext a
      rw [integral_const_mul]
      split_ifs with h
      · subst h
        simp only [add_neg_cancel, h0, hvol, mul_one]
      · rw [horth _ (fun h' => h (by rw [add_neg_eq_zero] at h'; exact h'.symm)), mul_zero]
    rw [e3]
    exact hasSum_ite_eq b (c b)
  have hz : (fun x => Φ x - S x) = 0 := by
    refine GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero G Γ K hK hcov A χ hc hx ha h0 hn hker μ 𝓕 hμ h𝓕 _
      (hΦ.sub hSc) (fun γ hγ x => by rw [hper γ hγ, hSper γ hγ]) fun a => ?_
    have i1 : Integrable (fun x => χ a x * Φ x) (μ.restrict 𝓕) :=
      hbddint _ CΦ ((hc a).mul hΦ) fun x => by rw [norm_mul, hn, one_mul]; exact hCΦ x
    have i2 : Integrable (fun x => χ a x * S x) (μ.restrict 𝓕) :=
      hbddint _ _ ((hc a).mul hSc) fun x => by rw [norm_mul, hn, one_mul]; exact hSb x
    simp only [mul_sub]
    rw [integral_sub i1 i2, hcoefS, sub_self]
  have e0 : Φ 0 = ∑' a, c a := by
    have := congrFun hz 0
    simp only [Pi.zero_apply, sub_eq_zero] at this
    rw [this]
    exact tsum_congr fun a => by rw [hχ0, mul_one]
  rw [e0]
  exact hs.of_norm.hasSum

theorem summable_norm_of_lattice {Y : Type} {n : ℕ} (T : Y → ℂ) (ℓ : Y → Fin n → ℝ) (hinj : Function.Injective ℓ)
    (hint : ∀ y, T y ≠ 0 → ∀ i, ∃ k : ℤ, ℓ y i = k) (C : ℝ)
    (hC : ∀ y, (∏ i, (1 + ℓ y i ^ 2)) * ‖T y‖ ≤ C) : Summable fun y => ‖T y‖ := by
  classical
  let g : ℤ → ℝ := fun k => (1 + (k : ℝ) ^ 2)⁻¹
  have hg0 : ∀ k, 0 ≤ g k := fun k => by positivity
  have hg : Summable g := by
    have h2 : Summable fun k : ℤ => ((|(k : ℝ)|) ^ 2)⁻¹ := by
      have := (Real.summable_one_div_int_pow (p := 2)).2 one_lt_two
      refine this.congr fun k => ?_
      simp [sq_abs]
    refine Summable.of_nonneg_of_le hg0 (fun k => ?_) (h2.add (summable_of_finite_support (f := fun k : ℤ => if k = 0 then (1 : ℝ) else 0)
      ((Set.finite_singleton (0 : ℤ)).subset fun k hk => by simpa using hk)))
    by_cases hk : k = 0
    · simp [g, hk]
    · have hpos : 0 < (k : ℝ) ^ 2 := by positivity
      simp only [g, hk, if_false, add_zero, sq_abs]
      exact inv_anti₀ hpos (by linarith)
  let b : (Fin n → ℤ) → ℝ := fun k => ∏ i, g (k i)
  have hb0 : ∀ k, 0 ≤ b k := fun k => Finset.prod_nonneg fun i _ => hg0 _
  have hb : Summable b := by
    refine summable_of_sum_le hb0 (c := (∑' k, g k) ^ n) fun s => ?_
    let t : Fin n → Finset ℤ := fun i => s.image fun k => k i
    have hsub : s ⊆ Fintype.piFinset t := fun k hk => Fintype.mem_piFinset.2 fun i =>
      Finset.mem_image_of_mem _ hk
    calc ∑ k ∈ s, b k ≤ ∑ k ∈ Fintype.piFinset t, b k := Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => hb0 _
      _ = ∏ i, ∑ k ∈ t i, g k := (Finset.prod_univ_sum t fun _ => g).symm
      _ ≤ ∏ _i : Fin n, ∑' k, g k := Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun _ _ => hg0 _)
          fun i _ => hg.sum_le_tsum _ fun _ _ => hg0 _
      _ = (∑' k, g k) ^ n := by simp
  have hsupp : ∀ y : Function.support T, ∃ k : Fin n → ℤ, ∀ i, ℓ y i = k i := fun y => by
    choose k hk using hint y y.2
    exact ⟨k, hk⟩
  choose e he using hsupp
  have hei : Function.Injective e := fun y y' h => Subtype.ext (hinj (funext fun i => by rw [he, he, h]))
  have hsum : Summable fun y : Function.support T => ‖T y‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun y => ?_) ((hb.comp_injective hei).mul_left C)
    have hprod : ∏ i, (1 + ℓ y i ^ 2) = (b (e y))⁻¹ := by
      simp only [b, g, Finset.prod_inv_distrib, inv_inv, he]
    have hpos : 0 < b (e y) := Finset.prod_pos fun i _ => by positivity
    have h := hC y
    rw [hprod] at h
    simp only [Function.comp_apply]
    rw [inv_mul_le_iff₀ hpos] at h
    linarith [mul_comm (b (e y)) C]
  have hs2 : Function.support (fun y => ‖T y‖) = Function.support T := by
    ext y; simp
  have h3 := (summable_subtype_iff_indicator (f := fun y => ‖T y‖) (s := Function.support T)).1 hsum
  rwa [← hs2, Set.indicator_support] at h3

theorem prod_bound {Fn Y ι : Type} [DecidableEq ι] (P : Fn → Prop) (Dop : ι → Fn → Fn) (hP : ∀ i f, P f → P (Dop i f))
    (T : Y → Fn → ℂ) (hb : ∀ f, P f → ∃ C, ∀ y, ‖T y f‖ ≤ C) (ℓ : Y → ι → ℝ)
    (hrel : ∀ i f y, P f → |ℓ y i| * ‖T y f‖ ≤ ‖T y (Dop i f)‖) (s : Finset ι) :
    ∀ f, P f → ∃ C, ∀ y, (∏ i ∈ s, (1 + ℓ y i ^ 2)) * ‖T y f‖ ≤ C := by
  induction s using Finset.induction_on with
  | empty =>
    intro f hf
    obtain ⟨C, hC⟩ := hb f hf
    exact ⟨C, fun y => by simpa using hC y⟩
  | insert i s hi ih =>
    intro f hf
    obtain ⟨C₁, h₁⟩ := ih f hf
    obtain ⟨C₂, h₂⟩ := ih _ (hP i _ (hP i f hf))
    refine ⟨C₁ + C₂, fun y => ?_⟩
    rw [Finset.prod_insert hi]
    have hp : 0 ≤ ∏ j ∈ s, (1 + ℓ y j ^ 2) := Finset.prod_nonneg fun j _ => by positivity
    have e1 := hrel i f y hf
    have e2 := hrel i _ y (hP i f hf)
    have e3 : ℓ y i ^ 2 * ‖T y f‖ ≤ ‖T y (Dop i (Dop i f))‖ := by
      calc ℓ y i ^ 2 * ‖T y f‖ = |ℓ y i| * (|ℓ y i| * ‖T y f‖) := by rw [← mul_assoc, abs_mul_abs_self, sq]
        _ ≤ |ℓ y i| * ‖T y (Dop i f)‖ := mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
        _ ≤ _ := e2
    have e4 := mul_le_mul_of_nonneg_left e3 hp
    calc (1 + ℓ y i ^ 2) * (∏ j ∈ s, (1 + ℓ y j ^ 2)) * ‖T y f‖
        = (∏ j ∈ s, (1 + ℓ y j ^ 2)) * ‖T y f‖ + (∏ j ∈ s, (1 + ℓ y j ^ 2)) * (ℓ y i ^ 2 * ‖T y f‖) := by ring
      _ ≤ C₁ + C₂ := add_le_add (h₁ y) (e4.trans (h₂ y))

section Heis

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}

theorem heisO_comm (a b : WO V W) (g : WO V W → ℂ) :
    heisO ψ V W a (heisO ψ V W b g) = ψ (symplO V W a b) • heisO ψ V W b (heisO ψ V W a g) := by
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]; norm_num
  have e : symplOH V W a b = symplO V W a b + symplOH V W b a := by
    unfold symplOH
    rw [symplO_skew a b]
    have : symplO V W a b = algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 * symplO V W a b := by rw [h2, one_mul]
    nth_rewrite 2 [this]
    ring
  rw [heisO_heisO, heisO_heisO, add_comm b a, smul_smul, ← ψ.map_add_eq_mul, ← e]

theorem integral_dLine_eq_zero (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) {L : ℝ →+ WO V W} (hL : Formalism.L2.Theta.IsRealDir W V L)
    {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
    (A : X → WO V W) (hA : Continuous A) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (hinv : ∀ t, ∫ x, heisO ψ V W (L t) f (A x) ∂ν = ∫ x, f (A x) ∂ν) :
    ∫ x, dLine ψ V W L f (A x) ∂ν = 0 := by
  have hd := theta_dLine hθ hψ hL hf
  obtain ⟨C, hC⟩ := theta_bounded hψ hd
  obtain ⟨C₀, hC₀⟩ := theta_bounded hψ hf
  have h0 : ∀ g : WO V W → ℂ, heisO ψ V W (L 0) g = g := fun g => by rw [map_zero, heisO_zero]
  have hmeas : ∀ {g : WO V W → ℂ}, IsThetaFunO ψ V W g → AEStronglyMeasurable (fun x => g (A x)) ν :=
    fun hg => (hg.cont.comp hA).aestronglyMeasurable
  have key := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (𝕜 := ℝ) (x₀ := (0 : ℝ))
    (s := Set.univ) (bound := fun _ => C) (F := fun t x => heisO ψ V W (L t) f (A x))
    (F' := fun t x => heisO ψ V W (L t) (dLine ψ V W L f) (A x)) Filter.univ_mem
    (.of_forall fun t => hmeas (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf _))
    (by
      simp only [h0]
      exact Integrable.of_bound (hmeas hf) C₀ (.of_forall fun x => hC₀ _))
    (by simp only [h0]; exact hmeas hd)
    (.of_forall fun x t _ => by
      rw [heisO, norm_mul, hψ.1.2.1, one_mul]
      exact hC _)
    (integrable_const C)
    (.of_forall fun x t _ => hasDerivAt_heisO hθ hψ hL hf (A x) t)).2
  simp only [hinv, h0] at key
  exact key.unique (hasDerivAt_const _ _)

theorem dLine_heisO (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) {L : ℝ →+ WO V W} (hL : Formalism.L2.Theta.IsRealDir W V L)
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (u : WO V W) (c : ℂ)
    (hc : ∀ t : ℝ, ψ (symplO V W (L t) u) = Complex.exp (t * c)) :
    dLine ψ V W L (heisO ψ V W u f) = c • heisO ψ V W u f + heisO ψ V W u (dLine ψ V W L f) := by
  funext w
  have e : (fun t : ℝ => heisO ψ V W (L t) (heisO ψ V W u f) w) = fun t : ℝ =>
      Complex.exp (t * c) * (ψ (symplOH V W w u) * heisO ψ V W (L t) f (w + u)) := by
    funext t
    rw [heisO_comm, hc, Pi.smul_apply, smul_eq_mul]
    rfl
  have h1 : HasDerivAt (fun t : ℝ => Complex.exp (t * c)) c 0 := by
    have h := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const c).cexp
    simpa using h
  have h2 := hasDerivAt_heisO hθ hψ hL hf (w + u) 0
  rw [map_zero, heisO_zero] at h2
  have h3 := h1.mul (h2.const_mul (ψ (symplOH V W w u)))
  unfold dLine at h3 ⊢
  rw [e]
  refine (HasDerivAt.deriv (f := fun t : ℝ => Complex.exp (t * c) * (ψ (symplOH V W w u) * heisO ψ V W (L t) f (w + u))) h3).trans ?_
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul, map_zero, heisO_zero, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  rfl

variable {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
  (A : X → WO V W)

theorem coef_rel (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) {L : ℝ →+ WO V W} (hL : Formalism.L2.Theta.IsRealDir W V L)
    (hA : Continuous A) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (u : WO V W) (c : ℂ)
    (hc : ∀ t : ℝ, ψ (symplO V W (L t) u) = Complex.exp (t * c))
    (hinv : ∀ g, IsThetaFunO ψ V W g → ∀ t, ∫ x, heisO ψ V W (L t) g (A x) ∂ν = ∫ x, g (A x) ∂ν) :
    c * ∫ x, heisO ψ V W u f (A x) ∂ν = -∫ x, heisO ψ V W u (dLine ψ V W L f) (A x) ∂ν := by
  have hu := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u
  have hu' := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ (theta_dLine hθ hψ hL hf) u
  have hI : ∀ {g : WO V W → ℂ}, IsThetaFunO ψ V W g → Integrable (fun x => g (A x)) ν := fun hg => by
    obtain ⟨C, hC⟩ := theta_bounded hψ hg
    exact Integrable.of_bound (hg.cont.comp hA).aestronglyMeasurable C (.of_forall fun x => hC _)
  have h := integral_dLine_eq_zero hθ hψ hL ν A hA hu (hinv _ hu)
  rw [dLine_heisO hθ hψ hL hf u c hc] at h
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [integral_add ((hI hu).const_mul c) (hI hu'), integral_const_mul] at h
  exact eq_neg_of_add_eq_zero_left h

theorem coef_level (hψ : IsStdChar D ψ (-1)) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (u v : WO V W)
    (hv : heisO ψ V W v f = f)
    (hinv : ∀ g, IsThetaFunO ψ V W g → ∫ x, heisO ψ V W v g (A x) ∂ν = ∫ x, g (A x) ∂ν) :
    ∫ x, heisO ψ V W u f (A x) ∂ν = ψ (symplO V W u v) * ∫ x, heisO ψ V W u f (A x) ∂ν := by
  have hu := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u
  conv_lhs => rw [← hv, heisO_comm]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [integral_const_mul, hinv _ hu]

theorem norm_coef_le (hψ : IsStdChar D ψ (-1)) {f : WO V W → ℂ} {C : ℝ} (hC : ∀ w, ‖f w‖ ≤ C) (u : WO V W) :
    ‖∫ x, heisO ψ V W u f (A x) ∂ν‖ ≤ C * ν.real Set.univ :=
  norm_integral_le_of_norm_le_const (.of_forall fun x => by
    rw [heisO, norm_mul, hψ.1.2.1, one_mul]; exact hC _)

end Heis

section Coords

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem symplO_eq_add (w v : WO S T) : symplO S T w v = symplOH S T w v + symplOH S T w v := by
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]; norm_num
  unfold symplOH
  rw [← add_mul, ← two_mul, mul_comm 2, h2, one_mul]

theorem psi_symplO (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) (w : WO S T) (x : RW T S) :
    ψ (symplO S T w (iotaW σ T S x)) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (omO S T (piW θ T S w) x : ℝ)) := by
  rw [symplO_eq_add, ψ.map_add_eq_mul, psi_symplOH h hψ, ← Complex.exp_add]
  congr 1
  ring

def realLine (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D) (z : RW T S) : ℝ →+ WO S T where
  toFun t := iotaW σ T S (t • z)
  map_zero' := by rw [zero_smul, map_zero]
  map_add' a b := by rw [add_smul, map_add]

theorem isRealDir_realLine (h : Chart θ σ) (z : RW T S) : Formalism.L2.Theta.IsRealDir T S (realLine σ S T z) :=
  ⟨(h.continuous_iota T S).comp (continuous_id.smul continuous_const), fun t => h.real_iota T S _⟩

theorem psi_realLine (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) (w : WO S T) (z : RW T S) (t : ℝ) :
    ψ (symplO S T (realLine σ S T z t) w) =
      Complex.exp (t * (2 * Real.pi * Complex.I * (omO S T (piW θ T S w) z : ℝ))) := by
  show ψ (symplO S T (iotaW σ T S (t • z)) w) = _
  rw [symplO_skew w, AddChar.map_neg_eq_inv, psi_symplO h hψ, ← Complex.exp_neg, map_smul]
  congr 1
  simp only [smul_eq_mul, Complex.ofReal_mul]
  ring

set_option synthInstance.maxHeartbeats 400000 in

theorem omO_rat (h : Chart θ σ) (x y : WO S T) (q : D.host.F)
    (hq : symplO S T x y = algebraMap D.host.F (AF D.host.F) q) :
    omO S T (piW θ T S x) (piW θ T S y) = (Algebra.trace ℚ D.host.F q : ℚ) := by
  have e : ∀ τ, formAt S T τ (piW θ T S x τ) (piW θ T S y τ) =
      (tauE D τ (algebraMap D.host.F D.host.E q)).re := fun τ => by
    rw [← valTau_symplO h.inf, hq]
    show (θ τ (infPart D (algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) q)))).re = _
    have e2 : algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) q) =
        incA D (algebraMap D.host.F D.host.E q) := by
      show (algebraMap D.host.F (AF D.host.F) q) ⊗ₜ[D.host.F] (1 : D.host.E) =
        (1 : AF D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E q)
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    rw [e2]
    exact congrArg Complex.re (comp_incA h.inf τ (algebraMap D.host.F D.host.E q))
  show ∑ τ, formAt S T τ (piW θ T S x τ) (piW θ T S y τ) = _
  simp only [e]
  rw [← Complex.re_sum, GlobalTheory.StdRat.sum_tauE_eq_trace]
  simp

theorem exists_coords (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (U : AddSubgroup (WO S T)) (hU : IsOpen (U : Set (WO S T))) :
    ∃ (n : ℕ) (b : Fin n → ℝ →+ WO S T) (ℓ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → Fin n → ℝ),
      (∀ i, Formalism.L2.Theta.IsRealDir T S (b i)) ∧
      (∀ y i (t : ℝ), ψ (symplO S T (b i t) (ratW T S y)) = Complex.exp (t * (2 * Real.pi * Complex.I * (ℓ y i : ℝ)))) ∧
      Function.Injective ℓ ∧
      ∀ y, (∀ v ∈ U, v.map (infPart D) = 0 → ψ (symplO S T v (ratW T S y)) = 1) → ∀ i, ∃ k : ℤ, ℓ y i = k := by
  classical
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  let rat : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ WO S T := (incA D).toAddMonoidHom.mapMatrix
  have hrat : ∀ y, rat y = ratW T S y := fun _ => rfl
  let z : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ RW T S := (piW θ T S).comp rat
  let fpart : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ WO S T := rat - (iotaW σ T S).comp z
  have hfin : ∀ y, (fpart y).map (infPart D) = 0 := fun y => by
    have hp : piW θ T S (fpart y) = 0 := by
      show piW θ T S (rat y - iotaW σ T S (piW θ T S (rat y))) = 0
      rw [AddMonoidHom.map_sub, h.pi_iota, sub_self]
    ext i j
    exact ThetaCont.infPart_eq_zero h _ fun τ => congrFun (congrFun (congrFun hp τ) i) j
  let e := Module.finBasis ℚ (Matrix (Fin T.rank) (Fin S.rank) D.host.E)
  choose N hN hNU using fun i => GlobalTheory.SplitScalar.exists_nsmul_mem U hU (hfin (e i))
  let lam := fun i => N i • e i
  have hchar : ∀ y i (t : ℝ), ψ (symplO S T (realLine σ S T (z (lam i)) t) (ratW T S y)) = _ :=
    fun y i t => psi_realLine h hψ (ratW T S y) (z (lam i)) t
  refine ⟨_, fun i => realLine σ S T (z (lam i)), fun y i => omO S T (piW θ T S (ratW T S y)) (z (lam i)),
    fun i => isRealDir_realLine h _, hchar, ?_, ?_⟩
  · intro y y' hyy
    by_contra hne
    have hd : y - y' ≠ 0 := sub_ne_zero.2 hne
    let Λ : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ ℝ :=
      { toFun := fun l => omO S T (z (y - y')) (z l)
        map_zero' := by rw [map_zero, map_zero]
        map_add' := fun a b => by rw [map_add, map_add] }
    have h1 : ∀ i, Λ (lam i) = 0 := fun i => by
      have := congrFun hyy i
      show omO S T (z (y - y')) (z (lam i)) = 0
      rw [map_sub, map_sub, LinearMap.sub_apply, sub_eq_zero]
      exact this
    have h2 : ∀ i, Λ (e i) = 0 := fun i => by
      have := h1 i
      simp only [lam, map_nsmul, nsmul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_left (Nat.cast_ne_zero.2 (hN i).ne')
    have h3 : Λ.toRatLinearMap = 0 := e.ext fun i => h2 i
    have h4 : ∀ l, Λ l = 0 := fun l => LinearMap.congr_fun h3 l
    obtain ⟨i, j, hij⟩ : ∃ i j, (y - y') i j ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hd (Matrix.ext hcon)
    obtain ⟨_, ⟨g, rfl⟩, hγ⟩ := GlobalTheory.RatAnnih.exists_symplO_eq S T (rat (y - y')) i j ((y - y') i j)⁻¹
    have h5 : symplO S T (rat (y - y')) (rat g) = algebraMap D.host.F (AF D.host.F) 2 := by
      haveI : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_pos (by rw [D.sp.cm.deg2]; norm_num)
      have e1 : incA D ((y - y') i j)⁻¹ * rat (y - y') i j = incA D 1 := by
        show incA D ((y - y') i j)⁻¹ * incA D ((y - y') i j) = _
        rw [← map_mul, inv_mul_cancel₀ hij]
      have e2 : Algebra.trace D.host.F D.host.E 1 = 2 := by
        rw [← map_one (algebraMap D.host.F D.host.E), Algebra.trace_algebraMap, D.sp.cm.deg2]
        norm_num
      refine hγ.trans ?_
      rw [e1, ← e2]
      exact GlobalTheory.SymplecticOrthogonalSesquilinear.trace_one_tmul _ 1
    have h6 := omO_rat h _ _ _ h5
    have h7 : omO S T (z (y - y')) (z g) = 0 := h4 g
    have h8 : (Algebra.trace ℚ D.host.F (2 : D.host.F) : ℚ) = 0 := by
      have h9 : ((Algebra.trace ℚ D.host.F (2 : D.host.F) : ℚ) : ℝ) = 0 := h6.symm.trans h7
      exact_mod_cast h9
    have h10 : (2 : D.host.F) = algebraMap ℚ D.host.F 2 := by simp
    rw [h10, Algebra.trace_algebraMap, nsmul_eq_mul] at h8
    have h11 : (0 : ℕ) < Module.finrank ℚ D.host.F := Module.finrank_pos
    have h12 : ((Module.finrank ℚ D.host.F : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 h11.ne'
    exact h12 (by simpa using h8)
  · intro y hy i
    have hv : fpart (lam i) ∈ U := by
      simp only [lam, map_nsmul]
      exact hNU i
    have h1 := hy _ hv (hfin _)
    obtain ⟨a, ha⟩ := GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_rat D S T (lam i) y
    have h2 : ψ (symplO S T (ratW T S (lam i)) (ratW T S y)) = 1 := (congrArg ψ ha).trans (hψ.1.2.2.1 a)
    have h3 : ratW T S (lam i) = realLine σ S T (z (lam i)) 1 + fpart (lam i) := by
      show rat (lam i) = iotaW σ T S ((1 : ℝ) • z (lam i)) + (rat (lam i) - iotaW σ T S (z (lam i)))
      rw [one_smul]
      abel
    rw [h3, (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S T).1, ψ.map_add_eq_mul, h1, mul_one, hchar] at h2
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h2
    refine ⟨k, ?_⟩
    have h2pi : (2 * Real.pi * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
    have : ((omO S T (piW θ T S (ratW T S y)) (z (lam i)) : ℝ) : ℂ) = (k : ℂ) := by
      apply mul_left_cancel₀ h2pi
      push_cast at hk ⊢
      linear_combination hk
    exact_mod_cast this

end Coords

section Iso

variable {D : D7}

theorem cT_mul_rect {A : Type} [CommRing A] (s : A →+* A) {a b c : Type} [Fintype b] (M : Matrix a b A) (N : Matrix b c A) :
    Formalism.UG.cT s (M * N) = Formalism.UG.cT s N * Formalism.UG.cT s M := by
  unfold Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem trace_rearr {A : Type} [CommRing A] {v w r : ℕ} (X : Matrix (Fin v) (Fin v) A) (Y Z : Matrix (Fin v) (Fin r) A)
    (c : Matrix (Fin r) (Fin w) A) (g : Matrix (Fin w) (Fin w) A) (a : Matrix (Fin w) (Fin r) A)
    (P : Matrix (Fin r) (Fin v) A) (h : X * Y = Z) :
    Matrix.trace (X * (Y * c) * g * (a * P)) = Matrix.trace (c * g * a * (P * Z)) := by
  rw [← Matrix.mul_assoc X, h, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem cT_map_incA {a b : ℕ} (M : Matrix (Fin a) (Fin b) D.host.E) :
    Formalism.UG.cT (cA D) (M.map (incA D)) = (adj D M).map (incA D) := by
  ext i j
  exact GlobalTheory.DualPairCheck.cA_incA _

theorem adj_mul_gram (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    adj D (adj D C * V.gram) = V.gram * C := by
  have h1 : adj D V.gram = V.gram := Matrix.ext fun i j => GlobalTheory.DualPairCheck.gram_star V j i
  have h2 : adj D (adj D C) = C := Matrix.ext fun i j => star_star _
  unfold adj at h1 h2 ⊢
  rw [cT_mul_rect, h1, h2]

theorem hO_isoPart (V W : HSp D) {r : ℕ} (C₁ C₂ : Matrix (Fin V.rank) (Fin r) D.host.E) (a b : Mx D W.rank r) :
    hO V W (isoPart V W C₁ a) (isoPart V W C₂ b) =
      Matrix.trace (Formalism.UG.cT (cA D) b * W.gram.map (incA D) * a * (adj D C₁ * V.gram * C₂).map (incA D)) := by
  rw [GlobalTheory.SplitHecke.hO_trace]
  show Matrix.trace ((V.gram⁻¹).map (incA D) * Formalism.UG.cT (cA D) (b * (adj D C₂ * V.gram).map (incA D)) *
    W.gram.map (incA D) * (a * (adj D C₁ * V.gram).map (incA D))) = _
  rw [cT_mul_rect, cT_map_incA, adj_mul_gram]
  rw [Matrix.map_mul (L := adj D C₁ * V.gram) (M := C₂)]
  refine trace_rearr _ _ (C₂.map (incA D)) _ _ _ _ ?_
  rw [← Matrix.map_mul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (GlobalTheory.LatVac.gram_det_isUnit V), Matrix.one_mul]

theorem symplO_isoPart_pair (V W S : HSp D) (hS : S.gram = 1) (C₁ C₂ : Matrix (Fin V.rank) (Fin S.rank) D.host.E)
    (h : adj D C₁ * V.gram * C₂ = 1) (a b : Mx D W.rank S.rank) :
    symplO V W (isoPart V W C₁ a) (isoPart V W C₂ b) = symplO S W a b := by
  unfold symplO
  rw [hO_isoPart, GlobalTheory.SplitHecke.hO_trace, h, hS, inv_one]
  have e : ((1 : Matrix (Fin S.rank) (Fin S.rank) D.host.E)).map (incA D) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  rw [e, Matrix.mul_one, Matrix.one_mul]

theorem symplO_isoPart_zero (V W : HSp D) {r : ℕ} (C₁ C₂ : Matrix (Fin V.rank) (Fin r) D.host.E)
    (h : adj D C₁ * V.gram * C₂ = 0) (a b : Mx D W.rank r) :
    symplO V W (isoPart V W C₁ a) (isoPart V W C₂ b) = 0 := by
  unfold symplO
  rw [hO_isoPart, h]
  have e : ((0 : Matrix (Fin r) (Fin r) D.host.E)).map (incA D) = 0 := Matrix.map_zero _ (map_zero _)
  rw [e, Matrix.mul_zero, Matrix.trace_zero, mul_zero, map_zero]

end Iso

section Main

variable {D : D7}

theorem symplOH_sub (V W : HSp D) (a b : WO V W) : symplOH V W a b - symplOH V W b a = symplO V W a b := by
  have e := symplO_eq_add a b
  have e2 : symplOH V W b a = -symplOH V W a b := by
    unfold symplOH
    rw [symplO_skew a b, mul_neg]
  rw [e2, sub_neg_eq_add, ← e]

theorem continuous_symplO_left (S T : HSp D) (w : WO S T) : Continuous fun a : WO S T => symplO S T a w := by
  have h : Continuous fun a : WO S T => symplOH S T a w := continuous_symplOH continuous_id continuous_const
  exact (h.add h).congr fun a => (symplO_eq_add a w).symm

theorem isoPart_map_eq_zero {B : Type} [CommRing B] (φ : AE D →+* B) (V W : HSp D) {r : ℕ}
    (C : Matrix (Fin V.rank) (Fin r) D.host.E) {a : Mx D W.rank r} (h : a.map φ = 0) :
    (isoPart V W C a).map φ = 0 := by
  show (a * (adj D C * V.gram).map (incA D)).map φ = 0
  rw [Matrix.map_mul, h, Matrix.zero_mul]

theorem core (D : D7) (V V' W S : HSp D) (hS : S.gram = 1) (C C' : Matrix (Fin V.rank) (Fin S.rank) D.host.E)
    (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (hs : IsIsoSplit V V' C B) (h1 : adj D C * V.gram * C' = 1)
    (h0 : adj D C * V.gram * C = 0)
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (μ : Measure (Mx D W.rank S.rank))
    (𝓨 : Set (Mx D W.rank S.rank)) (hcov : IsCovolOne (ratMx D W.rank S.rank) μ 𝓨) (f : WO V W → ℂ)
    (hf : IsThetaFunO ψ V W f) :
    Summable (fun y : Matrix (Fin W.rank) (Fin S.rank) D.host.E =>
      ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) f) 0‖) ∧
    HasSum (fun y : Matrix (Fin W.rank) (Fin S.rank) D.host.E =>
      res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) f) 0) (f 0) := by
  classical
  obtain ⟨θ, hθ⟩ := hψ.2.1
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W S
  have i6 : BorelSpace (Mx D W.rank S.rank) := ⟨rfl⟩
  have hcov' := hcov
  obtain ⟨hμ, h𝓨, hvol⟩ := hcov
  have hfin : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.one_lt_top⟩
  let Ah : Mx D W.rank S.rank →+ WO V W :=
    { toFun := isoPart V W C, map_zero' := Matrix.zero_mul _, map_add' := fun a b => Matrix.add_mul a b _ }
  have hAc : Continuous (isoPart V W C) := Continuous.matrix_mul continuous_id continuous_const
  have hmid : midPart V V' W B 0 = 0 := Matrix.zero_mul _
  have hres : ∀ g, res V V' W C B μ 𝓨 g 0 = ∫ a, g (isoPart V W C a) ∂(μ.restrict 𝓨) := fun g => by
    simp only [res, hmid, add_zero]
  obtain ⟨hH, -⟩ := GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W S.rank C B hs ψ hψ μ 𝓨 hcov'
  have hinv : ∀ g, IsThetaFunO ψ V W g → ∀ a, ∫ x, heisO ψ V W (isoPart V W C a) g (isoPart V W C x) ∂(μ.restrict 𝓨) =
      ∫ x, g (isoPart V W C x) ∂(μ.restrict 𝓨) := fun g hg a => by
    have := congrFun ((hH g hg).2.2.2 a) 0
    rwa [hres, hres] at this
  obtain ⟨U, hU, hlev⟩ := hf.level
  have hU' : IsOpen ((U.comap Ah : AddSubgroup (WO S W)) : Set (WO S W)) := hU.preimage hAc
  obtain ⟨n, b, ℓ, hb, hchar, hinj, hint⟩ := exists_coords ψ hψ S W (U.comap Ah) hU'
  let u : Matrix (Fin W.rank) (Fin S.rank) D.host.E → WO V W := fun y => isoPart V W C' (Matrix.map y (incA D))
  let T : Matrix (Fin W.rank) (Fin S.rank) D.host.E → (WO V W → ℂ) → ℂ :=
    fun y g => ∫ x, heisO ψ V W (u y) g (isoPart V W C x) ∂(μ.restrict 𝓨)
  have hpair : ∀ (a : Mx D W.rank S.rank) y, symplO V W (isoPart V W C a) (u y) = symplO S W a (ratW W S y) :=
    fun a y => symplO_isoPart_pair V W S hS C C' h1 a _
  let L : Fin n → ℝ →+ WO V W := fun i => Ah.comp (b i)
  have hL : ∀ i, Formalism.L2.Theta.IsRealDir W V (L i) := fun i =>
    ⟨hAc.comp (hb i).1, fun t => isoPart_map_eq_zero (finPart D) V W C ((hb i).2 t)⟩
  have hc : ∀ y i (t : ℝ), ψ (symplO V W (L i t) (u y)) =
      Complex.exp (t * (2 * Real.pi * Complex.I * (ℓ y i : ℝ))) := fun y i t => by
    refine Eq.trans ?_ (hchar y i t)
    exact congrArg ψ (hpair _ y)
  have hrel : ∀ i g y, IsThetaFunO ψ V W g → |ℓ y i| * ‖T y g‖ ≤ ‖T y (dLine ψ V W (L i) g)‖ := fun i g y hg => by
    have h := coef_rel (μ.restrict 𝓨) (isoPart V W C) hθ hψ (hL i) hAc hg (u y) _ (hc y i)
      (fun g' hg' t => hinv g' hg' (b i t))
    have h2 := congrArg norm h
    rw [norm_mul, norm_neg] at h2
    have h3 : ‖2 * Real.pi * Complex.I * (ℓ y i : ℂ)‖ = 2 * Real.pi * |ℓ y i| := by
      simp [abs_of_pos Real.pi_pos]
    rw [h3] at h2
    have hpi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
    have hn : 0 ≤ |ℓ y i| * ‖T y g‖ := by positivity
    calc |ℓ y i| * ‖T y g‖ ≤ 2 * Real.pi * (|ℓ y i| * ‖T y g‖) := le_mul_of_one_le_left hn hpi
      _ = ‖T y (dLine ψ V W (L i) g)‖ := by rw [← mul_assoc]; exact h2
  have hbd : ∀ g, IsThetaFunO ψ V W g → ∃ c, ∀ y, ‖T y g‖ ≤ c := fun g hg => by
    obtain ⟨c, hc'⟩ := theta_bounded hψ hg
    exact ⟨c * (μ.restrict 𝓨).real Set.univ, fun y => norm_coef_le (μ.restrict 𝓨) _ hψ hc' _⟩
  obtain ⟨Cb, hCb⟩ := prod_bound (IsThetaFunO ψ V W) (fun i => dLine ψ V W (L i))
    (fun i g hg => theta_dLine hθ hψ (hL i) hg) T hbd ℓ hrel Finset.univ f hf
  have hsupp : ∀ y, T y f ≠ 0 → ∀ i, ∃ k : ℤ, ℓ y i = k := fun y hy => hint y fun v hv hv0 => by
    have hfix : heisO ψ V W (isoPart V W C v) f = f := hlev _ hv (isoPart_map_eq_zero (infPart D) V W C hv0)
    have h := coef_level (μ.restrict 𝓨) (isoPart V W C) hψ hf (u y) (isoPart V W C v) hfix (fun g hg => hinv g hg v)
    have h' : ψ (symplO V W (u y) (isoPart V W C v)) = 1 :=
      mul_right_cancel₀ hy (by rw [one_mul]; exact h.symm)
    rw [symplO_skew (isoPart V W C v) (u y), hpair, AddChar.map_neg_eq_inv, inv_eq_one] at h'
    exact h'
  have hsum : Summable fun y => ‖T y f‖ := summable_norm_of_lattice _ ℓ hinj hsupp Cb hCb
  let χ : Matrix (Fin W.rank) (Fin S.rank) D.host.E → Mx D W.rank S.rank → ℂ :=
    fun y a => ψ (symplO S W a (ratW W S y))
  have hterm : ∀ y, T y f = ∫ a in 𝓨, χ y a * f (isoPart V W C a) ∂μ := fun y => by
    refine integral_congr_ae (.of_forall fun a => ?_)
    have hu : u y = ratW W V (y * (adj D C' * V.gram)) := (Matrix.map_mul (L := y) (M := adj D C' * V.gram)).symm
    show ψ (symplOH V W (isoPart V W C a) (u y)) * f (isoPart V W C a + u y) = _
    rw [add_comm, hu, hf.quasi, ← hu, ← mul_assoc, ← ψ.map_add_eq_mul, ← sub_eq_add_neg, symplOH_sub, hpair]
  have hχ0 : ∀ y, (∀ x, χ y x = 1) → ∀ i, ℓ y i = 0 := fun y hy i => by
    by_contra hne
    have h := hchar y i (1 / (2 * ℓ y i))
    have h' : χ y (b i (1 / (2 * ℓ y i))) = 1 := hy _
    have e : (((1 / (2 * ℓ y i) : ℝ) : ℂ)) * (2 * Real.pi * Complex.I * (ℓ y i : ℝ)) = Real.pi * Complex.I := by
      have : (ℓ y i : ℂ) ≠ 0 := by exact_mod_cast hne
      push_cast
      field_simp
    rw [e, Complex.exp_pi_mul_I] at h
    have h2 : (1 : ℂ) = -1 := h'.symm.trans h
    norm_num at h2
  have hzero : ∀ x : Mx D W.rank S.rank, χ 0 x = 1 := fun x => by
    have e : ratW W S (0 : Matrix (Fin W.rank) (Fin S.rank) D.host.E) = 0 := Matrix.map_zero _ (map_zero _)
    have e2 : symplO S W x 0 = 0 := by
      have := (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S W).2.1 x 0 0
      rwa [add_zero, left_eq_add] at this
    show ψ (symplO S W x (ratW W S 0)) = 1
    rw [e, e2, ψ.map_zero_eq_one]
  have : Countable (Matrix (Fin W.rank) (Fin S.rank) D.host.E) :=
    (Module.finBasis ℚ (Matrix (Fin W.rank) (Fin S.rank) D.host.E)).equivFun.injective.countable
  have hF := hasSum_coefficients (Mx D W.rank S.rank) (ratL W S) K hK hKc
    (Matrix (Fin W.rank) (Fin S.rank) D.host.E) χ
    (fun y => hψ.1.1.comp (continuous_symplO_left S W _))
    (fun y x x' => by
      show ψ (symplO S W (x + x') _) = _
      rw [(GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S W).1, ψ.map_add_eq_mul])
    (fun y y' x => by
      have e : ratW W S (y + y') = ratW W S y + ratW W S y' := Matrix.map_add _ (map_add _) _ _
      show ψ (symplO S W x (ratW W S (y + y'))) = _
      rw [e, (GlobalTheory.SymplecticOrthogonalSesquilinear.symplO_alt D S W).2.1, ψ.map_add_eq_mul])
    hzero (fun y x => hψ.1.2.1 _)
    (fun x => by
      refine Iff.trans ?_ (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S W x)
      exact ⟨fun h _ ⟨y, hy⟩ => hy ▸ h y, fun h y => h _ ⟨y, rfl⟩⟩)
    (fun y hy => hinj (funext fun i => by rw [hχ0 y hy i, hχ0 0 hzero i]))
    μ 𝓨 hμ h𝓨 hvol (fun a => f (isoPart V W C a)) (hf.cont.comp hAc)
    (fun γ hγ x => by
      obtain ⟨g, rfl⟩ := hγ
      have hu : isoPart V W C (ratW W S g) = ratW W V (g * (adj D C * V.gram)) :=
        (Matrix.map_mul (L := g) (M := adj D C * V.gram)).symm
      have e : isoPart V W C (ratW W S g + x) = isoPart V W C (ratW W S g) + isoPart V W C x := Ah.map_add _ _
      have e2 : symplOH V W (isoPart V W C (ratW W S g)) (isoPart V W C x) = 0 := by
        unfold symplOH
        rw [symplO_isoPart_zero V W C C h0, mul_zero]
      show f (isoPart V W C (ratW W S g + x)) = _
      rw [e, hu, hf.quasi, ← hu, e2, neg_zero, ψ.map_zero_eq_one, one_mul])
    (by simpa only [hterm] using hsum)
  have hA0 : isoPart V W C 0 = 0 := Ah.map_zero
  simp only [hA0] at hF
  have hr : ∀ y, res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) f) 0 = T y f := fun y => hres _
  simp only [hr]
  exact ⟨hsum, by simpa only [hterm] using hF⟩

theorem value_zero_eq_sum_restrictions : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ f, IsThetaFunO ψ V W f → Summable (fun y : Matrix (Fin W.rank) (Fin r) D.host.E => ‖res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) f) 0‖) ∧ HasSum (fun y : Matrix (Fin W.rank) (Fin r) D.host.E => res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) f) 0) (f 0) := by
  intro D V V' W r C C' B hs h1 _ _ ψ hψ μ 𝓨 hcov f hf
  have hg : (GlobalTheory.Size.posSp D r).gram = 1 := by
    funext i j
    refine (Examples₂.stdSpace_gram_apply (E := D.host.E) Examples₂.star_isIntegral r (fun _ => false) r 0 i j).trans ?_
    change (if i = j then (Examples₂.sgn false : D.host.E) else 0) = if i = j then 1 else 0
    by_cases h : i = j <;> simp [h, Examples₂.sgn]
  exact core D V V' W (GlobalTheory.Size.posSp D r) hg C C' B hs h1 hs.frame.2.2 ψ hψ μ 𝓨 hcov f hf

end Main

end GlobalTheory.TwFour

end
