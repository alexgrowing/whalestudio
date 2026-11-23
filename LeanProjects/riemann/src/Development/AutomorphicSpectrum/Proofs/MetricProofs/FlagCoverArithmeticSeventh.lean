import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AevalNeZeroOfNotMem
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Values
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.BaseEtale

section Root

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

theorem exists_analytic_zero (f : W × ℂ → ℂ) (p : W × ℂ) (hf : AnalyticAt ℂ f p) (hp : f p = 0)
    (hd : fderiv ℂ f p ((0 : W), (1 : ℂ)) ≠ 0) :
    ∃ (U : Set W) (ε : ℝ) (r : W → ℂ), IsOpen U ∧ p.1 ∈ U ∧ 0 < ε ∧ AnalyticOnNhd ℂ r U ∧
      ∀ w ∈ U, ∀ θ : ℂ, ‖θ - p.2‖ < ε → f (w, θ) = 0 → θ = r w := by
  set A := fderiv ℂ f p with hA
  let Lm : W × ℂ →L[ℂ] W × ℂ := (ContinuousLinearMap.fst ℂ W ℂ).prod A
  have hinj : Function.Injective Lm := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨h, τ⟩ hv
    have h1 : h = 0 := congrArg Prod.fst hv
    have h2 : A (h, τ) = 0 := congrArg Prod.snd hv
    subst h1
    have h3 : ((0 : W), τ) = τ • ((0 : W), (1 : ℂ)) := by simp
    rw [h3, map_smul, smul_eq_mul] at h2
    have h4 : τ = 0 := (mul_eq_zero.1 h2).resolve_right hd
    simp [h4]
  have hsurj : Function.Surjective Lm := by
    rintro ⟨u, c⟩
    refine ⟨(u, (c - A (u, 0)) / A ((0 : W), (1 : ℂ))), ?_⟩
    have h3 : (u, (c - A (u, 0)) / A ((0 : W), (1 : ℂ))) =
        (u, (0 : ℂ)) + ((c - A (u, 0)) / A ((0 : W), (1 : ℂ))) • ((0 : W), (1 : ℂ)) := by simp
    refine Prod.ext rfl ?_
    show A _ = c
    rw [h3, map_add, map_smul, smul_eq_mul, div_mul_cancel₀ _ hd]
    ring
  let Le := ContinuousLinearEquiv.ofBijective Lm (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj)
  have hLe : (Le : W × ℂ →L[ℂ] W × ℂ) = Lm := ContinuousLinearEquiv.coe_ofBijective _ _ _
  let φ : W × ℂ → W × ℂ := fun x => (x.1, f x)
  have hφ : HasStrictFDerivAt φ (Le : W × ℂ →L[ℂ] W × ℂ) p := by
    rw [hLe]
    exact (ContinuousLinearMap.fst ℂ W ℂ).hasStrictFDerivAt.prodMk hf.hasStrictFDerivAt
  let Φ := hφ.toOpenPartialHomeomorph φ
  have hΦ : ∀ x, Φ x = (x.1, f x) := fun x => rfl
  have hpS : p ∈ Φ.source := hφ.mem_toOpenPartialHomeomorph_source
  have hφan : AnalyticAt ℂ Φ p := ((ContinuousLinearMap.fst ℂ W ℂ).analyticAt p).prod hf
  have hsymm : AnalyticAt ℂ Φ.symm (Φ p) :=
    Φ.analyticAt_symm' (i := Le) hpS hφan hφ.hasFDerivAt.fderiv
  obtain ⟨s, hs, hsan⟩ := hsymm.exists_mem_nhds_analyticOnNhd
  obtain ⟨T0, hT0s, hT0o, hT0p⟩ := mem_nhds_iff.mp hs
  have hS : IsOpen (Φ.source ∩ Φ ⁻¹' T0) := Φ.continuousOn.isOpen_inter_preimage Φ.open_source hT0o
  obtain ⟨U1, V1, hU1, hV1, hpU, hpV, hUV⟩ := isOpen_prod_iff.1 hS p.1 p.2 ⟨hpS, hT0p⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hV1 _ hpV
  have hΦp : Φ p = (p.1, 0) := by rw [hΦ, hp]
  refine ⟨U1 ∩ {w | (w, (0 : ℂ)) ∈ Φ.target ∩ T0}, ε, fun w => (Φ.symm (w, 0)).2, ?_, ?_, hε, ?_, ?_⟩
  · exact hU1.inter ((Φ.open_target.inter hT0o).preimage (continuous_id.prodMk continuous_const))
  · refine ⟨hpU, ?_⟩
    show (p.1, (0 : ℂ)) ∈ Φ.target ∩ T0
    rw [← hΦp]
    exact ⟨Φ.map_source hpS, hT0p⟩
  · intro w hw
    have h1 : AnalyticAt ℂ (fun w : W => (w, (0 : ℂ))) w := analyticAt_id.prod analyticAt_const
    have h2 : AnalyticAt ℂ (fun w : W => Φ.symm (w, 0)) w :=
      AnalyticAt.comp (f := fun w : W => (w, (0 : ℂ))) (hsan _ (hT0s hw.2.2)) h1
    exact analyticAt_snd.comp h2
  · intro w hw θ hθ h0
    have hmem : (w, θ) ∈ Φ.source ∩ Φ ⁻¹' T0 :=
      hUV ⟨hw.1, hball (by simpa [Metric.mem_ball, dist_eq_norm] using hθ)⟩
    have e : Φ (w, θ) = (w, 0) := by rw [hΦ, h0]
    have := Φ.left_inv hmem.1
    rw [e] at this
    show θ = (Φ.symm (w, 0)).2
    rw [this]

theorem exists_analytic_root (a : ℕ → W → ℂ) (n : ℕ) (w₀ : W) (θ₀ : ℂ)
    (ha : ∀ e < n, AnalyticAt ℂ (a e) w₀)
    (h0 : (∑ e ∈ Finset.range n, Polynomial.C (a e w₀) * Polynomial.X ^ e).eval θ₀ = 0)
    (h1 : (Polynomial.derivative (∑ e ∈ Finset.range n, Polynomial.C (a e w₀) * Polynomial.X ^ e)).eval θ₀ ≠ 0) :
    ∃ (U : Set W) (ε : ℝ) (r : W → ℂ), IsOpen U ∧ w₀ ∈ U ∧ 0 < ε ∧ AnalyticOnNhd ℂ r U ∧
      ∀ w ∈ U, ∀ θ : ℂ, ‖θ - θ₀‖ < ε →
        (∑ e ∈ Finset.range n, Polynomial.C (a e w) * Polynomial.X ^ e).eval θ = 0 → θ = r w := by
  let f : W × ℂ → ℂ := fun x => (∑ e ∈ Finset.range n, Polynomial.C (a e x.1) * Polynomial.X ^ e).eval x.2
  have hfe : f = fun x => ∑ e ∈ Finset.range n, a e x.1 * x.2 ^ e := by
    funext x
    simp [f, Polynomial.eval_finset_sum]
  have hf : AnalyticAt ℂ f (w₀, θ₀) := by
    rw [hfe]
    refine Finset.analyticAt_fun_sum _ fun e he => ?_
    have h2 : AnalyticAt ℂ (fun x : W × ℂ => a e x.1) (w₀, θ₀) :=
      AnalyticAt.comp (f := fun x : W × ℂ => x.1) (ha e (Finset.mem_range.1 he)) analyticAt_fst
    exact h2.mul (analyticAt_snd.pow e)
  have hline : HasDerivAt (fun θ => f (w₀, θ)) (fderiv ℂ f (w₀, θ₀) ((0 : W), (1 : ℂ))) θ₀ :=
    hf.differentiableAt.hasFDerivAt.comp_hasDerivAt θ₀
      ((hasDerivAt_const θ₀ w₀).prodMk (hasDerivAt_id θ₀))
  have hpoly := (∑ e ∈ Finset.range n, Polynomial.C (a e w₀) * Polynomial.X ^ e).hasDerivAt θ₀
  have hd : fderiv ℂ f (w₀, θ₀) ((0 : W), (1 : ℂ)) ≠ 0 := by
    rw [hline.unique hpoly]
    exact h1
  exact exists_analytic_zero f (w₀, θ₀) hf h0 hd

end Root

section Fields

theorem exists_sep_poly {Ω : Type} [Field Ω] [CharZero Ω] {L L' : IntermediateField ℚ Ω} (hle : L ≤ L')
    (hpos : 0 < L.relfinrank L') {t : Ω} (ht : t ∈ L') :
    ∃ μ A B : Polynomial Ω, (∀ e, μ.coeff e ∈ L) ∧ (∀ e, A.coeff e ∈ L) ∧ (∀ e, B.coeff e ∈ L) ∧
      A * μ + B * Polynomial.derivative μ = 1 ∧ μ.eval t = 0 := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle] at hpos
  have hfin : FiniteDimensional L (IntermediateField.extendScalars hle) := Module.finite_of_finrank_pos hpos
  let t' : IntermediateField.extendScalars hle := ⟨t, ht⟩
  have hi : IsIntegral L t' := IsIntegral.of_finite L t'
  have hsep : (minpoly L t').Separable := (minpoly.irreducible hi).separable
  obtain ⟨a, b, hab⟩ := hsep
  refine ⟨(minpoly L t').map (algebraMap L Ω), a.map (algebraMap L Ω), b.map (algebraMap L Ω),
    fun e => ?_, fun e => ?_, fun e => ?_, ?_, ?_⟩
  · rw [Polynomial.coeff_map]; exact SetLike.coe_mem _
  · rw [Polynomial.coeff_map]; exact SetLike.coe_mem _
  · rw [Polynomial.coeff_map]; exact SetLike.coe_mem _
  · have := congrArg (Polynomial.map (algebraMap L Ω)) hab
    simpa [Polynomial.map_add, Polynomial.map_mul, Polynomial.derivative_map] using this
  · have h := congrArg (algebraMap (IntermediateField.extendScalars hle) Ω) (minpoly.aeval L t')
    rw [map_zero, ← Polynomial.aeval_algebraMap_apply] at h
    rw [Polynomial.eval_map_algebraMap]
    exact h

end Fields

section Forms

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem isMultiHomog_finset_prod {α : Type} (s : Finset α) (f : α → MRing ι) (a : α → K → ℕ)
    (h : ∀ i ∈ s, IsMultiHomog (f i) (a i)) : IsMultiHomog (∏ i ∈ s, f i) (∑ i ∈ s, a i) := by
  induction s using Finset.induction_on with
  | empty => simpa using (isMultiHomog_one : IsMultiHomog (1 : MRing ι) 0)
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    exact isMultiHomog_mul (h b (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isMultiHomog_rename_block {κ : K → K'} {v : (Σ k, ι k) → (Σ k, ι' k)} (hv : IsBlockMap κ v) {f : MRing ι}
    {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (rename v f : MRing ι') (Function.extend κ a 0) := by
  intro m hm k'
  rw [support_rename_of_injective hv.2.1] at hm
  obtain ⟨m0, hm0, rfl⟩ := Finset.mem_image.mp hm
  by_cases hk : k' ∈ Set.range κ
  · obtain ⟨k, rfl⟩ := hk
    rw [hv.1.extend_apply, ← hf m0 hm0 k]
    have hex : ∀ i' : ι' (κ k), ∃ i : ι k, v ⟨k, i⟩ = ⟨κ k, i'⟩ := by
      intro i'
      obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
      have h1 : κ p.1 = κ k := by rw [← hv.2.2.1 p, hp]
      obtain ⟨k₁, i⟩ := p
      obtain rfl : k₁ = k := hv.1 h1
      exact ⟨i, hp⟩
    choose g hg using hex
    have hb : Function.Bijective g := by
      constructor
      · intro a b hab
        have : (⟨κ k, a⟩ : Σ k, ι' k) = ⟨κ k, b⟩ := by rw [← hg a, ← hg b, hab]
        exact eq_of_heq (Sigma.mk.inj this).2
      · intro i
        have hq : ∃ i', v ⟨k, i⟩ = ⟨κ k, i'⟩ := by
          have h1 := hv.2.2.1 ⟨k, i⟩
          generalize v ⟨k, i⟩ = q at h1
          obtain ⟨q1, q2⟩ := q
          simp only at h1
          subst h1
          exact ⟨q2, rfl⟩
        obtain ⟨i', hi'⟩ := hq
        refine ⟨i', ?_⟩
        have h2 : v ⟨k, g i'⟩ = v ⟨k, i⟩ := by rw [hg i', hi']
        exact eq_of_heq (Sigma.mk.inj (hv.2.1 h2)).2
    calc ∑ i', (Finsupp.mapDomain v m0) ⟨κ k, i'⟩ = ∑ i', m0 ⟨k, g i'⟩ := by
          refine Finset.sum_congr rfl fun i' _ => ?_
          rw [← hg i', Finsupp.mapDomain_apply hv.2.1]
      _ = ∑ i, m0 ⟨k, i⟩ := hb.sum_comp fun i => m0 ⟨k, i⟩
  · rw [Function.extend_apply' _ _ _ (by simpa using hk)]
    refine Finset.sum_eq_zero fun i' _ => ?_
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨p, hp⟩
    exact hk ⟨p.1, by rw [← hv.2.2.1 p, hp]⟩

abbrev ev (f : MRing ι) (w : (Σ k, ι k) → ℂ) : ℂ := eval w (map (Int.castRingHom ℂ) f)

theorem ev_rename (z : (Σ k, ι' k) → ℂ) (v : (Σ k, ι k) → (Σ k, ι' k)) (s : MRing ι) :
    ev (rename v s : MRing ι') z = ev s (z ∘ v) := by
  rw [ev, map_rename, eval_rename]

theorem ev_ne_zero_of_orbit {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) {w w' : (Σ k, ι k) → ℂ}
    (ho : SameOrbit w w') (h : ev f w ≠ 0) : ev f w' ≠ 0 := by
  obtain ⟨c, -, rfl⟩ := ho
  intro h0
  apply h
  rw [ev, eval_smul_homog f a hf, show eval w' (map (Int.castRingHom ℂ) f) = 0 from h0, mul_zero]

def fr (g h : MRing ι) (w : (Σ k, ι k) → ℂ) : ℂ := ev g w / ev h w

theorem fr_orbit {g h : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) (hh : IsMultiHomog h d)
    {w w' : (Σ k, ι k) → ℂ} (ho : SameOrbit w w') : fr g h w = fr g h w' := by
  obtain ⟨c, hc, rfl⟩ := ho
  have hu : (∏ k, c k ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  rw [fr, fr, ev, ev, eval_smul_homog g d hg, eval_smul_homog h d hh, mul_div_mul_left _ _ hu]

theorem exists_rep {Ω : Type} [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) {c : Ω} (hc : c ∈ blockFnField y) :
    ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧ aeval y h ≠ 0 ∧
      aeval y g = c * aeval y h := by
  have zero_rep : ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧ aeval y h ≠ 0 ∧
      aeval y g = (0 : Ω) * aeval y h :=
    ⟨0, 0, 1, isMultiHomog_zero 0, isMultiHomog_one, by simp, by simp⟩
  unfold blockFnField at hc
  induction hc using IntermediateField.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, q, hpq, rfl⟩ := hx
    by_cases hq : y q = 0
    · rw [hq, div_zero]; exact zero_rep
    · refine ⟨_, X p, X q, isMultiHomog_X_single p, ?_, by simpa using hq, ?_⟩
      · rw [hpq]; exact isMultiHomog_X_single q
      · simp [div_mul_cancel₀ _ hq]
  | algebraMap r =>
    refine ⟨0, C r.num, C (r.den : ℤ), isMultiHomog_C_zero _, isMultiHomog_C_zero _, ?_, ?_⟩
    · simpa using r.den_nz
    · simp only [aeval_C]
      have h0 : (r.den : Ω) ≠ 0 := by exact_mod_cast r.den_nz
      have h1 : algebraMap ℚ Ω r = (r.num : Ω) / (r.den : Ω) := by
        conv_lhs => rw [← Rat.num_div_den r]
        simp
      rw [h1]
      simp [div_mul_cancel₀ _ h0]
  | add a b _ _ ha hb =>
    obtain ⟨d, g, h, hg, hh, hy, he⟩ := ha
    obtain ⟨d', g', h', hg', hh', hy', he'⟩ := hb
    refine ⟨d + d', g * h' + g' * h, h * h', isMultiHomog_add (isMultiHomog_mul hg hh') ?_,
      isMultiHomog_mul hh hh', ?_, ?_⟩
    · rw [add_comm d d']; exact isMultiHomog_mul hg' hh
    · rw [map_mul]; exact mul_ne_zero hy hy'
    · simp only [map_add, map_mul, he, he']; ring
  | inv a _ ha =>
    by_cases h0 : a = 0
    · rw [h0, _root_.inv_zero]; exact zero_rep
    obtain ⟨d, g, h, hg, hh, hy, he⟩ := ha
    refine ⟨d, h, g, hh, hg, by rw [he]; exact mul_ne_zero h0 hy, ?_⟩
    rw [he]
    field_simp
  | mul a b _ _ ha hb =>
    obtain ⟨d, g, h, hg, hh, hy, he⟩ := ha
    obtain ⟨d', g', h', hg', hh', hy', he'⟩ := hb
    refine ⟨d + d', g * g', h * h', isMultiHomog_mul hg hg', isMultiHomog_mul hh hh', ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero hy hy'
    · simp only [map_mul, he, he']; ring

end Forms

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem isValueAt_finset_sum {α : Type} (s : Finset α) (f : α → Ω) (g : α → ℂ)
    (h : ∀ a ∈ s, IsValueAt x (f a) z (g a)) : IsValueAt x (∑ a ∈ s, f a) z (∑ a ∈ s, g a) := by
  induction s using Finset.induction_on with
  | empty => simpa using ValRing.isValueAt_zero_self x z
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact isValueAt_add (h a (Finset.mem_insert_self _ _)) (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

def PolyVal (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (P : Polynomial Ω) (Q : Polynomial ℂ) : Prop :=
  ∀ e, IsValueAt x (P.coeff e) z (Q.coeff e)

theorem PolyVal.add {P P' : Polynomial Ω} {Q Q' : Polynomial ℂ} (h : PolyVal x z P Q) (h' : PolyVal x z P' Q') :
    PolyVal x z (P + P') (Q + Q') := fun e => by
  rw [Polynomial.coeff_add, Polynomial.coeff_add]
  exact isValueAt_add (h e) (h' e)

theorem PolyVal.mul {P P' : Polynomial Ω} {Q Q' : Polynomial ℂ} (h : PolyVal x z P Q) (h' : PolyVal x z P' Q') :
    PolyVal x z (P * P') (Q * Q') := fun e => by
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  exact isValueAt_finset_sum _ _ _ fun a _ => isValueAt_mul (h a.1) (h' a.2)

theorem PolyVal.derivative {P : Polynomial Ω} {Q : Polynomial ℂ} (h : PolyVal x z P Q) :
    PolyVal x z (Polynomial.derivative P) (Polynomial.derivative Q) := fun e => by
  rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative]
  refine isValueAt_mul (h (e + 1)) ?_
  simpa using isValueAt_intCast x z ((e : ℤ) + 1)

theorem polyVal_one : PolyVal x z (1 : Polynomial Ω) (1 : Polynomial ℂ) := fun e => by
  rw [Polynomial.coeff_one, Polynomial.coeff_one]
  split_ifs
  · exact isValueAt_one_self x z
  · exact ValRing.isValueAt_zero_self x z

theorem PolyVal.eval {P : Polynomial Ω} {Q : Polynomial ℂ} (h : PolyVal x z P Q) {t : Ω} {τ : ℂ}
    (ht : IsValueAt x t z τ) : IsValueAt x (P.eval t) z (Q.eval τ) := by
  have h1 : P.natDegree < P.natDegree + Q.natDegree + 1 := by omega
  have h2 : Q.natDegree < P.natDegree + Q.natDegree + 1 := by omega
  rw [Polynomial.eval_eq_sum_range' h1, Polynomial.eval_eq_sum_range' h2]
  exact isValueAt_finset_sum _ _ _ fun e _ => isValueAt_mul (h e) (isValueAt_pow ht e)

theorem PolyVal.unique (hz : z ∈ mcPts (mCoordIdeal x)) {P : Polynomial Ω} {Q Q' : Polynomial ℂ}
    (h : PolyVal x z P Q) (h' : PolyVal x z P Q') : Q = Q' :=
  Polynomial.ext fun e => isValueAt_unique hz (h e) (h' e)

theorem simple_root_value (hz : z ∈ mcPts (mCoordIdeal x)) {μ A B : Polynomial Ω} {Qμ QA QB : Polynomial ℂ}
    (hμ : PolyVal x z μ Qμ) (hA : PolyVal x z A QA) (hB : PolyVal x z B QB)
    (hid : A * μ + B * Polynomial.derivative μ = 1) {t : Ω} {τ : ℂ} (ht : IsValueAt x t z τ)
    (hr : μ.eval t = 0) : Qμ.eval τ = 0 ∧ (Polynomial.derivative Qμ).eval τ ≠ 0 := by
  have h0 : Qμ.eval τ = 0 := by
    have := hμ.eval ht
    rw [hr] at this
    exact isValueAt_zero hz this
  refine ⟨h0, fun h1 => ?_⟩
  have h2 : PolyVal x z 1 (QA * Qμ + QB * Polynomial.derivative Qμ) := by
    rw [← hid]
    exact (hA.mul hμ).add (hB.mul hμ.derivative)
  have h3 := congrArg (Polynomial.eval τ) (h2.unique hz polyVal_one)
  simp [h0, h1] at h3

end Values

section Core

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω : Type} [Field Ω]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k, ι' k)}

def IsRep (y : (Σ k, ι k) → Ω) (P : Polynomial Ω) (n : ℕ) (d : ℕ → K → ℕ) (g h : ℕ → MRing ι) : Prop :=
  P.natDegree < n ∧ ∀ e, IsMultiHomog (g e) (d e) ∧ IsMultiHomog (h e) (d e) ∧ aeval y (h e) ≠ 0 ∧
    aeval y (g e) = P.coeff e * aeval y (h e)

theorem exists_isRep [CharZero Ω] (y : (Σ k, ι k) → Ω) {P : Polynomial Ω} (hP : ∀ e, P.coeff e ∈ blockFnField y) :
    ∃ n d g h, IsRep y P n d g h := by
  choose d g h a b c e using fun e => exists_rep y (hP e)
  exact ⟨P.natDegree + 1, d, g, h, Nat.lt_succ_self _, fun i => ⟨a i, b i, c i, e i⟩⟩

def valPoly (n : ℕ) (g h : ℕ → MRing ι) (w : (Σ k, ι k) → ℂ) : Polynomial ℂ :=
  ∑ e ∈ Finset.range n, Polynomial.C (fr (g e) (h e) w) * Polynomial.X ^ e

theorem isValueAt_of_rep (hv : IsBlockMap κ v) (x' : (Σ k, ι' k) → Ω) {d : K → ℕ} {g h : MRing ι} {c : Ω}
    (hg : IsMultiHomog g d) (hh : IsMultiHomog h d) (hy : aeval (x' ∘ v) h ≠ 0)
    (he : aeval (x' ∘ v) g = c * aeval (x' ∘ v) h) {z : (Σ k, ι' k) → ℂ} (hz : ev h (z ∘ v) ≠ 0) :
    IsValueAt x' c z (fr g h (z ∘ v)) := by
  refine ⟨Function.extend κ d 0, rename v g, rename v h, isMultiHomog_rename_block hv hg,
    isMultiHomog_rename_block hv hh, ?_, ?_, ?_, ?_⟩
  · rw [aeval_rename]; exact hy
  · rw [aeval_rename, aeval_rename]; exact he
  · rw [← ev, ev_rename]; exact hz
  · rw [← ev, ← ev, ev_rename, ev_rename, fr]

theorem polyVal_of_rep (hv : IsBlockMap κ v) (x' : (Σ k, ι' k) → Ω) {P : Polynomial Ω} {n : ℕ} {d : ℕ → K → ℕ}
    {g h : ℕ → MRing ι} (hr : IsRep (x' ∘ v) P n d g h) {z : (Σ k, ι' k) → ℂ}
    (hz : ∀ e < n, ev (h e) (z ∘ v) ≠ 0) : PolyVal x' z P (valPoly n g h (z ∘ v)) := fun e => by
  have hc : (valPoly n g h (z ∘ v)).coeff e = if e < n then fr (g e) (h e) (z ∘ v) else 0 := by
    simp [valPoly, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases he : e < n
  · rw [hc, if_pos he]
    obtain ⟨a, b, c, f⟩ := hr.2 e
    exact isValueAt_of_rep hv x' a b c f (hz e he)
  · rw [hc, if_neg he, Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hr.1; omega)]
    exact ValRing.isValueAt_zero_self _ _

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ev_den {n : ℕ} {h : ℕ → MRing ι} {w : (Σ k, ι k) → ℂ} (H : ev (∏ e ∈ Finset.range n, h e) w ≠ 0) :
    ∀ e < n, ev (h e) w ≠ 0 := fun e he hz => H (by
  rw [ev, map_prod, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_range.2 he) hz)

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem analyticAt_ev (f : MRing ι) (w : (Σ k, ι k) → ℂ) [Fintype (Σ k, ι k)] : AnalyticAt ℂ (ev f) w :=
  AnalyticOnNhd.eval_mvPolynomial _ w (Set.mem_univ _)

theorem exists_good_form [CharZero Ω] (hv : IsBlockMap κ v) (x' : (Σ k, ι' k) → Ω)
    (hle : blockFnField (x' ∘ v) ≤ blockFnField x')
    (hpos : 0 < (blockFnField (x' ∘ v)).relfinrank (blockFnField x')) {t : Ω} (ht : t ∈ blockFnField x') :
    ∃ (E : MRing ι) (a : K → ℕ), IsMultiHomog E a ∧ aeval (x' ∘ v) E ≠ 0 ∧
      ∀ b' ∈ mcPts (mCoordIdeal x'), ∀ wb, SameOrbit wb (b' ∘ v) → ev E wb ≠ 0 → ∀ τ₀, IsValueAt x' t b' τ₀ →
        ∃ (U : Set ((Σ k, ι k) → ℂ)) (ε : ℝ) (r : ((Σ k, ι k) → ℂ) → ℂ), IsOpen U ∧ wb ∈ U ∧ 0 < ε ∧
          AnalyticOnNhd ℂ r U ∧ ∀ b'' ∈ mcPts (mCoordIdeal x'), ∀ w' ∈ U, SameOrbit w' (b'' ∘ v) →
            ∀ τ, IsValueAt x' t b'' τ → ‖τ - τ₀‖ < ε → τ = r w' := by
  obtain ⟨μ, A, B, hμ, hA, hB, hid, hroot⟩ := exists_sep_poly hle hpos ht
  obtain ⟨n₁, d₁, g₁, h₁, r₁⟩ := exists_isRep _ hμ
  obtain ⟨n₂, d₂, g₂, h₂, r₂⟩ := exists_isRep _ hA
  obtain ⟨n₃, d₃, g₃, h₃, r₃⟩ := exists_isRep _ hB
  have m₁ := isMultiHomog_finset_prod (Finset.range n₁) h₁ d₁ fun e _ => (r₁.2 e).2.1
  have m₂ := isMultiHomog_finset_prod (Finset.range n₂) h₂ d₂ fun e _ => (r₂.2 e).2.1
  have m₃ := isMultiHomog_finset_prod (Finset.range n₃) h₃ d₃ fun e _ => (r₃.2 e).2.1
  have mE := isMultiHomog_mul (isMultiHomog_mul m₁ m₂) m₃
  refine ⟨_, _, mE, ?_, ?_⟩
  · simp only [map_mul, map_prod]
    exact mul_ne_zero (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun e _ => (r₁.2 e).2.2.1)
      (Finset.prod_ne_zero_iff.2 fun e _ => (r₂.2 e).2.2.1)) (Finset.prod_ne_zero_iff.2 fun e _ => (r₃.2 e).2.2.1)
  intro b' hb' wb ho hE τ₀ hτ₀
  have hE' := ev_ne_zero_of_orbit mE ho hE
  have split : ∀ {f₁ f₂ f₃ : MRing ι} {w : (Σ k, ι k) → ℂ}, ev (f₁ * f₂ * f₃) w ≠ 0 →
      ev f₁ w ≠ 0 ∧ ev f₂ w ≠ 0 ∧ ev f₃ w ≠ 0 := fun {f₁ f₂ f₃ w} h => by
    have h' : ev f₁ w * ev f₂ w * ev f₃ w ≠ 0 := by simpa [ev] using h
    exact ⟨left_ne_zero_of_mul (left_ne_zero_of_mul h'), right_ne_zero_of_mul (left_ne_zero_of_mul h'),
      right_ne_zero_of_mul h'⟩
  obtain ⟨e₁, e₂, e₃⟩ := split hE'
  have p₁ := polyVal_of_rep hv x' r₁ (ev_den e₁)
  have p₂ := polyVal_of_rep hv x' r₂ (ev_den e₂)
  have p₃ := polyVal_of_rep hv x' r₃ (ev_den e₃)
  obtain ⟨k₀, k₁⟩ := simple_root_value hb' p₁ p₂ p₃ hid hτ₀ hroot
  have orb : ∀ {w w' : (Σ k, ι k) → ℂ}, SameOrbit w w' → valPoly n₁ g₁ h₁ w = valPoly n₁ g₁ h₁ w' :=
    fun ho => Finset.sum_congr rfl fun e _ => by rw [fr_orbit (r₁.2 e).1 (r₁.2 e).2.1 ho]
  rw [← orb ho] at k₀ k₁
  have hw₁ := (split hE).1
  obtain ⟨U, ε, r, hU, hw, hε, han, huniq⟩ := exists_analytic_root (fun e w => fr (g₁ e) (h₁ e) w) n₁ wb τ₀
    (fun e he => (analyticAt_ev _ wb).div (analyticAt_ev _ wb) (ev_den hw₁ e he)) k₀ k₁
  refine ⟨U ∩ {w | ev (∏ e ∈ Finset.range n₁, h₁ e) w ≠ 0}, ε, r,
    hU.inter (isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const), ⟨hw, hw₁⟩, hε,
    han.mono Set.inter_subset_left, ?_⟩
  intro b'' hb'' w' hw' ho' τ hτ hlt
  have p := polyVal_of_rep hv x' r₁ (ev_den (ev_ne_zero_of_orbit m₁ ho' hw'.2))
  have h0 := p.eval hτ
  rw [hroot] at h0
  have h1 := isValueAt_zero hb'' h0
  rw [← orb ho'] at h1
  exact huniq w' hw'.1 τ hlt h1

theorem isValueAt_ratio (x : (Σ k, ι k) → Ω) {q m : Σ k, ι k} (hqm : q.1 = m.1) (hx : x m ≠ 0)
    {z : (Σ k, ι k) → ℂ} (hz : z m ≠ 0) : IsValueAt x (x q / x m) z (z q / z m) := by
  refine ⟨_, X q, X m, isMultiHomog_X_single q, ?_, by simpa using hx, ?_, by simpa using hz, by simp⟩
  · rw [hqm]; exact isMultiHomog_X_single m
  · simp [div_mul_cancel₀ _ hx]

theorem coord_ne_zero {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x))
    {m : Σ k, ι k} (hm : z m ≠ 0) : x m ≠ 0 := fun h => hm (by
  have h1 := eval_eq_zero_of_mem_mcPts hz
    (mem_mCoordIdeal_of_aeval_eq_zero x (isMultiHomog_X_single m) (by simpa using h))
  simpa using h1)

end Core

section General

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Ω : Type} [Field Ω]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k, ι' k)}

theorem exists_form_local_inverse [CharZero Ω] (hv : IsBlockMap κ v) (x' : (Σ k, ι' k) → Ω)
    (hle : blockFnField (x' ∘ v) ≤ blockFnField x')
    (hpos : 0 < (blockFnField (x' ∘ v)).relfinrank (blockFnField x')) :
    ∃ (D : MRing ι) (a : K → ℕ), IsMultiHomog D a ∧ aeval (x' ∘ v) D ≠ 0 ∧
      ∀ b' ∈ mcPts (mCoordIdeal x'), ∀ wb, SameOrbit wb (b' ∘ v) → ev D wb ≠ 0 →
        ∃ (V : Set ((Σ k, ι k) → ℂ)) (V' : Set ((Σ k, ι' k) → ℂ)) (s : ((Σ k, ι k) → ℂ) → (Σ k, ι' k) → ℂ),
          IsOpen V ∧ wb ∈ V ∧ IsOpen V' ∧ b' ∈ V' ∧ AnalyticOnNhd ℂ s V ∧
            ∀ b'' ∈ V' ∩ mcPts (mCoordIdeal x'), ∀ w' ∈ V, SameOrbit w' (b'' ∘ v) → SameOrbit (s w') b'' := by
  let Pr := {r : (Σ k, ι' k) × (Σ k, ι' k) // r.1.1 = r.2.1 ∧ x' r.2 ≠ 0}
  have hmem : ∀ r : Pr, x' r.1.1 / x' r.1.2 ∈ blockFnField x' := fun r =>
    IntermediateField.subset_adjoin _ _ ⟨_, _, r.2.1, rfl⟩
  choose E a hEa hE0 hE1 using fun r : Pr => exists_good_form hv x' hle hpos (hmem r)
  haveI : Fintype Pr := Fintype.ofFinite _
  refine ⟨∏ r, E r, ∑ r, a r, isMultiHomog_finset_prod _ _ _ fun r _ => hEa r, ?_, ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun r _ => hE0 r
  intro b' hb' wb ho hD
  have hD' : ∀ r, ev (E r) wb ≠ 0 := fun r h0 => hD (by
    rw [ev, map_prod, map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ r) h0)
  choose m hm using hb'.1
  have hxm : ∀ k, x' ⟨k, m k⟩ ≠ 0 := fun k => coord_ne_zero hb' (hm k)
  let c : (Σ k, ι' k) → (Σ k, ι' k) := fun q => ⟨q.1, m q.1⟩
  let pr : (Σ k, ι' k) → Pr := fun q => ⟨(q, c q), rfl, hxm q.1⟩
  have hval : ∀ q, IsValueAt x' (x' q / x' (c q)) b' (b' q / b' (c q)) := fun q =>
    isValueAt_ratio (q := q) (m := c q) x' rfl (hxm q.1) (hm q.1)
  choose U ε r hU hw hε han huniq using fun q => hE1 (pr q) b' hb' wb ho (hD' _) _ (hval q)
  refine ⟨⋂ q, U q, {z | ∀ q, z (c q) ≠ 0 ∧ ‖z q / z (c q) - b' q / b' (c q)‖ < ε q}, fun w q => r q w,
    isOpen_iInter_of_finite hU, Set.mem_iInter.2 hw, ?_, fun q => ⟨hm q.1, by simpa using hε q⟩, ?_, ?_⟩
  · rw [isOpen_iff_mem_nhds]
    intro z hz
    have h : ∀ q, ∀ᶠ z' in 𝓝 z, z' (c q) ≠ 0 ∧ ‖z' q / z' (c q) - b' q / b' (c q)‖ < ε q := fun q => by
      have c1 : ContinuousAt (fun z' : (Σ k, ι' k) → ℂ => z' (c q)) z := (continuous_apply _).continuousAt
      have c2 : ContinuousAt (fun z' : (Σ k, ι' k) → ℂ => z' q) z := (continuous_apply _).continuousAt
      have c3 : ContinuousAt (fun z' : (Σ k, ι' k) → ℂ => ‖z' q / z' (c q) - b' q / b' (c q)‖) z :=
        ((c2.div c1 (hz q).1).sub continuousAt_const).norm
      exact (c1.eventually_ne (hz q).1).and (c3 (Iio_mem_nhds (hz q).2))
    exact Filter.eventually_all.2 h
  · intro w hw'
    rw [analyticAt_pi_iff]
    exact fun q => han q w (Set.mem_iInter.1 hw' q)
  · rintro b'' ⟨hb1, hb2⟩ w' hw' ho'
    refine ⟨fun k => (b'' ⟨k, m k⟩)⁻¹, fun k => inv_ne_zero (hb1 ⟨k, m k⟩).1, ?_⟩
    funext q
    have hu := huniq q b'' hb2 w' (Set.mem_iInter.1 hw' q) ho' _
      (isValueAt_ratio (q := q) (m := c q) x' rfl (hxm q.1) (hb1 q).1) (hb1 q).2
    exact hu.symm.trans (div_eq_inv_mul _ _)

theorem aeval_eq_zero_of_mem {x : (Σ k, ι k) → Ω} {f : MRing ι} (hf : f ∈ mCoordIdeal x) : aeval x f = 0 := by
  have h : mConeMap x f = 0 := hf
  have e : ((aeval (fun _ => (1 : Ω)) : MvPolynomial K Ω →ₐ[Ω] Ω).restrictScalars ℤ).comp (mConeMap x) =
      aeval x := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap]
  have h2 := DFunLike.congr_fun e f
  rw [← h2, AlgHom.comp_apply, h, map_zero]

end General

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal y') (d + 2) → ∃ (D : MRing (baseIdx ι M.blk)) (a : NonPluckerBlocks M.blk → ℕ), IsMultiHomog D a ∧ D ∉ mCoordIdeal M.x ∧ ∀ b' ∈ mcPts (mCoordIdeal M'.x), ∀ wb, SameOrbit wb (b' ∘ Cv.v) → eval wb (map (Int.castRingHom ℂ) D) ≠ 0 → ∃ (V : Set ((Σ k, baseIdx ι M.blk k) → ℂ)) (V' : Set ((Σ k, baseIdx ι' M'.blk k) → ℂ)) (s : ((Σ k, baseIdx ι M.blk k) → ℂ) → (Σ k, baseIdx ι' M'.blk k) → ℂ), IsOpen V ∧ wb ∈ V ∧ IsOpen V' ∧ b' ∈ V' ∧ AnalyticOnNhd ℂ s V ∧ ∀ b'' ∈ V' ∩ mcPts (mCoordIdeal M'.x), ∀ w' ∈ V, SameOrbit w' (b'' ∘ Cv.v) → SameOrbit (s w') b'' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv d _ _
  have hle : blockFnField (M'.x ∘ Cv.v) ≤ blockFnField M'.x :=
    IntermediateField.adjoin_le_iff.2 (by
      rintro t ⟨p, q, hpq, rfl⟩
      exact IntermediateField.subset_adjoin _ _
        ⟨Cv.v p, Cv.v q, by rw [Cv.block.2.2.1, Cv.block.2.2.1, hpq], rfl⟩)
  obtain ⟨D, a, hD, hD0, hmain⟩ := exists_form_local_inverse Cv.block M'.x hle Cv.deg_pos
  refine ⟨D, a, hD, fun hmem => hD0 ?_, hmain⟩
  have e : M'.x ∘ Cv.v = fun q => Cv.φ (M.x q) := funext Cv.x_eq
  have e2 : (aeval fun q => Cv.φ (M.x q)) D = Cv.φ (aeval M.x D) :=
    (MvPolynomial.comp_aeval_apply M.x Cv.φ.toIntAlgHom D).symm
  rw [e, e2, aeval_eq_zero_of_mem hmem, map_zero]

end GlobalTheory.CompanionTheory.Ar.PB.BaseEtale
