import Formalism.HermitianCurvature.HermitianCurvatureProofs.StepClaimFromStepsFull

namespace Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem weighted_L2_zero (B : Base) (wt : B.Ω → ℝ) : WeightedL2 B wt (fun _ => 0) := by
  unfold WeightedL2
  refine ⟨aestronglyMeasurable_const, ?_⟩
  simp

theorem weighted_L2_const_mul (B : Base) (wt : B.Ω → ℝ) (a : ℂ) (f : B.Ω → ℂ) (hf : WeightedL2 B wt f) :
    WeightedL2 B wt (fun ω => a * f ω) := by
  unfold WeightedL2 at *
  obtain ⟨hm, hi⟩ := hf
  refine ⟨hm.const_mul a, ?_⟩
  refine (hi.const_mul (‖a‖ ^ 2)).congr (ae_of_all _ fun ω => ?_)
  simp only [norm_mul, mul_pow]
  ring

theorem weighted_L2_add (B : Base) (wt : B.Ω → ℝ) (hw : ∀ ω, 0 ≤ wt ω) (f g : B.Ω → ℂ) (hf : WeightedL2 B wt f)
    (hg : WeightedL2 B wt g) : WeightedL2 B wt (fun ω => f ω + g ω) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  have hcross : AEStronglyMeasurable
      (fun ω => ((wt ω * ‖f ω‖ ^ 2 : ℝ) : ℂ) * conj (g ω) / conj (f ω)) B.μ := by
    have h1 : AEMeasurable (fun ω => ((wt ω * ‖f ω‖ ^ 2 : ℝ) : ℂ)) B.μ :=
      Complex.measurable_ofReal.comp_aemeasurable hf.2.1.aemeasurable
    have h2 : AEMeasurable (fun ω => conj (g ω)) B.μ :=
      (Complex.continuous_conj.measurable).comp_aemeasurable hg.1.aemeasurable
    have h3 : AEMeasurable (fun ω => conj (f ω)) B.μ :=
      (Complex.continuous_conj.measurable).comp_aemeasurable hf.1.aemeasurable
    exact ((h1.mul h2).div h3).aestronglyMeasurable
  have heq : (fun ω => wt ω * ‖f ω + g ω‖ ^ 2) = fun ω => wt ω * ‖f ω‖ ^ 2 + wt ω * ‖g ω‖ ^ 2 +
      2 * (((wt ω * ‖f ω‖ ^ 2 : ℝ) : ℂ) * conj (g ω) / conj (f ω)).re := by
    funext ω
    by_cases h0 : f ω = 0
    · simp [h0]
    · have hc : conj (f ω) ≠ 0 := by simpa using h0
      have h1 : ((wt ω * ‖f ω‖ ^ 2 : ℝ) : ℂ) * conj (g ω) / conj (f ω) = (wt ω : ℂ) * (f ω * conj (g ω)) := by
        rw [div_eq_iff hc]
        push_cast
        rw [← Complex.mul_conj']
        ring
      rw [h1, Complex.re_ofReal_mul, Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add]
      ring
  have hmeas : AEStronglyMeasurable (fun ω => wt ω * ‖f ω + g ω‖ ^ 2) B.μ := by
    rw [heq]
    exact (hf.2.1.add hg.2.1).add ((Complex.continuous_re.comp_aestronglyMeasurable hcross).const_mul 2)
  refine Integrable.mono' ((hf.2.const_mul 2).add (hg.2.const_mul 2)) hmeas (Filter.Eventually.of_forall ?_)
  intro ω
  have h1 : ‖f ω + g ω‖ ≤ ‖f ω‖ + ‖g ω‖ := norm_add_le _ _
  have h2 : ‖f ω + g ω‖ ^ 2 ≤ 2 * ‖f ω‖ ^ 2 + 2 * ‖g ω‖ ^ 2 := by
    nlinarith [norm_nonneg (f ω + g ω), norm_nonneg (f ω), norm_nonneg (g ω), sq_nonneg (‖f ω‖ - ‖g ω‖)]
  rw [Real.norm_of_nonneg (mul_nonneg (hw ω) (by positivity))]
  simp only [Pi.add_apply]
  nlinarith [hw ω, mul_le_mul_of_nonneg_left h2 (hw ω)]

theorem weighted_L2_sum (B : Base) (wt : B.Ω → ℝ) (hw : ∀ ω, 0 ≤ wt ω) {I : Type} (s : Finset I) (f : I → B.Ω → ℂ)
    (hf : ∀ i ∈ s, WeightedL2 B wt (f i)) : WeightedL2 B wt (fun ω => ∑ i ∈ s, f i ω) := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using weighted_L2_zero B wt
  · intro i s hi ih hf
    have e : (fun ω => ∑ j ∈ insert i s, f j ω) = fun ω => f i ω + ∑ j ∈ s, f j ω := by
      funext ω
      rw [Finset.sum_insert hi]
    rw [e]
    exact weighted_L2_add B wt hw _ _ (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem coeff_id (s : Finset ℝ) (d k j : ℕ) (hs : s.card = d + 1) (hk : k ≤ d) :
    ∑ x ∈ s, (Lagrange.basis s id x).coeff j * x ^ k = if j = k then 1 else 0 := by
  have h := Lagrange.eq_interpolate (s := s) (v := id) (f := (Polynomial.X : Polynomial ℝ) ^ k)
    (Function.injective_id.injOn) (by
      rw [Polynomial.degree_X_pow, hs]; exact_mod_cast Nat.lt_succ_of_le hk)
  have h2 := congrArg (fun p => Polynomial.coeff p j) h
  simp only [Lagrange.interpolate_apply, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.eval_pow,
    Polynomial.eval_X, id, Polynomial.coeff_X_pow] at h2
  rw [h2]; apply Finset.sum_congr rfl; intros; ring

theorem extract (N d : ℕ) (grid : Fin N → Finset ℝ) (hg : ∀ a, (grid a).card = d + 1)
    (c : (Fin N → Fin (d + 1)) → ℂ) (κ : Fin N → Fin (d + 1)) :
    c κ = ∑ g ∈ Fintype.piFinset grid, ((∏ a, (Lagrange.basis (grid a) id (g a)).coeff (κ a : ℕ) : ℝ) : ℂ) *
      ∑ κ' : Fin N → Fin (d + 1), ((∏ a, (g a) ^ (κ' a : ℕ) : ℝ) : ℂ) * c κ' := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have key : ∀ κ' : Fin N → Fin (d + 1), ∑ g ∈ Fintype.piFinset grid,
      ((∏ a, (Lagrange.basis (grid a) id (g a)).coeff (κ a : ℕ) : ℝ) : ℂ) *
        (((∏ a, (g a) ^ (κ' a : ℕ) : ℝ) : ℂ) * c κ') = (if κ = κ' then 1 else 0) * c κ' := by
    intro κ'
    have h1 : ∑ g ∈ Fintype.piFinset grid, (∏ a, (Lagrange.basis (grid a) id (g a)).coeff (κ a : ℕ)) *
        (∏ a, (g a) ^ (κ' a : ℕ)) = if κ = κ' then (1 : ℝ) else 0 := by
      simp_rw [← Finset.prod_mul_distrib]
      rw [← Finset.prod_univ_sum (t := grid)
        (f := fun a x => (Lagrange.basis (grid a) id x).coeff (κ a : ℕ) * x ^ (κ' a : ℕ))]
      have h3 : ∀ a, ∑ x ∈ grid a, (Lagrange.basis (grid a) id x).coeff (κ a : ℕ) * x ^ (κ' a : ℕ) =
          if (κ a : ℕ) = (κ' a : ℕ) then 1 else 0 :=
        fun a => coeff_id (grid a) d _ _ (hg a) (Nat.lt_succ_iff.1 (κ' a).2)
      simp_rw [h3]
      by_cases h : κ = κ'
      · subst h; simp
      · rw [if_neg h]
        obtain ⟨a, ha⟩ := Function.ne_iff.1 h
        apply Finset.prod_eq_zero (Finset.mem_univ a)
        rw [if_neg]; intro hh; exact ha (Fin.ext hh)
    have h4 : ((if κ = κ' then (1 : ℂ) else 0)) = (((if κ = κ' then (1 : ℝ) else 0) : ℝ) : ℂ) := by
      split_ifs <;> simp
    rw [h4, ← h1]; push_cast; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring
  simp_rw [key]; simp

theorem coefficient_L2 : InterpolationCoefficientsInL2 := by
  intro B N d wt m c J hw hJ hm hL κ
  choose grid hsub hcard using fun a => (hJ a).exists_subset_card_eq (d + 1)
  have h : c κ = fun ω => ∑ g ∈ Fintype.piFinset grid,
      ((∏ a, (Lagrange.basis (grid a) id (g a)).coeff (κ a : ℕ) : ℝ) : ℂ) * m g ω := by
    funext ω
    rw [extract N d grid hcard (fun κ' => c κ' ω) κ]
    simp_rw [hm]
  rw [h]
  apply weighted_L2_sum B wt hw
  intro g hgm
  apply weighted_L2_const_mul
  apply hL
  intro a
  exact hsub a (Fintype.mem_piFinset.1 hgm a)

end Formalism.FourierDecayAlt.P.LEx1

namespace Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem dS_poly (B : Base) {A A' : Type} (T : Fn B A → Fn B A') (u : Fn B A) (d : ℕ) (c : ℕ → Fn B A')
    (hc : ∀ (s : ℝ) ω a, conjS B T u s ω a = ∑ q ∈ range (d + 1), (s : ℂ) ^ q * c q ω a) (p : ℕ) (ω : B.Ω) (a : A') :
    dS B T u p ω a = p.factorial * (if p < d + 1 then c p ω a else 0) := by
  unfold dS
  have h : (fun s : ℝ => conjS B T u s ω a) = fun s : ℝ => (mkP d (fun q => c q ω a)).eval (s : ℂ) := by
    funext s; rw [hc, mkP_eval]
  rw [h, iterDeriv_poly]
  simp only [Complex.ofReal_zero]
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative, mkP_coeff]
  simp [Nat.descFactorial_self]

theorem meas_th (B : Base) (ε σ : ℝ) : Measurable fun ω => th ε σ (B.G ω) := by
  unfold th
  exact (B.G_meas.div (B.G_meas.add_const ε)).pow_const σ

theorem coefIntegrable : CoefIntegrable := by
  intro B S σ _ hM hW h4 h4' ε hε Y hY p
  obtain ⟨c, hc⟩ := h4 Y hY
  have hth : ∀ ω, 0 ≤ th ε σ (B.G ω) := fun ω =>
    Real.rpow_nonneg (div_nonneg (B.G_pos ω).le (by have := B.G_pos ω; linarith)) _
  have hd : ∀ ω k, 0 ≤ S.d Y ω k := fun ω k => (hW.2 Y hY ω k).le
  have hk : ∀ k, WeightedL2 B (fun ω => th ε σ (B.G ω) * S.d Y ω k) (fun ω => S.ds Y p ω k) := by
    intro k
    have hco := coefficient_L2 B 1 (S.r + 1) (fun ω => th ε σ (B.G ω) * S.d Y ω k) (fun y ω => S.gs Y (y 0) ω k)
      (fun κ ω => c (κ 0 : ℕ) ω k) (fun _ => Set.univ) (fun ω => mul_nonneg (hth ω) (hd ω k))
      (fun _ => Set.infinite_univ)
      (by
        intro y ω
        show conjS B (S.g Y) S.X (y 0) ω k = _
        rw [hc (y 0) ω k]
        rw [← (Equiv.funUnique (Fin 1) (Fin (S.r + 1 + 1))).symm.sum_comp]
        rw [← Fin.sum_univ_eq_sum_range (fun q => ((y 0 : ℝ) : ℂ) ^ q * c q ω k)]
        apply Finset.sum_congr rfl
        intro i _
        simp [Equiv.funUnique])
      (by
        intro y _
        refine ⟨((hM.2.2 Y hY).2 (y 0) k).aestronglyMeasurable, ?_⟩
        refine Integrable.mono' ((h4' ε hε).1 Y hY (y 0)) ?_ (Filter.Eventually.of_forall ?_)
        · exact (((meas_th B ε σ).mul ((hM.2.2 Y hY).1 k)).mul
            (((hM.2.2 Y hY).2 (y 0) k).norm.pow_const 2)).aestronglyMeasurable
        · intro ω
          rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (hth ω) (hd ω k)) (by positivity)), mul_assoc]
          apply mul_le_mul_of_nonneg_left _ (hth ω)
          unfold LE.sq
          exact Finset.single_le_sum (f := fun k => S.d Y ω k * ‖S.gs Y (y 0) ω k‖ ^ 2)
            (fun k _ => mul_nonneg (hd ω k) (by positivity)) (Finset.mem_univ k))
    have hds : (fun ω => S.ds Y p ω k) =
        fun ω => (p.factorial : ℂ) * (if p < S.r + 1 + 1 then c p ω k else 0) := by
      funext ω
      exact dS_poly B (S.g Y) S.X (S.r + 1) c hc p ω k
    rw [hds]
    apply weighted_L2_const_mul
    by_cases hp : p < S.r + 1 + 1
    · simp only [if_pos hp]
      exact hco (fun _ => ⟨p, hp⟩)
    · simp only [if_neg hp]
      exact weighted_L2_zero B _
  have he : (fun ω => th ε σ (B.G ω) * LE.sq B (S.d Y) (S.ds Y p) ω) =
      fun ω => ∑ k, (th ε σ (B.G ω) * S.d Y ω k) * ‖S.ds Y p ω k‖ ^ 2 := by
    funext ω; unfold LE.sq; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
  rw [he]
  exact integrable_finset_sum _ (fun k _ => (hk k).2)

end Formalism.FourierDecayAlt.P.LEx1

namespace Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem opt_delta (x A Bb : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ Bb)
    (h : ∀ δ : ℝ, 0 < δ → x ≤ (A / δ + δ * Bb) / 2) : x ≤ √A * √Bb := by
  obtain ⟨a, ha, rfl⟩ : ∃ a, 0 ≤ a ∧ A = a ^ 2 := ⟨√A, Real.sqrt_nonneg _, (Real.sq_sqrt hA).symm⟩
  obtain ⟨b, hb, rfl⟩ : ∃ b, 0 ≤ b ∧ Bb = b ^ 2 := ⟨√Bb, Real.sqrt_nonneg _, (Real.sq_sqrt hB).symm⟩
  rw [Real.sqrt_sq ha, Real.sqrt_sq hb]
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · have h1 := h (a / b) (div_pos ha' hb')
      have hane : a ≠ 0 := ha'.ne'
      have hbne : b ≠ 0 := hb'.ne'
      have e : (a ^ 2 / (a / b) + a / b * b ^ 2) / 2 = a * b := by
        field_simp <;> ring
      linarith
    · subst hb'
      by_contra hx
      push_neg at hx
      have hx0 : 0 < x := by simpa using hx
      have hδ : 0 < 2 * a ^ 2 / x := div_pos (mul_pos two_pos (pow_pos ha' 2)) hx0
      have h1 := h _ hδ
      have hane : a ≠ 0 := ha'.ne'
      have hxne : x ≠ 0 := hx0.ne'
      have e : a ^ 2 / (2 * a ^ 2 / x) = x / 2 := by
        field_simp <;> ring
      have e3 : 2 * a ^ 2 / x * (0:ℝ) ^ 2 = 0 := by simp
      linarith
  · subst ha'
    by_contra hx
    push_neg at hx
    have hx0 : 0 < x := by simpa using hx
    have hne : b ^ 2 + 1 ≠ 0 := by positivity
    have hδ : 0 < x / (b ^ 2 + 1) := div_pos hx0 (by positivity)
    have h1 := h _ hδ
    have e : x / (b ^ 2 + 1) * (b ^ 2 + 1) = x := by field_simp
    have e2 : x / (b ^ 2 + 1) * b ^ 2 ≤ x / (b ^ 2 + 1) * (b ^ 2 + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hδ.le
    have e3 : (0:ℝ) ^ 2 / (x / (b ^ 2 + 1)) = 0 := by simp
    linarith

theorem csTerm : CSTerm := by
  intro hTB hC B S σ ε h4 hε hM hW hI4 hI4' hCI Y hY p
  have hth : ∀ ω, 0 ≤ th ε σ (B.G ω) := fun ω =>
    Real.rpow_nonneg (div_nonneg (B.G_pos ω).le (by have := B.G_pos ω; linarith)) _
  have hd : ∀ ω k, 0 ≤ S.d Y ω k := fun ω k => (hW.2 Y hY ω k).le
  have hds0 : S.ds Y 0 = S.gX Y := dS_zero B _ _
  have hEi : Integrable (fun ω => th ε σ (B.G ω) * LE.sq B (S.d Y) (S.gX Y) ω) B.μ := by
    have := hCI ε hε Y hY 0
    rwa [hds0] at this
  have hDi := hCI ε hε Y hY p
  have hfac : (0:ℝ) < p.factorial := by exact_mod_cast p.factorial_pos
  have hσ : 0 < 4 * σ := by linarith
  set K : ℝ := Real.exp 1 * p.factorial * (4 * σ) ^ p with hK
  have hKpos : 0 < K := by positivity
  have hE0 : 0 ≤ S.En ε σ Y := integral_nonneg fun ω => mul_nonneg (hth ω) (sq_nonneg' B _ hd _ ω)
  have hD0 : 0 ≤ S.Dn ε σ Y p := integral_nonneg fun ω => mul_nonneg (hth ω) (sq_nonneg' B _ hd _ ω)
  set I : ℂ := ∫ ω, (ld p (th ε σ) (B.G ω) : ℂ) * pr B (S.d Y) (S.gX Y) (S.ds Y p) ω ∂B.μ with hI
  have hb : ∀ δ : ℝ, 0 < δ → ‖I‖ / K ≤ (S.En ε σ Y / δ + δ * S.Dn ε σ Y p) / 2 := by
    intro δ hδ
    have hg : Integrable (fun ω => K * (((th ε σ (B.G ω) * LE.sq B (S.d Y) (S.gX Y) ω) / δ +
        δ * (th ε σ (B.G ω) * LE.sq B (S.d Y) (S.ds Y p) ω)) / 2)) B.μ :=
      (((hEi.div_const δ).add (hDi.const_mul δ)).div_const 2).const_mul K
    have h1 := norm_integral_le_of_norm_le hg (f := fun ω => (ld p (th ε σ) (B.G ω) : ℂ) *
        pr B (S.d Y) (S.gX Y) (S.ds Y p) ω) (Eventually.of_forall fun ω => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have a1 := hTB hC σ ε h4 hε p (B.G ω) (B.G_pos ω)
      have a2 := pr_bound B (S.d Y) hd (S.gX Y) (S.ds Y p) δ hδ ω
      calc |ld p (th ε σ) (B.G ω)| * ‖pr B (S.d Y) (S.gX Y) (S.ds Y p) ω‖
          ≤ (K * th ε σ (B.G ω)) * ((LE.sq B (S.d Y) (S.gX Y) ω / δ + δ * LE.sq B (S.d Y) (S.ds Y p) ω) / 2) :=
            mul_le_mul a1 a2 (norm_nonneg _) (mul_nonneg hKpos.le (hth ω))
        _ = _ := by ring)
    have h2 : ∫ ω, K * (((th ε σ (B.G ω) * LE.sq B (S.d Y) (S.gX Y) ω) / δ +
        δ * (th ε σ (B.G ω) * LE.sq B (S.d Y) (S.ds Y p) ω)) / 2) ∂B.μ =
        K * ((S.En ε σ Y / δ + δ * S.Dn ε σ Y p) / 2) := by
      rw [integral_const_mul, integral_div, integral_add (hEi.div_const δ) (hDi.const_mul δ), integral_div,
        integral_const_mul]
      rfl
    rw [h2] at h1
    rw [div_le_iff₀ hKpos]
    linarith
  have hfin := opt_delta _ _ _ hE0 hD0 hb
  rw [div_le_iff₀ hKpos] at hfin
  show ‖I / (p.factorial : ℂ)‖ ≤ _
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ hfac]
  calc ‖I‖ ≤ √(S.En ε σ Y) * √(S.Dn ε σ Y p) * K := hfin
    _ = _ := by rw [hK]; ring

end Formalism.FourierDecayAlt.P.LEx1

namespace Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem meas_th' (B : Base) (ε σ : ℝ) : Measurable fun ω => th ε σ (B.G ω) := meas_th B ε σ

theorem L1 (hTR : ThetaRange) (hTL : ThetaLimit) (B : Base) (σ : ℝ) (hσ : 0 ≤ σ) (f : B.Ω → ℝ)
    (hf : Integrable f B.μ) :
    Tendsto (fun ε : ℝ => ∫ ω, th ε σ (B.G ω) * f ω ∂B.μ) (𝓝[>] 0) (𝓝 (∫ ω, f ω ∂B.μ)) := by
  have lim : ∀ ω, Tendsto (fun ε : ℝ => th ε σ (B.G ω) * f ω) (𝓝[>] 0) (𝓝 (f ω)) := by
    intro ω
    have h0 := hTL σ 0 (B.G ω) (B.G_pos ω)
    simp only [ld, iteratedDeriv_zero, Real.exp_log (B.G_pos ω), ↓reduceIte] at h0
    simpa using h0.mul_const (f ω)
  refine tendsto_integral_filter_of_dominated_convergence (fun ω => ‖f ω‖) ?_ ?_ hf.norm
    (ae_of_all _ lim)
  · exact Filter.Eventually.of_forall fun ε =>
      (meas_th B ε σ).aestronglyMeasurable.mul hf.aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine ae_of_all _ fun ω => ?_
    obtain ⟨h1, h2⟩ := hTR ε σ (B.G ω) hε hσ (B.G_pos ω)
    rw [norm_mul, Real.norm_of_nonneg h1.le]
    exact mul_le_of_le_one_left (norm_nonneg _) h2

theorem L2 (hTS : ThetaSmooth) (hTR : ThetaRange) (hTL : ThetaLimit) (hTB : ThetaBound) (hC : E.CauchyTheta)
    (B : Base) (σ : ℝ) (h4 : 4 ≤ σ) (p : ℕ) (hp : p ≠ 0) (h : B.Ω → ℂ) (hh : Integrable h B.μ) :
    Tendsto (fun ε : ℝ => ∫ ω, (ld p (th ε σ) (B.G ω) : ℂ) * h ω ∂B.μ) (𝓝[>] 0) (𝓝 0) := by
  have hσ : 0 ≤ σ := by linarith
  have lim : ∀ ω, Tendsto (fun ε : ℝ => (ld p (th ε σ) (B.G ω) : ℂ) * h ω) (𝓝[>] 0) (𝓝 0) := by
    intro ω
    have h0 := hTL σ p (B.G ω) (B.G_pos ω)
    rw [if_neg hp] at h0
    have h1 := ((Complex.continuous_ofReal.tendsto 0).comp h0).mul_const (h ω)
    simpa using h1
  have hK : 0 ≤ Real.exp 1 * p.factorial * (4 * σ) ^ p :=
    mul_nonneg (by positivity) (pow_nonneg (by linarith) p)
  have hmeas : ∀ ε : ℝ, Measurable fun ω => ld p (th ε σ) (B.G ω) := by
    intro ε
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
    have hm : Measurable (iteratedDeriv (q + 1) (fun u => th ε σ (Real.exp u))) := by
      rw [iteratedDeriv_succ]
      exact measurable_deriv _
    unfold ld
    exact hm.comp (Real.measurable_log.comp B.G_meas)
  have key := tendsto_integral_filter_of_dominated_convergence (μ := B.μ) (l := 𝓝[>] (0:ℝ))
    (F := fun ε ω => (ld p (th ε σ) (B.G ω) : ℂ) * h ω) (f := fun _ => (0:ℂ))
    (fun ω => Real.exp 1 * p.factorial * (4 * σ) ^ p * ‖h ω‖)
    (Filter.Eventually.of_forall fun ε =>
      (Complex.measurable_ofReal.comp (hmeas ε)).aestronglyMeasurable.mul hh.aestronglyMeasurable)
    (by
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      refine ae_of_all _ fun ω => ?_
      have hb := hTB hC σ ε h4 hε p (B.G ω) (B.G_pos ω)
      obtain ⟨_, h2⟩ := hTR ε σ (B.G ω) hε hσ (B.G_pos ω)
      have h3 : |ld p (th ε σ) (B.G ω)| ≤ Real.exp 1 * p.factorial * (4 * σ) ^ p := by
        calc _ ≤ _ := hb
          _ ≤ Real.exp 1 * p.factorial * (4 * σ) ^ p * 1 := mul_le_mul_of_nonneg_left h2 hK
          _ = _ := mul_one _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _))
    (hh.norm.const_mul _) (ae_of_all _ lim)
  simpa using key

theorem domConv : DomConv := by
  intro hTR hTL hTB hTZ hC B S σ h4 hM hW hI4 hStar hInt Y hY hIp
  have hσ : 0 ≤ σ := by linarith
  have hd : ∀ ω k, 0 ≤ S.d Y ω k := fun ω k => (hW.2 Y hY ω k).le
  have hds0 : S.ds Y 0 = S.gX Y := dS_zero B _ _
  have hIg : Integrable (LE.sq B (S.d Y) (S.gX Y)) B.μ := by
    have := hIp 0
    rwa [hds0] at this
  have hmds : ∀ p k, Measurable fun ω => S.ds Y p ω k := fun p k => dsMeas B S hM hI4 Y hY p k
  have hmg : ∀ k, Measurable fun ω => S.gX Y ω k := by
    intro k
    have := hmds 0 k
    rwa [hds0] at this
  have l1 : Tendsto (fun ε => S.Ath ε σ) (𝓝[>] 0) (𝓝 S.A0) := L1 hTR hTL B σ hσ _ hInt
  have l2 : Tendsto (fun ε => S.En ε σ Y) (𝓝[>] 0) (𝓝 (∫ ω, LE.sq B (S.d Y) (S.gX Y) ω ∂B.μ)) :=
    L1 hTR hTL B σ hσ _ hIg
  have l3 : ∀ p, p ≠ 0 → Tendsto (fun ε => S.term ε σ Y p) (𝓝[>] 0) (𝓝 0) := by
    intro p hp
    have := (L2 thetaSmooth hTR hTL hTB hC B σ h4 p hp _ (int_pr B (S.d Y) hd (S.gX Y) (S.ds Y p)
      ((hM.2.2 Y hY).1) hmg (hmds p) hIg (hIp p))).div_const (p.factorial : ℂ)
    simpa [Step.term] using this
  have lsum : Tendsto (fun ε => ∑ p ∈ range (S.r + 2), S.term ε σ Y p) (𝓝[>] 0)
      (𝓝 (∑ p ∈ range (S.r + 2), if p = 0 then ((∫ ω, LE.sq B (S.d Y) (S.gX Y) ω ∂B.μ : ℝ) : ℂ) else 0)) := by
    apply tendsto_finset_sum
    intro p _
    by_cases hp : p = 0
    · subst hp
      simp only [if_true]
      simp_rw [hTZ B S _ σ Y]
      exact (Complex.continuous_ofReal.tendsto _).comp l2
    · rw [if_neg hp]; exact l3 p hp
  have llhs : Tendsto (fun ε => ((|S.P Y| * S.Ath ε σ : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 ((|S.P Y| * S.A0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp (l1.const_mul _)
  have heq : (fun ε => ((|S.P Y| * S.Ath ε σ : ℝ) : ℂ)) =ᶠ[𝓝[>] 0]
      fun ε => ∑ p ∈ range (S.r + 2), S.term ε σ Y p := by
    filter_upwards [self_mem_nhdsWithin] with ε hε using hStar ε hε Y hY
  have hfin := tendsto_nhds_unique (llhs.congr' heq) lsum
  rw [Finset.sum_ite_eq' (range (S.r + 2)) 0, if_pos (by simp)] at hfin
  exact_mod_cast hfin.symm

end Formalism.FourierDecayAlt.P.LEx1

namespace Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem cutTheta : CutTheta := by
  intro hC c σ ε h4 hε p
  choose Cc hCc using fun i => cutBound c 1 i le_rfl
  have hexp : ∀ ε₂ x : ℝ, ld p (fun y => c.sc ε₂ 1 y * th ε σ y) x =
      ∑ i ∈ range (p + 1), (p.choose i : ℝ) * ld i (c.sc ε₂ 1) x * ld (p - i) (th ε σ) x := by
    intro ε₂ x
    unfold ld
    have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => c.sc ε₂ 1 (Real.exp u)) := smoothLog_sc c ε₂ 1
    have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u => th ε σ (Real.exp u)) := thetaSmooth ε σ hε
    exact iteratedDeriv_fun_mul (hf.contDiffAt.of_le (by exact_mod_cast le_top))
      (hg.contDiffAt.of_le (by exact_mod_cast le_top))
  refine ⟨∑ i ∈ range (p + 1), (p.choose i : ℝ) * Cc i *
      (Real.exp 1 * (p - i).factorial * (4 * σ) ^ (p - i)), fun ε₂ x h2 hx => ⟨?_, ?_⟩⟩
  · rw [hexp, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_mul, Nat.abs_cast]
    have a := (hCc i ε₂ x h2 hx).1
    have b := thetaBound hC σ ε h4 hε (p - i) x hx
    calc (p.choose i : ℝ) * |ld i (c.sc ε₂ 1) x| * |ld (p - i) (th ε σ) x|
        ≤ ((p.choose i : ℝ) * Cc i) * (Real.exp 1 * (p - i).factorial * (4 * σ) ^ (p - i) * th ε σ x) :=
          mul_le_mul (mul_le_mul_of_nonneg_left a (Nat.cast_nonneg _)) b (abs_nonneg _)
            (mul_nonneg (Nat.cast_nonneg _) ((abs_nonneg _).trans a))
      _ = _ := by ring
  · intro hlt
    rw [hexp, Finset.sum_eq_single 0]
    · rw [(hCc 0 ε₂ x h2 hx).2.2 hlt]; simp
    · intro i _ hi
      rw [(hCc i ε₂ x h2 hx).2.2 hlt, if_neg hi]; simp
    · simp

end Formalism.FourierDecayAlt.P.LEx1

namespace Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem L3 (hC : E.CauchyTheta) (hCT : CutTheta) (hTS : ThetaSmooth) (hTR : ThetaRange) (B : Base) (c : Cut)
    (σ ε : ℝ) (h4 : 4 ≤ σ) (hε : 0 < ε) (p : ℕ) (h : B.Ω → ℂ) (hm : AEStronglyMeasurable h B.μ) (b : B.Ω → ℝ)
    (hb : Integrable b B.μ) (hbd : ∀ ω, th ε σ (B.G ω) * ‖h ω‖ ≤ b ω) :
    (∀ ε₂ : ℝ, 0 < ε₂ → Integrable (fun ω => (ld p (fun y => c.sc ε₂ 1 y * th ε σ y) (B.G ω) : ℂ) * h ω) B.μ) ∧
    Tendsto (fun ε₂ : ℝ => ∫ ω, (ld p (fun y => c.sc ε₂ 1 y * th ε σ y) (B.G ω) : ℂ) * h ω ∂B.μ) (𝓝[>] 0)
      (𝓝 (∫ ω, (ld p (th ε σ) (B.G ω) : ℂ) * h ω ∂B.μ)) := by
  obtain ⟨C, hCb⟩ := hCT hC c σ ε h4 hε p
  have hsm : ∀ ε₂ : ℝ, SmoothLog (fun y => c.sc ε₂ 1 y * th ε σ y) := fun ε₂ =>
    ContDiff.mul (smoothLog_sc c ε₂ 1) (hTS ε σ hε)
  have hmeas : ∀ ε₂ : ℝ, AEStronglyMeasurable
      (fun ω => (ld p (fun y => c.sc ε₂ 1 y * th ε σ y) (B.G ω) : ℂ) * h ω) B.μ := fun ε₂ =>
    ((Complex.measurable_ofReal.comp ((meas_ld p _ (hsm ε₂)).comp B.G_meas)).aestronglyMeasurable.mul hm)
  have hbound : ∀ ε₂ : ℝ, 0 < ε₂ → ∀ ω,
      ‖(ld p (fun y => c.sc ε₂ 1 y * th ε σ y) (B.G ω) : ℂ) * h ω‖ ≤ |C| * b ω := by
    intro ε₂ h2 ω
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have a := (hCb ε₂ (B.G ω) h2 (B.G_pos ω)).1
    have t0 := (hTR ε σ (B.G ω) hε (by linarith) (B.G_pos ω)).1.le
    calc _ ≤ (C * th ε σ (B.G ω)) * ‖h ω‖ := mul_le_mul_of_nonneg_right a (norm_nonneg _)
      _ = C * (th ε σ (B.G ω) * ‖h ω‖) := by ring
      _ ≤ |C| * (th ε σ (B.G ω) * ‖h ω‖) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (mul_nonneg t0 (norm_nonneg _))
      _ ≤ |C| * b ω := mul_le_mul_of_nonneg_left (hbd ω) (abs_nonneg _)
  refine ⟨fun ε₂ h2 => Integrable.mono' (hb.const_mul |C|) (hmeas ε₂) (Eventually.of_forall (hbound ε₂ h2)), ?_⟩
  refine tendsto_integral_filter_of_dominated_convergence (fun ω => |C| * b ω) (Eventually.of_forall hmeas) ?_
    (hb.const_mul _) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε₂ h2
    exact Eventually.of_forall (hbound ε₂ h2)
  · refine Eventually.of_forall fun ω => ?_
    apply tendsto_const_nhds.congr'
    have e1 : ∀ᶠ ε₂ : ℝ in 𝓝[>] 0, ε₂ < B.G ω :=
      (eventually_lt_nhds (B.G_pos ω)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, e1] with ε₂ h2 h3
    rw [(hCb ε₂ (B.G ω) h2 (B.G_pos ω)).2 h3]

theorem adj : Adj := by
  intro hC hLeib hCT hCI hTS hTR B S c σ h4 hM hW hI3 hAdj hJet hI4 hI4' hInt ε hε Y hY
  have hσ : 0 ≤ σ := by linarith
  have hd : ∀ ω k, 0 ≤ S.d Y ω k := fun ω k => (hW.2 Y hY ω k).le
  have hdw : ∀ ω i, 0 ≤ S.dw ω i := fun ω i => (hW.1 ω i).le
  have hth : ∀ ω, 0 ≤ th ε σ (B.G ω) ∧ th ε σ (B.G ω) ≤ 1 := fun ω =>
    ⟨(hTR ε σ (B.G ω) hε hσ (B.G_pos ω)).1.le, (hTR ε σ (B.G ω) hε hσ (B.G_pos ω)).2⟩
  have hds0 : S.ds Y 0 = S.gX Y := dS_zero B _ _
  have hmds : ∀ p k, Measurable fun ω => S.ds Y p ω k := fun p k => dsMeas B S hM hI4 Y hY p k
  have hmg : ∀ k, Measurable fun ω => S.gX Y ω k := by
    intro k
    have := hmds 0 k
    rwa [hds0] at this
  have hci := hCI B S σ hσ hM hW hI4 hI4' ε hε Y hY
  have hsm : ∀ ε₂ : ℝ, SmoothLog (fun y => c.sc ε₂ 1 y * th ε σ y) := fun ε₂ =>
    ContDiff.mul (smoothLog_sc c ε₂ 1) (hTS ε σ hε)

  set hL : B.Ω → ℂ := fun ω => ((|S.P Y| * LE.sq B S.dw S.X ω : ℝ) : ℂ) with hLdef
  have hsq0 : ∀ ω, 0 ≤ LE.sq B S.dw S.X ω := sq_nonneg' B _ hdw _
  have l0 := L3 hC hCT hTS hTR B c σ ε h4 hε 0 hL
    (Complex.measurable_ofReal.comp_aemeasurable (hInt.1.aemeasurable.const_mul _)).aestronglyMeasurable
    (fun ω => |S.P Y| * LE.sq B S.dw S.X ω) (hInt.const_mul _) (by
      intro ω
      rw [hLdef]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (mul_nonneg (abs_nonneg _) (hsq0 ω))]
      exact mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (hsq0 ω)) (hth ω).2)

  have lp := fun p => L3 hC hCT hTS hTR B c σ ε h4 hε p (pr B (S.d Y) (S.gX Y) (S.ds Y p))
    (meas_pr B (S.d Y) _ _ ((hM.2.2 Y hY).1) hmg (hmds p)).aestronglyMeasurable
    (fun ω => (th ε σ (B.G ω) * LE.sq B (S.d Y) (S.ds Y 0) ω / 1 + 1 * (th ε σ (B.G ω) * LE.sq B (S.d Y) (S.ds Y p) ω)) / 2)
    ((((hci 0).div_const 1).add ((hci p).const_mul 1)).div_const 2) (by
      intro ω
      have := mul_le_mul_of_nonneg_left (pr_bound B (S.d Y) hd (S.gX Y) (S.ds Y p) 1 one_pos ω) (hth ω).1
      rw [hds0]
      calc _ ≤ _ := this
        _ = _ := by ring)
  have hleft : ∀ ε₂ : ℝ, ∀ ω, pr B (fun _ _ => 1) (S.gst Y (fun ω k => (S.d Y ω k : ℂ) * S.gX Y ω k))
      (mulF B (fun y => c.sc ε₂ 1 y * th ε σ y) S.X) ω =
      (ld 0 (fun y => c.sc ε₂ 1 y * th ε σ y) (B.G ω) : ℂ) * hL ω := by
    intro ε₂ ω
    rw [ld_zero' _ _ (B.G_pos ω), hLdef]
    unfold pr LE.sq mulF
    simp_rw [hI3 Y hY ω]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have e := Complex.mul_conj' (S.X ω i)
    simp only [map_mul, Complex.conj_ofReal]
    linear_combination ((c.sc ε₂ 1 (B.G ω) : ℂ) * (th ε σ (B.G ω) : ℂ) * ((|S.P Y| : ℝ) : ℂ) * (S.dw ω i : ℂ)) * e
  have hright : ∀ ε₂ : ℝ, ∀ ω, pr B (S.d Y) (S.gX Y) (S.g Y (mulF B (fun y => c.sc ε₂ 1 y * th ε σ y) S.X)) ω =
      ∑ p ∈ range (S.r + 2), (ld p (fun y => c.sc ε₂ 1 y * th ε σ y) (B.G ω) : ℂ) *
        pr B (S.d Y) (S.gX Y) (S.ds Y p) ω / p.factorial := by
    intro ε₂ ω
    unfold pr
    simp_rw [hLeib B _ _ (S.g Y) S.X (S.r + 1) (hJet Y hY) (hI4 Y hY) _ (hsm ε₂) ω]
    simp only [map_sum, map_div₀, map_mul, Complex.conj_ofReal, map_natCast, Finset.mul_sum, Finset.sum_div]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro k _
    show _ = _ * (_ * _ * conj (dS B (S.g Y) S.X p ω k)) / _
    ring
  have heq : (fun ε₂ : ℝ => ∫ ω, (ld 0 (fun y => c.sc ε₂ 1 y * th ε σ y) (B.G ω) : ℂ) * hL ω ∂B.μ) =ᶠ[𝓝[>] 0]
      fun ε₂ : ℝ => ∑ p ∈ range (S.r + 2), (∫ ω, (ld p (fun y => c.sc ε₂ 1 y * th ε σ y) (B.G ω) : ℂ) *
        pr B (S.d Y) (S.gX Y) (S.ds Y p) ω ∂B.μ) / p.factorial := by
    filter_upwards [self_mem_nhdsWithin] with ε₂ h2
    have h := hAdj Y hY ε ε₂ hε h2
    simp_rw [hleft ε₂, hright ε₂] at h
    rw [h, integral_finset_sum _ (fun p _ => ((lp p).1 ε₂ h2).div_const _)]
    apply Finset.sum_congr rfl
    intro p _
    rw [integral_div]
  have lsum : Tendsto (fun ε₂ : ℝ => ∑ p ∈ range (S.r + 2),
      (∫ ω, (ld p (fun y => c.sc ε₂ 1 y * th ε σ y) (B.G ω) : ℂ) *
        pr B (S.d Y) (S.gX Y) (S.ds Y p) ω ∂B.μ) / p.factorial) (𝓝[>] 0)
      (𝓝 (∑ p ∈ range (S.r + 2), S.term ε σ Y p)) := by
    apply tendsto_finset_sum
    intro p _
    exact ((lp p).2).div_const _
  have hfin := tendsto_nhds_unique (l0.2.congr' heq) lsum
  rw [← hfin]
  have e3 : (fun ω => (ld 0 (th ε σ) (B.G ω) : ℂ) * hL ω) =
      fun ω => ((|S.P Y| * (th ε σ (B.G ω) * LE.sq B S.dw S.X ω) : ℝ) : ℂ) := by
    funext ω
    rw [ld_zero' _ _ (B.G_pos ω), hLdef]; push_cast; ring
  rw [e3]
  have e4 : ∫ ω, ((|S.P Y| * (th ε σ (B.G ω) * LE.sq B S.dw S.X ω) : ℝ) : ℂ) ∂B.μ =
      ((∫ ω, |S.P Y| * (th ε σ (B.G ω) * LE.sq B S.dw S.X ω) ∂B.μ : ℝ) : ℂ) := integral_ofReal
  rw [e4, integral_const_mul]
  rfl

end Formalism.FourierDecayAlt.P.LEx1

namespace Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate

theorem markovTerm : MarkovTerm := by
  intro hMV B S σ ε M hσ hε hL hM hW hI4 hI4' Y hY hEns p
  obtain ⟨c, hc⟩ := hI4 Y hY
  have hth : ∀ ω, 0 ≤ th ε σ (B.G ω) := fun ω =>
    Real.rpow_nonneg (div_nonneg (B.G_pos ω).le (by have := B.G_pos ω; linarith)) _
  have hd : ∀ ω k, 0 ≤ S.d Y ω k := fun ω k => (hW.2 Y hY ω k).le
  set wt : B.Ω → Bool × S.ι → ℝ := fun ω k => th ε σ (B.G ω) * S.d Y ω k with hwt
  have hwt0 : ∀ ω k, 0 ≤ wt ω k := fun ω k => mul_nonneg (hth ω) (hd ω k)
  have hwtm : ∀ k, Measurable fun ω => wt ω k := fun k => (meas_th B ε σ).mul ((hM.2.2 Y hY).1 k)
  have hsq : ∀ v : Fn B (Bool × S.ι), (fun ω => th ε σ (B.G ω) * LE.sq B (S.d Y) v ω) = LE.sq B wt v := by
    intro v; funext ω; unfold LE.sq; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; simp only [hwt]; ring
  have hmds : ∀ q k, Measurable fun ω => S.ds Y q ω k := fun q k => dsMeas B S hM hI4 Y hY q k
  have hci : ∀ q, Integrable (LE.sq B wt (S.ds Y q)) B.μ := fun q => by
    rw [← hsq]; exact coefIntegrable B S σ hσ hM hW hI4 hI4' ε hε Y hY q
  have hgi : ∀ s, Integrable (LE.sq B wt (S.gs Y s)) B.μ := fun s => by
    rw [← hsq]; exact (hI4' ε hε).1 Y hY s
  have hDn : S.Dn ε σ Y p = ∫ ω, LE.sq B wt (S.ds Y p) ω ∂B.μ := by unfold Step.Dn; rw [hsq]
  have hEn : ∀ s, S.Ens ε σ Y s = ∫ ω, LE.sq B wt (S.gs Y s) ω ∂B.μ := fun s => by unfold Step.Ens; rw [hsq]
  have hD0 : 0 ≤ S.Dn ε σ Y p := by rw [hDn]; exact integral_nonneg fun ω => sq_nonneg' B wt hwt0 _ ω
  have hM0 : 0 ≤ M := by
    refine le_trans ?_ (hEns 0 (by simpa using hY))
    rw [hEn]; exact integral_nonneg fun ω => sq_nonneg' B wt hwt0 _ ω
  have hK0 : 0 ≤ 2 * ((S.r : ℝ) + 1) ^ 2 / S.L := by positivity
  have hdsq : ∀ q ω k, S.ds Y q ω k = q.factorial * (if q < S.r + 1 + 1 then c q ω k else 0) :=
    fun q ω k => dS_poly B (S.g Y) S.X (S.r + 1) c hc q ω k
  by_cases hp : p < S.r + 1 + 1
  swap
  · have : S.ds Y p = fun _ _ => 0 := by funext ω k; rw [hdsq, if_neg hp]; simp
    have h0 : S.Dn ε σ Y p = 0 := by rw [hDn, this]; simp [LE.sq]
    rw [h0]; positivity
  set w : Fn B (Bool × S.ι) := S.ds Y p with hw
  let a' : ℕ → ℂ := fun q => (∫ ω, pr B wt (S.ds Y q) w ω ∂B.μ) / q.factorial
  have hpi : ∀ q, Integrable (pr B wt (S.ds Y q) w) B.μ := fun q =>
    int_pr B wt hwt0 _ _ hwtm (hmds q) (hmds p) (hci q) (hci p)
  have hphi : ∀ s : ℝ, ∫ ω, pr B wt (S.gs Y s) w ω ∂B.μ = ∑ q ∈ range (S.r + 1 + 1), (s : ℂ) ^ q * a' q := by
    intro s
    have h1 : pr B wt (S.gs Y s) w = fun ω => ∑ q ∈ range (S.r + 1 + 1),
        (s : ℂ) ^ q * (pr B wt (S.ds Y q) w ω / q.factorial) := by
      funext ω
      unfold pr
      have hgs : ∀ k, S.gs Y s ω k = ∑ q ∈ range (S.r + 1 + 1), (s : ℂ) ^ q * (S.ds Y q ω k / q.factorial) := by
        intro k
        show conjS B (S.g Y) S.X s ω k = _
        rw [hc s ω k]
        apply Finset.sum_congr rfl
        intro q hq
        rw [hdsq, if_pos (Finset.mem_range.1 hq)]
        have : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast q.factorial_ne_zero
        field_simp
      simp_rw [hgs, Finset.mul_sum, Finset.sum_mul, Finset.sum_div, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro q _
      apply Finset.sum_congr rfl; intro k _
      ring
    rw [h1, integral_finset_sum _ (fun q _ => ((hpi q).div_const _).const_mul _)]
    apply Finset.sum_congr rfl; intro q _
    rw [integral_const_mul, integral_div]
  have hbound : ∀ s : ℝ, Y + s ∈ S.J →
      ‖∫ ω, pr B wt (S.gs Y s) w ω ∂B.μ‖ ≤ √M * √(S.Dn ε σ Y p) := by
    intro s hs
    have h1 := opt_delta _ _ _ (integral_nonneg fun ω => sq_nonneg' B wt hwt0 (S.gs Y s) ω)
      (integral_nonneg fun ω => sq_nonneg' B wt hwt0 w ω)
      (fun δ hδ => norm_int_pr_le B wt hwt0 (S.gs Y s) w (hgi s) (hci p) δ hδ)
    rw [← hEn, ← hDn] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hEns s hs)) (Real.sqrt_nonneg _))
  have hfun : (fun s : ℝ => ∑ k : Fin (S.r + 1 + 1), s ^ (k : ℕ) • a' k) =
      fun s : ℝ => (mkP (S.r + 1) a').eval (s : ℂ) := by
    funext s
    rw [mkP_eval, ← Fin.sum_univ_eq_sum_range (fun q => (s : ℂ) ^ q * a' q)]
    apply Finset.sum_congr rfl; intro k _
    rw [Complex.real_smul]; push_cast; ring
  have hmk := hMV ℂ (S.r + 1) (fun k => a' k) (S.a - Y) S.L (√M * √(S.Dn ε σ Y p)) hL (by
    intro t ht
    have hs : Y + t ∈ S.J := by
      unfold Step.J; constructor <;> [linarith [ht.1]; linarith [ht.2]]
    have e : (∑ k : Fin (S.r + 1 + 1), t ^ (k : ℕ) • a' k) = (mkP (S.r + 1) a').eval (t : ℂ) := congrFun hfun t
    rw [e, mkP_eval, ← hphi t]
    exact hbound t hs) p 0 (by
      have h1 := hY.1; have h2 := hY.2
      constructor <;> linarith)
  rw [hfun, iterDeriv_poly] at hmk
  simp only [Complex.ofReal_zero] at hmk
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative, mkP_coeff, zero_add, if_pos hp] at hmk
  have hval : (p.descFactorial p) • a' p = ((S.Dn ε σ Y p : ℝ) : ℂ) := by
    rw [Nat.descFactorial_self, hDn, ← int_pr_self]
    simp only [a', nsmul_eq_mul]
    have : (p.factorial : ℂ) ≠ 0 := by exact_mod_cast p.factorial_ne_zero
    field_simp
    rfl
  rw [hval, Complex.norm_real, Real.norm_of_nonneg hD0] at hmk
  push_cast at hmk
  set x := √(S.Dn ε σ Y p) with hx
  set y := √M with hy
  set A := (2 * ((S.r : ℝ) + 1) ^ 2 / S.L) ^ p with hA
  have hx2 : x * x = S.Dn ε σ Y p := Real.mul_self_sqrt hD0
  have hy2 : y * y = M := Real.mul_self_sqrt hM0
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hA0 : 0 ≤ A := pow_nonneg hK0 p
  have hpow : (2 * ((S.r : ℝ) + 1) ^ 2 / S.L) ^ (2 * p) = A * A := by
    rw [hA, ← pow_add]; congr 1; ring
  rw [hpow, ← hx2, ← hy2]
  rw [← hx2] at hmk
  rcases hx0.eq_or_lt with h0 | h0
  · rw [← h0]; simp; positivity
  · have h3 : x ≤ A * y := by
      have : x * x ≤ (A * y) * x := by linarith
      exact le_of_mul_le_mul_right this h0
    nlinarith [mul_nonneg hA0 hy0]

end Formalism.FourierDecayAlt.P.LEx1
