import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.GenPiecesK
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.ExistsFinMap
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.OpBound
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.MatrixEntryAbsSumUnitaryLieCoordinatesSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.HasSumSingle

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci
open PositivityTheory.Rg.Fx

private theorem homog_eq {ι : Type} (d : ℕ) (p : MvPolynomial ι ℂ) :
    homog d p = ∑ α ∈ p.support,
      monomial (Finsupp.single none (d - α.degree) + α.mapDomain some) (p.coeff α) := by
  unfold homog
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [rename_monomial, X_pow_eq_monomial, monomial_mul, one_mul]

private theorem deg_le {ι : Type} {d : ℕ} {p : MvPolynomial ι ℂ} (h : p.totalDegree ≤ d) {α : ι →₀ ℕ}
    (hα : α ∈ p.support) : α.degree ≤ d := by
  have := (le_totalDegree hα).trans h
  simpa [Finsupp.degree_apply, Finsupp.sum] using this

private theorem deg_exp {ι : Type} {d : ℕ} {α : ι →₀ ℕ} (h : α.degree ≤ d) :
    (Finsupp.single none (d - α.degree) + α.mapDomain some : Option ι →₀ ℕ).degree = d := by
  rw [map_add, Finsupp.degree_single, Finsupp.degree_mapDomain]
  omega

private theorem homog_deg {ι : Type} {d : ℕ} {p : MvPolynomial ι ℂ} (h : p.totalDegree ≤ d) :
    (homog d p).totalDegree ≤ d := by
  rw [homog_eq]
  refine totalDegree_finsetSum_le fun α hα => (totalDegree_monomial_le _ _).trans (le_of_eq ?_)
  have := deg_exp (deg_le h hα)
  rw [Finsupp.degree_apply] at this
  exact this

private theorem homog_eval {ι : Type} {d : ℕ} {p : MvPolynomial ι ℂ} (h : p.totalDegree ≤ d) (x : ℂ) (g : ι → ℂ) :
    eval (fun o : Option ι => o.elim x fun y => x * g y) (homog d p) = x ^ d * eval g p := by
  unfold homog
  conv_rhs => rw [p.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hd := deg_le h hα
  rw [map_mul, map_pow, eval_X, eval_rename, eval_monomial, eval_monomial]
  have e : (α.prod fun n e => ((fun o : Option ι => o.elim x fun y => x * g y) ∘ some) n ^ e)
      = x ^ α.degree * α.prod fun n e => g n ^ e := by
    simp only [Function.comp, Option.elim, mul_pow, Finsupp.prod, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
  rw [e]
  have : x ^ d = x ^ (d - α.degree) * x ^ α.degree := by rw [← pow_add]; congr 1; omega
  rw [this]
  simp only [Option.elim]
  ring

private theorem mon_norm {σ : Type} [Fintype σ] {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (ψ : MvPolynomial σ ℂ →+* (H →L[ℂ] H)) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ m : σ →₀ ℕ, ‖ψ (monomial m 1)‖ ≤ D ^ m.degree := by
  have h0 : 0 ≤ ∑ i, ‖ψ (X i)‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨1 + ∑ i, ‖ψ (X i)‖, by linarith, fun m => ?_⟩
  have h1 : ‖(1 : H →L[ℂ] H)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  induction m using Finsupp.induction_linear with
  | zero => simpa using h1
  | add a b ha hb =>
    have : (monomial (a + b) 1 : MvPolynomial σ ℂ) = monomial a 1 * monomial b 1 := by
      rw [monomial_mul, one_mul]
    rw [this, map_mul, map_add, pow_add]
    exact (norm_mul_le _ _).trans (mul_le_mul ha hb (norm_nonneg _) (by positivity))
  | single i e =>
    rw [← X_pow_eq_monomial, map_pow, Finsupp.degree_single]
    have hi : ‖ψ (X i)‖ ≤ 1 + ∑ i, ‖ψ (X i)‖ := by
      have := Finset.single_le_sum (f := fun i => ‖ψ (X i)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
      linarith
    induction e with
    | zero => simpa using h1
    | succ e ih =>
      rw [pow_succ, pow_succ]
      exact (norm_mul_le _ _).trans (mul_le_mul ih hi (norm_nonneg _) (by positivity))

private theorem homog_norm {ι : Type} [Fintype ι] {H : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (ψ : MvPolynomial (Option ι) ℂ →+* (H →L[ℂ] H)) (hψ : ∀ c : ℂ, ψ (C c) = c • 1) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (d : ℕ) (p : MvPolynomial ι ℂ), p.totalDegree ≤ d → ‖ψ (homog d p)‖ ≤ l1 p * D ^ d := by
  obtain ⟨D, hD, h⟩ := mon_norm ψ
  refine ⟨D, hD, fun d p hp => ?_⟩
  rw [homog_eq, map_sum, l1, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α hα => ?_)
  rw [← mul_one (p.coeff α), ← C_mul_monomial, map_mul, hψ, smul_mul_assoc, one_mul, norm_smul, mul_one]
  refine mul_le_mul_of_nonneg_left ((h _).trans (le_of_eq ?_)) (norm_nonneg _)
  rw [deg_exp (deg_le hp hα)]

private theorem trunc_eq {K : Type} [Field K] [NumberField K] {n : ℕ} (d : ℕ)
    (G : ℕ → MvPolynomial (Pl K × Fin n) (MvPolynomial (Ix K n) ℂ)) (s : Finset ((Pl K × Fin n) →₀ ℕ))
    (h : ∀ k, (G k).support ⊆ s) :
    trunc d G = ∑ β ∈ s, monomial β (∑ k ∈ Finset.range (d + 1), homog d ((G k).coeff β)) := by
  unfold trunc
  simp only [map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_subset (h k) fun β _ hβ => ?_
  rw [notMem_support_iff.mp hβ]
  simp [homog]

private theorem eval_blockE {K : Type} [Field K] [NumberField K] {n : ℕ} (L : Ix K n → ℂ)
    (p : MvPolynomial (Ix K n) ℂ) :
    eval L (aeval blockE p) = eval (fun y : Ix K n => (msOf L y.1).esymm (y.2 + 1)) p := by
  have e : ∀ y : Ix K n, eval L (blockE y) = (msOf L y.1).esymm (y.2 + 1) := by
    intro y
    rw [blockE, eval_rename, ← coe_aeval_eq_eval]
    exact aeval_esymm_eq_multiset_esymm (Fin n) ℂ _ _
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, aeval_X, eval_X, e]

theorem UpperTheory.ConvolutionTheory.Ci.truncSpec :
    TruncSpec := by
  intro K _ _ n S Φ hΦ
  classical
  obtain ⟨K₀, G₀, hG₀⟩ := UpperTheory.ConvolutionTheory.FX.gen_piecesK (K →+* ℂ) (Pl K × Fin n) n Φ (by
    intro w
    convert hΦ.1 w)
  refine ⟨⟨G₀, fun k => (hG₀ k).1⟩, fun G hG => ?_⟩
  have hGG : G = G₀ := by
    funext k
    refine map_injective _ (UpperTheory.ConvolutionTheory.FX.blockE_inj (K →+* ℂ) n) ?_
    exact (hG k).trans (hG₀ k).1.symm
  subst hGG
  have hs : ∀ k, (G k).support ⊆ Φ.support := fun k => (hG₀ k).2.1
  have hdeg : ∀ d β, ∀ k ∈ Finset.range (d + 1), ((G k).coeff β).totalDegree ≤ d := fun d β k hk =>
    ((hG₀ k).2.2 β).1.trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have hT := fun d => trunc_eq d G Φ.support hs
  refine ⟨⟨Φ.vars.image Prod.fst, Φ.totalDegree, ?_, fun d => ?_⟩, fun L t => ?_, fun H _ _ _ ev hev => ?_⟩
  · intro w hw
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
    exact hΦ.2 x hx
  · have hsup : (trunc d G).support ⊆ Φ.support := by
      rw [hT]
      refine support_sum.trans (Finset.biUnion_subset.mpr fun β hβ => support_monomial_subset.trans ?_)
      simpa using hβ
    refine ⟨fun x hx => ?_, Finset.sup_mono hsup, fun β => ?_⟩
    · obtain ⟨m, hm, hx⟩ := (mem_vars_iff_mem_support x).mp hx
      exact Finset.mem_image_of_mem _ ((mem_vars_iff_mem_support x).mpr ⟨m, hsup hm, hx⟩)
    · rw [hT, coeff_sum]
      refine totalDegree_finsetSum_le fun γ _ => ?_
      rw [coeff_monomial]
      split_ifs
      · exact totalDegree_finsetSum_le fun k hk => homog_deg (hdeg d γ k hk)
      · simp
  · have hc : ∀ k, ∀ β ∈ Φ.support, eval (fun y : Ix K n => (msOf L y.1).esymm (y.2 + 1)) ((G k).coeff β)
        = eval L (piece k (Φ.coeff β)) := by
      intro k β hβ
      rw [← eval_blockE]
      congr 1
      have := congrArg (coeff β) (hG k)
      rw [coeff_map, pieceK, coeff_sum] at this
      simp only [coeff_monomial, Finset.sum_ite_eq', if_pos hβ] at this
      exact this
    refine ⟨fun d => ∑ β ∈ Φ.support, (∑ k ∈ Finset.range (d + 1), eval L (piece k (Φ.coeff β))) *
      β.prod fun i e => hval t i ^ e, ?_, fun x d => ?_⟩
    · have : evK L (hval t) Φ = ∑ β ∈ Φ.support, PositivityTheory.Rg.Fx.ev L (Φ.coeff β) * β.prod fun i e => hval t i ^ e := by
        conv_lhs => rw [Φ.as_sum]
        rw [map_sum]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [evK, eval₂Hom_monomial]
      rw [this]
      refine tendsto_finsetSum _ fun β _ => Tendsto.mul_const _ ?_
      exact (UpperTheory.ConvolutionTheory.FX.piece_sum _ (Φ.coeff β) L).tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    · rw [hT, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun β hβ => ?_
      rw [val, eval₂Hom_monomial, map_sum, ← mul_assoc, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [← hc k β hβ]
      exact homog_eval (hdeg d β k hk) _ _
  · obtain ⟨D, hD, hb⟩ := homog_norm (ev.comp C) hev
    set A : ℝ := ∑ β ∈ Φ.support, ‖ev (monomial β 1)‖ with hA
    have hA0 : 0 ≤ A := Finset.sum_nonneg fun _ _ => norm_nonneg _
    set E : ℝ := |K₀| + 1 with hE
    have hE1 : 1 ≤ E := by have := abs_nonneg K₀; linarith
    refine ⟨(A + 1) * 2 * E * D, fun d => ?_⟩
    have h1 : ∀ β, ‖ev (C (∑ k ∈ Finset.range (d + 1), homog d ((G k).coeff β)))‖
        ≤ 2 ^ (d + 1) * E ^ (d + 1) * D ^ (d + 1) := by
      intro β
      rw [map_sum, map_sum]
      refine (norm_sum_le _ _).trans ?_
      have h2 : ∀ k ∈ Finset.range (d + 1), ‖ev (C (homog d ((G k).coeff β)))‖ ≤ E ^ (d + 1) * D ^ (d + 1) := by
        intro k hk
        refine (hb d _ (hdeg d β k hk)).trans (mul_le_mul ?_ (pow_le_pow_right₀ hD (Nat.le_succ d))
          (by positivity) (by positivity))
        refine ((hG₀ k).2.2 β).2.trans ?_
        have h3 : K₀ ^ (k + 1) ≤ E ^ (k + 1) :=
          (le_abs_self _).trans (by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (by linarith) _)
        have h4 : E ^ (k + 1) ≤ E ^ (d + 1) :=
          pow_le_pow_right₀ hE1 (by have := Finset.mem_range.mp hk; omega)
        have h5 : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
        calc K₀ ^ (k + 1) / k.factorial ≤ E ^ (d + 1) / k.factorial := by gcongr; linarith
          _ ≤ E ^ (d + 1) := div_le_self (by positivity) h5
      refine (Finset.sum_le_card_nsmul _ _ _ h2).trans ?_
      rw [Finset.card_range, nsmul_eq_mul, mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact_mod_cast (Nat.lt_two_pow_self (n := d + 1)).le
    rw [hT, map_sum]
    refine (norm_sum_le _ _).trans ?_
    have h6 : ∀ β ∈ Φ.support, ‖ev (monomial β (∑ k ∈ Finset.range (d + 1), homog d ((G k).coeff β)))‖
        ≤ 2 ^ (d + 1) * E ^ (d + 1) * D ^ (d + 1) * ‖ev (monomial β 1)‖ := by
      intro β _
      rw [← mul_one (∑ k ∈ Finset.range (d + 1), homog d ((G k).coeff β)), ← C_mul_monomial, map_mul]
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (h1 β) (norm_nonneg _))
    refine (Finset.sum_le_sum h6).trans ?_
    rw [← Finset.mul_sum, ← hA, mul_pow, mul_pow, mul_pow]
    have h7 : A ≤ (A + 1) ^ (d + 1) :=
      (by linarith : A ≤ A + 1).trans (le_self_pow₀ (by linarith) (Nat.succ_ne_zero d))
    calc 2 ^ (d + 1) * E ^ (d + 1) * D ^ (d + 1) * A ≤ 2 ^ (d + 1) * E ^ (d + 1) * D ^ (d + 1) * (A + 1) ^ (d + 1) := by
          gcongr
      _ = _ := by ring
