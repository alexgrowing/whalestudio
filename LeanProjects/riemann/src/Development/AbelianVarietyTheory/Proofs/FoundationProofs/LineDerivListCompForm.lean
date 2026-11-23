import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeries
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonomialDerivCauchyBoundGaussianGrowth

open Filter Topology

namespace GlobalTheory.ProdThetaConj

theorem exists_ringHom_extend (R K : Type) [Field R] [Countable R] [Field K]
    (hK : Cardinal.mk K ≤ Cardinal.mk ℂ) (i : R →+* K) (j : R →+* ℂ) :
    ∃ s : K →+* ℂ, ∀ x, s (i x) = j x := by
  letI : Algebra R K := i.toAlgebra
  letI : Algebra R ℂ := j.toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R ℂ
  have hC : Cardinal.aleph0 < Cardinal.mk ℂ := by
    rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  have hct := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht
    Cardinal.mk_le_aleph0 hC
  have hle : Cardinal.mk s ≤ Cardinal.mk t :=
    le_trans (Cardinal.mk_set_le s) (hct ▸ hK)
  obtain ⟨e⟩ := (Cardinal.le_def _ _).1 hle
  have hw : AlgebraicIndependent R (((↑) : t → ℂ) ∘ e) := ht.1.comp e e.injective
  let S := Algebra.adjoin R (Set.range ((↑) : s → K))
  let φ : S →ₐ[R] ℂ :=
    (MvPolynomial.aeval (((↑) : t → ℂ) ∘ e)).comp hs.1.aevalEquiv.symm.toAlgHom
  have hφ : Function.Injective φ :=
    (algebraicIndependent_iff_injective_aeval.1 hw).comp hs.1.aevalEquiv.symm.injective
  let _ : Algebra S ℂ := φ.toRingHom.toAlgebra
  have : IsScalarTower R S ℂ := IsScalarTower.of_algebraMap_eq fun x => (φ.commutes x).symm
  have : FaithfulSMul S ℂ := (faithfulSMul_iff_algebraMap_injective S ℂ).2 hφ
  have : Algebra.IsAlgebraic S K := hs.isAlgebraic
  let ψ : K →ₐ[R] ℂ := (IsAlgClosed.lift : K →ₐ[S] ℂ).restrictScalars R
  exact ⟨ψ.toRingHom, fun x => ψ.commutes x⟩

section General

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
theorem summable_prod_half_pow : Summable fun α : σ →₀ ℕ => ∏ j, (1 / 2 : ℝ) ^ α j := by
  have h : Summable fun α : σ → ℕ => ∏ j, (1 / 2 : ℝ) ^ α j := by
    classical
    refine summable_of_sum_le (c := ∏ _j : σ, (2 : ℝ)) (fun α => by positivity) fun u => ?_
    let n : ℕ := u.sup fun α => Finset.univ.sup α
    have hsub : u ⊆ Fintype.piFinset fun _ : σ => Finset.range (n + 1) := by
      intro α hα
      rw [Fintype.mem_piFinset]
      intro j
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact (Finset.le_sup (f := α) (Finset.mem_univ j)).trans
        (Finset.le_sup (f := fun α => Finset.univ.sup α) hα)
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
    rw [← Finset.prod_univ_sum (fun _ : σ => Finset.range (n + 1)) (fun _ k => (1 / 2 : ℝ) ^ k)]
    exact Finset.prod_le_prod (fun _ _ => by positivity) fun _ _ => sum_geometric_two_le _
  exact h.comp_injective (i := fun α : σ →₀ ℕ => (α : σ → ℕ)) DFunLike.coe_injective

theorem tsum_of_entire {f : (σ → ℂ) → ℂ} (hf : Differentiable ℂ f) (c : (σ →₀ ℕ) → ℂ)
    (hc : ∀ α, (∏ j, ((α j).factorial : ℂ)) * c α = pderivIter α f 0)
    (hc' : ∀ α, c α = MvPowerSeries.coeff α (GlobalTheory.taylor f)) (z : σ → ℂ) :
    ∑' α : σ →₀ ℕ, c α * ∏ j, z j ^ α j = f z := by
  have hb : ∀ R : ℝ, 0 < R → ∃ u : (σ →₀ ℕ) → ℝ, Summable u ∧ ∀ α, ∀ w ∈ Metric.ball (0 : σ → ℂ) R,
      ‖c α * ∏ j, w j ^ α j‖ ≤ u α := by
    intro R hR
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : σ → ℂ) (2 * R)).exists_bound_of_continuousOn
      hf.continuous.continuousOn
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (Metric.mem_closedBall_self (by positivity)))
    refine ⟨fun α => C * ∏ j, (1 / 2 : ℝ) ^ α j, summable_prod_half_pow.mul_left C, fun α w hw => ?_⟩
    have h1 := norm_pderivIter_le_of_differentiable (F := f) (a := 0) (r := fun _ => 2 * R) (M := C) α
      (fun _ => by positivity) (fun _ _ => by positivity) hf (fun y hy => hC y (by
        rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by positivity)]
        intro k
        simpa using (hy k).le))
    rw [← hc, norm_mul, norm_prod, mul_div_assoc] at h1
    simp only [Complex.norm_natCast] at h1
    have h2 := le_of_mul_le_mul_left h1 (Finset.prod_pos fun k _ => by
      exact_mod_cast Nat.factorial_pos _)
    rw [norm_mul, norm_prod]
    calc ‖c α‖ * ∏ j, ‖w j ^ α j‖ ≤ (C / ∏ k, (2 * R) ^ α k) * ∏ j, R ^ α j := by
          refine mul_le_mul h2 (Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun j _ => ?_)
            (by positivity) (by positivity)
          rw [norm_pow]
          exact pow_le_pow_left₀ (norm_nonneg _)
            ((norm_le_pi_norm w j).trans (mem_ball_zero_iff.1 hw).le) _
      _ = C * ∏ j, (1 / 2 : ℝ) ^ α j := by
          rw [div_mul_eq_mul_div, mul_div_assoc, ← Finset.prod_div_distrib]
          congr 1
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [← div_pow]
          congr 1
          field_simp
  have hsum : ∀ w : σ → ℂ, Summable fun α : σ →₀ ℕ => c α * ∏ j, w j ^ α j := fun w => by
    obtain ⟨u, hu, h⟩ := hb (‖w‖ + 1) (by positivity)
    exact Summable.of_norm_bounded hu fun α => h α w (by simp)
  have hd : DifferentiableOn ℂ (fun w : σ → ℂ => ∑' α : σ →₀ ℕ, c α * ∏ j, w j ^ α j) Set.univ := by
    refine SCV.differentiableOn_tsum_of_locally_normal isOpen_univ (fun α => ?_) fun x _ => ?_
    · apply Differentiable.differentiableOn
      fun_prop
    · obtain ⟨u, hu, h⟩ := hb (‖x‖ + 1) (by positivity)
      exact ⟨_, Metric.isOpen_ball.mem_nhds (by simp), u, hu, h⟩
  have han := SCV.analyticOnNhd_of_differentiableOn isOpen_univ hd 0 (Set.mem_univ _)
  have hfa := SCV.analyticOnNhd_of_differentiable hf Set.univ 0 (Set.mem_univ _)
  have heq := (taylor_eq_iff han hfa).1 (by
    ext α
    rw [← hc']
    exact ConjSeries.coeff_taylor_of_hasSum _ han (Eventually.of_forall fun w => (hsum w).hasSum) α
      (Nat.lt_succ_self _))
  exact SCV.eqOn_of_eventuallyEq isOpen_univ isPreconnected_univ hd hf.differentiableOn
    (Set.mem_univ 0) heq (Set.mem_univ z)

end General

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped BigOperators

theorem tsum_taylor_mono (D : D7) {N N' : ℕ} {F : VC D N N' → ℂ} (hF : Differentiable ℂ F)
    (z : VC D N N') : ∑' α, Formalism.MainNotions.TaylorLogMetric.taylor D F α * mono D α z = F z := by
  let L := LinearMap.toContinuousLinearMap (GaussCauchy.curry D N N')
  have hc : coordV D = fun k => L (Pi.single k 1) := by
    funext k
    exact (GaussCauchy.curry_single D N N' k).symm
  have han := SCV.analyticOnNhd_of_differentiable hF Set.univ 0 (Set.mem_univ _)
  have h := tsum_of_entire (f := fun w => F (L w)) (hF.comp L.differentiable)
    (Formalism.MainNotions.TaylorLogMetric.taylor D F) (fun α => by
      have := GaussCauchy.factorial_mul_taylor D N N' F hF α
      rwa [Finsupp.prod_fintype _ _ (by simp)] at this)
    (fun α => by rw [ConjSeries.taylor_eq_coeff, hc, ← taylor_comp_clm L han])
    (fun k => z k.1 k.2.1 k.2.2)
  refine Eq.trans ?_ h
  refine tsum_congr fun α => ?_
  rw [mono, Finsupp.prod_fintype _ _ (by simp)]

theorem exists_endo_eq_cj (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) {S : Set ℂ} (hS : S.Countable) :
    ∃ s : ℂ →+* ℂ, ∀ x ∈ S, x ∈ M → cj M ρ x = s x := by
  let R := IntermediateField.adjoin ℚ (S ∩ (M : Set ℂ))
  have hle : R ≤ M := IntermediateField.adjoin_le_iff.2 Set.inter_subset_right
  have : Countable R := by
    have h1 : (S ∩ (M : Set ℂ)).Countable := hS.mono Set.inter_subset_left
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (IntermediateField.cardinalMk_adjoin_le ℚ _).trans ?_
    simp only [sup_le_iff, le_refl, and_true]
    exact ⟨Cardinal.mk_le_aleph0, Cardinal.le_aleph0_iff_set_countable.2 h1⟩
  obtain ⟨s, hs⟩ := exists_ringHom_extend R ℂ le_rfl R.val.toRingHom
    (ρ.comp (IntermediateField.inclusion hle)).toRingHom
  refine ⟨s, fun x hx hM => ?_⟩
  have := hs ⟨x, IntermediateField.subset_adjoin ℚ _ ⟨hx, hM⟩⟩
  simp only [cj, TaylorLogMetric.liftM, dif_pos hM]
  exact this.symm

def ConjPair (D : D7) {N N' : ℕ} (s : ℂ →+* ℂ) (F F' : VC D N N' → ℂ) : Prop :=
  Differentiable ℂ F ∧ Differentiable ℂ F' ∧
    MvPowerSeries.map s (taylorDir (coordV D) F) = taylorDir (coordV D) F'

variable {D : D7} {N N' : ℕ} {s : ℂ →+* ℂ}

theorem an0 {F : VC D N N' → ℂ} (h : Differentiable ℂ F) : AnalyticAt ℂ F 0 :=
  SCV.analyticOnNhd_of_differentiable h Set.univ 0 (Set.mem_univ _)

theorem ConjPair.taylor_eq {F F' : VC D N N' → ℂ} (h : ConjPair D s F F') (α : Mono D N N') :
    s (Formalism.MainNotions.TaylorLogMetric.taylor D F α) = Formalism.MainNotions.TaylorLogMetric.taylor D F' α := by
  rw [ConjSeries.taylor_eq_coeff, ConjSeries.taylor_eq_coeff, ← h.2.2, MvPowerSeries.coeff_map]

theorem ConjPair.fnConj_eq {F F' : VC D N N' → ℂ} (h : ConjPair D s F F')
    {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ}
    (hs : ∀ α, cj M ρ (Formalism.MainNotions.TaylorLogMetric.taylor D F α) = s (Formalism.MainNotions.TaylorLogMetric.taylor D F α)) :
    fnConj D M ρ F = F' := by
  funext z
  rw [← tsum_taylor_mono D h.2.1 z, fnConj]
  refine tsum_congr fun α => ?_
  rw [← h.taylor_eq, ← hs, cj]

theorem taylor_const_mul {F : VC D N N' → ℂ} (h : Differentiable ℂ F) (a : ℂ) (α : Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (fun z => a * F z) α = a * Formalism.MainNotions.TaylorLogMetric.taylor D F α := by
  rw [ConjSeries.taylor_eq_coeff, ConjSeries.taylor_eq_coeff]
  have := taylorDir_smul (coordV D) a (an0 h)
  rw [show (fun z => a * F z) = a • F from rfl, this, MvPowerSeries.coeff_smul]

theorem ConjPair.const_mul {F F' : VC D N N' → ℂ} (h : ConjPair D s F F') (a : ℂ) :
    ConjPair D s (fun z => a * F z) (fun z => s a * F' z) := by
  refine ⟨h.1.const_mul a, h.2.1.const_mul _, ?_⟩
  ext α
  rw [MvPowerSeries.coeff_map, ← ConjSeries.taylor_eq_coeff, ← ConjSeries.taylor_eq_coeff,
    taylor_const_mul h.1, taylor_const_mul h.2.1, map_mul, h.taylor_eq]

theorem ConjPair.sum {κ : Type*} [Fintype κ] {F F' : κ → VC D N N' → ℂ}
    (h : ∀ i, ConjPair D s (F i) (F' i)) :
    ConjPair D s (fun z => ∑ i, F i z) (fun z => ∑ i, F' i z) := by
  refine ⟨Differentiable.fun_sum fun i _ => (h i).1, Differentiable.fun_sum fun i _ => (h i).2.1, ?_⟩
  rw [taylorDir_sum _ _ fun i _ => an0 (h i).1, taylorDir_sum _ _ fun i _ => an0 (h i).2.1, map_sum]
  exact Finset.sum_congr rfl fun i _ => (h i).2.2

theorem ConjPair.prod {κ : Type*} [Fintype κ] {F F' : κ → VC D N N' → ℂ}
    (h : ∀ i, ConjPair D s (F i) (F' i)) :
    ConjPair D s (fun z => ∏ i, F i z) (fun z => ∏ i, F' i z) := by
  have hp : ∀ G : κ → VC D N N' → ℂ, (∀ i, Differentiable ℂ (G i)) →
      Differentiable ℂ fun z => ∏ i, G i z := fun G hG z =>
    (HasFDerivAt.finsetProd (u := Finset.univ) fun i _ => (hG i z).hasFDerivAt).differentiableAt
  refine ⟨hp _ fun i => (h i).1, hp _ fun i => (h i).2.1, ?_⟩
  rw [taylorDir_prod _ _ fun i _ => an0 (h i).1, taylorDir_prod _ _ fun i _ => an0 (h i).2.1, map_prod]
  exact Finset.prod_congr rfl fun i _ => (h i).2.2

theorem lineDerivList_comp_form {κ : Type*} (u : κ → VC D N N') (ℓ : VC D N N' →ₗ[ℂ] ℂ) (g : ℂ → ℂ)
    (l : List κ) : lineDerivList ℂ (l.map u) (fun z => g (ℓ z)) 0 =
      (l.map fun k => ℓ (u k)).prod * iteratedDeriv l.length g 0 := by
  rw [lineDerivList_comp_linearMap, List.map_map]
  have h1 := lineDerivList_map_smul (fun k => ℓ (u k)) (fun _ => (1 : ℂ)) l g
  have h2 := lineDerivList_replicate l.length (1 : ℂ) g 0 (0 : ℂ)
  simp only [smul_eq_mul, mul_one, List.map_const', zero_add] at h1 h2
  simp only [map_zero, Function.comp_def, h1, h2]

theorem ConjPair.comp_form {g g' : ℂ → ℂ} (hg : Differentiable ℂ g) (hg' : Differentiable ℂ g')
    (hc : ∀ n, s (coef1 g n) = coef1 g' n) (ℓ ℓ' : VC D N N' →ₗ[ℂ] ℂ)
    (hℓ : ∀ k, s (ℓ (coordV D k)) = ℓ' (coordV D k)) :
    ConjPair D s (fun z => g (ℓ z)) (fun z => g' (ℓ' z)) := by
  have h1 : Differentiable ℂ fun z => g (ℓ z) :=
    hg.comp (LinearMap.toContinuousLinearMap ℓ).differentiable
  have h2 : Differentiable ℂ fun z => g' (ℓ' z) :=
    hg'.comp (LinearMap.toContinuousLinearMap ℓ').differentiable
  refine ⟨h1, h2, ?_⟩
  ext α
  have hd : ∀ n, s (iteratedDeriv n g 0) = iteratedDeriv n g' 0 := fun n => by
    have := hc n
    rw [coef1, coef1, map_div₀, map_natCast] at this
    exact (div_left_inj' (by exact_mod_cast n.factorial_ne_zero)).1 this
  rw [MvPowerSeries.coeff_map,
    coeff_taylorDir_eq_lineDerivList _ (an0 h1) (Multiset.coe_toList _),
    coeff_taylorDir_eq_lineDerivList _ (an0 h2) (Multiset.coe_toList _),
    lineDerivList_comp_form, lineDerivList_comp_form, map_mul, map_mul, map_inv₀, map_natCast, hd,
    map_list_prod, List.map_map]
  simp only [Function.comp_def, hℓ]

end GlobalTheory.ProdThetaConj
