import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropASt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.RCauchy
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContDiffOfDifferentiableFd

namespace ReciprocityTheory.ChartRestriction.G.I2

section

open Complex

noncomputable section

theorem cab_dirCauchy {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (F : V → ℂ) (hF : Differentiable ℂ F) (c : ℕ) (x : Fin c → V) (hx : ∀ k, ‖x k‖ ≤ 1)
    (ρ M : ℝ) (hρ : 0 < ρ) (hM : ∀ v, ‖v‖ ≤ c * ρ → ‖F v‖ ≤ M) :
    ‖iteratedFDeriv ℂ c F 0 x‖ ≤ M / ρ ^ c := by
  let T : (Fin c → ℂ) →L[ℂ] V := ∑ k, (ContinuousLinearMap.proj k).smulRight (x k)
  have hT : ∀ z, T z = ∑ k, z k • x k := by
    intro z; simp [T]
  have hG : Differentiable ℂ (F ∘ T) := hF.comp T.differentiable
  have h1 := iter_step_bound (F ∘ T) hG ρ M hρ c id 0 (by
    intro y hy
    simp only [Pi.zero_apply, sub_zero] at hy
    apply hM
    rw [hT]
    calc ‖∑ k, y k • x k‖ ≤ ∑ k, ‖y k • x k‖ := norm_sum_le _ _
      _ ≤ ∑ k, ‖y k‖ := by
          apply Finset.sum_le_sum; intro k _
          rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) (hx k)
      _ ≤ c * ρ := hy)
  have hcd : ContDiff ℂ c F := contDiff_of_differentiable_fd hF c
  rw [T.iteratedFDeriv_comp_right hcd 0 le_rfl] at h1
  have hx' : (fun j : Fin c => T (Pi.single j 1)) = x := by
    funext j; rw [hT]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero, hx'] using h1

theorem cab_iter_pow {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (ℓ : V →L[ℂ] ℂ) (c : ℕ) (x : Fin c → V) :
    iteratedFDeriv ℂ c (fun v => (ℓ v) ^ c) 0 x = (c.factorial : ℂ) * ∏ k, ℓ (x k) := by
  let f := (ContinuousMultilinearMap.mkPiAlgebra ℂ (Fin c) ℂ).compContinuousLinearMap (fun _ => ℓ)
  have hf : (fun v => (ℓ v) ^ c) = fun v => f (fun _ => v) := by
    funext v; simp [f, ContinuousMultilinearMap.mkPiAlgebra_apply, Finset.prod_const]
  rw [hf, ContinuousMultilinearMap.iteratedFDeriv_comp_diagonal]
  simp only [f, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply]
  have : ∀ σ : Equiv.Perm (Fin c), ∏ i, ℓ (x (σ i)) = ∏ k, ℓ (x k) := fun σ =>
    Equiv.prod_comp σ (fun k => ℓ (x k))
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    nsmul_eq_mul]

theorem cab_perm_of_ofFn {ι : Type} [Fintype ι] {n : ℕ} (f g : Fin n → ι)
    (h : List.Perm (List.ofFn f) (List.ofFn g)) : ∃ σ : Equiv.Perm (Fin n), g = f ∘ σ := by
  classical
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  have h1 : f ∘ Tuple.sort f = g ∘ Tuple.sort g := by
    apply List.ofFn_injective
    exact (((Tuple.sort f).ofFn_comp_perm f).trans
      (h.trans ((Tuple.sort g).ofFn_comp_perm g).symm)).eq_of_pairwise'
        (Tuple.monotone_sort f).sortedLE_ofFn.pairwise (Tuple.monotone_sort g).sortedLE_ofFn.pairwise
  refine ⟨(Tuple.sort g).symm.trans (Tuple.sort f), ?_⟩
  funext i
  have := congrFun h1 ((Tuple.sort g).symm i)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
  simp [this]

theorem cab_iter_cast {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] (F : W → ℂ) (z : W)
    {n n' : ℕ} (h : n = n') (v : Fin n → W) :
    iteratedFDeriv ℂ n F z v = iteratedFDeriv ℂ n' F z (v ∘ Fin.cast h.symm) := by
  subst h; rfl

theorem cab_jet_eq {ι : Type} [Fintype ι] [DecidableEq ι] {c : ℕ} {β P : EuclideanSpace ℂ ι → ℂ}
    (hβ : ContDiff ℂ (⊤ : WithTop ℕ∞) β) (hP : ContDiff ℂ (⊤ : WithTop ℕ∞) P)
    (h : ∀ α : ι →₀ ℕ, α.degree ≤ c →
      polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1) β 0 =
        polyDeriv (MvPolynomial.monomial α 1) (fun i => EuclideanSpace.single i 1) P 0) :
    iteratedFDeriv ℂ c β 0 = iteratedFDeriv ℂ c P 0 := by
  have hbasis : ∀ l : Fin c → ι, iteratedFDeriv ℂ c β 0 (fun k => EuclideanSpace.single (l k) 1) =
      iteratedFDeriv ℂ c P 0 (fun k => EuclideanSpace.single (l k) 1) := by
    intro l
    set m : Multiset ι := (List.ofFn l : Multiset ι) with hm
    set α := Multiset.toFinsupp m with hα
    have hαm : Finsupp.toMultiset α = m := Multiset.toFinsupp_toMultiset m
    have hn : Multiset.card (Finsupp.toMultiset α) = c := by
      rw [hαm, hm, Multiset.coe_card, List.length_ofFn]
    have hdeg : α.degree ≤ c := by
      have : Multiset.card (Finsupp.toMultiset α) = α.degree := by
        simp only [Finsupp.card_toMultiset]
        rfl
      omega
    have h1 := h α hdeg
    unfold polyDeriv at h1
    simp only [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_true, one_mul] at h1
    rw [cab_iter_cast β 0 hn, cab_iter_cast P 0 hn] at h1
    set g : Fin c → ι := fun k => (Finsupp.toMultiset α).toList.get
      ((Fin.cast hn.symm k).cast (Multiset.length_toList _).symm) with hg
    have hperm : List.Perm (List.ofFn l) (List.ofFn g) := by
      have e1 : List.ofFn g = (Finsupp.toMultiset α).toList := by
        apply List.ext_get (by simp [hn])
        intro k h1 h2; simp [hg]
      rw [e1, ← Multiset.coe_eq_coe, Multiset.coe_toList, hαm]
    obtain ⟨σ, hσ⟩ := cab_perm_of_ofFn l g hperm
    have hv : ((fun k => EuclideanSpace.single
        ((Finsupp.toMultiset α).toList.get (k.cast (Multiset.length_toList _).symm)) (1 : ℂ)) ∘
          Fin.cast hn.symm) = (fun k => EuclideanSpace.single (l k) (1 : ℂ)) ∘ σ := by
      funext k
      have := congrFun hσ k
      simp only [Function.comp_apply] at this ⊢
      rw [← this]
    rw [hv, (hβ.contDiffAt).iteratedFDeriv_comp_perm, (hP.contDiffAt).iteratedFDeriv_comp_perm] at h1
    simpa using h1
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear (fun _ => (EuclideanSpace.basisFun ι ℂ).toBasis)
  intro l
  simpa [EuclideanSpace.basisFun_apply] using hbasis l

end

end

section

noncomputable section

theorem cab_contDiff_top {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    {F : W → ℂ} (hF : Differentiable ℂ F) : ContDiff ℂ (⊤ : WithTop ℕ∞) F := by
  let e : W ≃L[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    (Module.finBasis ℂ W).equivFun.toContinuousLinearEquiv
  have h1 : Differentiable ℂ (F ∘ e.symm) := hF.comp e.symm.differentiable
  have h3 : ContDiff ℂ (⊤ : WithTop ℕ∞) (F ∘ e.symm) := contDiff_of_differentiable h1
  have : F = (F ∘ e.symm) ∘ e := by ext x; simp
  rw [this]
  exact h3.comp e.contDiff

theorem cab_restrict {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (Sb : Submodule ℂ V)
    {c : ℕ} {f g : V → ℂ} (hf : ContDiff ℂ c f) (hg : ContDiff ℂ c g) (hfg : ∀ v ∈ Sb, f v = g v)
    (x : Fin c → V) (hx : ∀ k, x k ∈ Sb) :
    iteratedFDeriv ℂ c f 0 x = iteratedFDeriv ℂ c g 0 x := by
  let ι : Sb →L[ℂ] V := Sb.subtypeL
  have hfi : f ∘ ι = g ∘ ι := by funext v; exact hfg v v.2
  have e1 := ι.iteratedFDeriv_comp_right hf (0 : Sb) le_rfl
  have e2 := ι.iteratedFDeriv_comp_right hg (0 : Sb) le_rfl
  rw [hfi, e2] at e1
  have := congrArg (fun M => M (fun k => (⟨x k, hx k⟩ : Sb))) e1
  simpa [ι, ContinuousMultilinearMap.compContinuousLinearMap_apply] using this.symm

theorem iteratedFDeriv_single_column {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {c : ℕ} {g : V → ℂ}
    (hg : ContDiff ℂ c g) (x : Fin c → V) :
    iteratedFDeriv ℂ c (fun w : Fin 1 → V => g (w 0)) 0 (fun k _ => x k) = iteratedFDeriv ℂ c g 0 x := by
  let pr : (Fin 1 → V) →L[ℂ] V := ContinuousLinearMap.proj 0
  have := pr.iteratedFDeriv_comp_right hg (0 : Fin 1 → V) le_rfl
  have h2 := congrArg (fun M => M (fun k _ => x k)) this
  simp only [pr, ContinuousMultilinearMap.compContinuousLinearMap_apply] at h2
  exact h2

end

end

section

noncomputable section

theorem cab_expo_le {q t u c : ℝ} (hq : 0 < q) (hqt : q * t ^ 2 ≤ c) :
    q * Real.pi * t ^ 2 / 2 - q * Real.pi * u ^ 2 + 2 * q * Real.pi * t * u ≤
      5 * Real.pi * c / 2 - Real.pi / 2 * q * u ^ 2 := by
  have h1 : 0 ≤ q * (u - 2 * t) ^ 2 := by positivity
  have hp := Real.pi_pos
  nlinarith [mul_nonneg hp.le h1]

theorem cab_tail_deriv {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    {κ : Type} (R : V → ℂ) (hR : Differentiable ℂ R) (c : ℕ) (x : Fin c → V) (hx : ∀ k, ‖x k‖ ≤ 1)
    (q : ℝ) (hq : 0 < q) (B : ℝ) (hB : 0 ≤ B) (u : κ → ℝ)
    (hsum : Summable (fun a => Real.exp (-(Real.pi / 2 * q * u a ^ 2))))
    (hbd : ∀ v, ‖R v‖ ≤ B * ∑' a, Real.exp (q * Real.pi * ‖v‖ ^ 2 / 2 - q * Real.pi * u a ^ 2 +
      2 * q * Real.pi * ‖v‖ * u a)) :
    ‖iteratedFDeriv ℂ c R 0 x‖ ≤ B * (q * (c + 1)) ^ ((c : ℝ) / 2) *
      Real.exp (5 * Real.pi * c / 2) * ∑' a, Real.exp (-(Real.pi / 2 * q * u a ^ 2)) := by
  have hc1 : (0 : ℝ) < c + 1 := by positivity
  have hqc : 0 < q * (c + 1) := mul_pos hq hc1
  set ρ := 1 / Real.sqrt (q * (c + 1)) with hρ
  have hρ0 : 0 < ρ := by positivity
  set S0 := ∑' a, Real.exp (-(Real.pi / 2 * q * u a ^ 2)) with hS0
  have hS0 : 0 ≤ S0 := tsum_nonneg fun a => (Real.exp_pos _).le
  have hM : ∀ v, ‖v‖ ≤ c * ρ → ‖R v‖ ≤ B * Real.exp (5 * Real.pi * c / 2) * S0 := by
    intro v hv
    have hqt : q * ‖v‖ ^ 2 ≤ c := by
      have h1 : ‖v‖ ^ 2 ≤ (c * ρ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv 2
      have h2 : (c * ρ) ^ 2 = c ^ 2 / (q * (c + 1)) := by
        rw [hρ, mul_pow, div_pow, Real.sq_sqrt hqc.le]; ring
      rw [h2] at h1
      have h3 : q * ‖v‖ ^ 2 ≤ c ^ 2 / (c + 1) := by
        calc q * ‖v‖ ^ 2 ≤ q * (c ^ 2 / (q * (c + 1))) := mul_le_mul_of_nonneg_left h1 hq.le
          _ = c ^ 2 / (c + 1) := by field_simp
      refine h3.trans ?_
      rw [div_le_iff₀ hc1]; nlinarith
    have hterm : ∀ a, Real.exp (q * Real.pi * ‖v‖ ^ 2 / 2 - q * Real.pi * u a ^ 2 +
        2 * q * Real.pi * ‖v‖ * u a) ≤
        Real.exp (5 * Real.pi * c / 2) * Real.exp (-(Real.pi / 2 * q * u a ^ 2)) := by
      intro a
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have := cab_expo_le (u := u a) hq hqt
      linarith
    have hs2 : Summable (fun a => Real.exp (5 * Real.pi * c / 2) * Real.exp (-(Real.pi / 2 * q * u a ^ 2))) :=
      hsum.mul_left _
    have hs1 : Summable (fun a => Real.exp (q * Real.pi * ‖v‖ ^ 2 / 2 - q * Real.pi * u a ^ 2 +
        2 * q * Real.pi * ‖v‖ * u a)) :=
      Summable.of_nonneg_of_le (fun a => (Real.exp_pos _).le) hterm hs2
    refine (hbd v).trans (le_of_le_of_eq (mul_le_mul_of_nonneg_left ?_ hB) (mul_assoc _ _ _).symm)
    calc _ ≤ ∑' a, Real.exp (5 * Real.pi * c / 2) * Real.exp (-(Real.pi / 2 * q * u a ^ 2)) :=
          hs1.tsum_le_tsum hterm hs2
      _ = _ := by rw [tsum_mul_left]
  have h := cab_dirCauchy R hR c x hx ρ _ hρ0 hM
  refine h.trans (le_of_eq ?_)
  have hr : 1 / ρ ^ c = (q * (c + 1)) ^ ((c : ℝ) / 2) := by
    rw [hρ, one_div_pow, one_div_one_div, Real.sqrt_eq_rpow, ← Real.rpow_natCast,
      ← Real.rpow_mul hqc.le]
    ring_nf
  rw [div_eq_mul_one_div, hr]; ring

end

end

end ReciprocityTheory.ChartRestriction.G.I2
