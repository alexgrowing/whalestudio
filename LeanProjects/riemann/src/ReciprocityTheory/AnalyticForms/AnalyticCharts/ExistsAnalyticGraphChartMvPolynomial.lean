import Mathlib

namespace ReciprocityTheory.AnForm

open Function

theorem exists_perm_coord_complement {e c : ℕ} (A : (Fin (e + c) → ℂ) →ₗ[ℂ] (Fin c → ℂ))
    (hA : Surjective A) :
    ∃ σ : Equiv.Perm (Fin (e + c)),
      ∀ v, (∀ i : Fin e, v (σ (Fin.castAdd c i)) = 0) → A v = 0 → v = 0 := by
  classical
  set col : Fin (e + c) → (Fin c → ℂ) := fun j => A (Pi.single j 1)
  have hexp : ∀ v : Fin (e + c) → ℂ, A v = ∑ j, v j • col j := by
    intro v
    have : v = ∑ j, v j • (Pi.single j 1 : Fin (e + c) → ℂ) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [this]
    simp [col, map_sum, map_smul]
  have hspan : Submodule.span ℂ (Set.range col) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨v, rfl⟩ := hA y
    rw [hexp]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' ℂ col
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have hsp' : Submodule.span ℂ (Set.range (col ∘ a)) = ⊤ := hsp.trans hspan
  let b : Module.Basis κ ℂ (Fin c → ℂ) := Module.Basis.mk hli (by rw [hsp'])
  have hκ : Fintype.card κ = c := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fin_fun]
  let q : Fin (e + c) → Prop := fun j => j ∈ Set.range a
  let eT : Fin c ≃ {j // q j} :=
    (Fintype.equivFinOfCardEq hκ).symm.trans (Equiv.ofInjective a ha)
  have hcard : Fintype.card {j // ¬ q j} = e := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, ← Fintype.card_congr eT, Fintype.card_fin]
    omega
  let eC : Fin e ≃ {j // ¬ q j} := (Fintype.equivFinOfCardEq hcard).symm
  let σ : Equiv.Perm (Fin (e + c)) :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr eC eT).trans
      ((Equiv.sumComm _ _).trans (Equiv.sumCompl q)))
  refine ⟨σ, fun v hv hAv => ?_⟩
  have hσ : ∀ i, σ (Fin.castAdd c i) = (eC i).1 := by
    intro i; simp [σ]
  have hoff : ∀ j, ¬ q j → v j = 0 := by
    intro j hj
    have := hv (eC.symm ⟨j, hj⟩)
    rwa [hσ, Equiv.apply_symm_apply] at this
  have hsum : ∑ k, v (a k) • (col ∘ a) k = 0 := by
    rw [← hAv, hexp]
    show ∑ k, v (a k) • col (a k) = _
    rw [← Finset.sum_image (s := Finset.univ) (g := a) (f := fun j => v j • col j)
      (fun x _ y _ h => ha h)]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have : ¬ q j := by
      rintro ⟨k, rfl⟩; exact hj (Finset.mem_image_of_mem _ (Finset.mem_univ k))
    simp [hoff j this]
  have hzero := (Fintype.linearIndependent_iff.mp hli) (fun k => v (a k)) hsum
  funext j
  by_cases hj : q j
  · obtain ⟨k, rfl⟩ := hj; simpa using hzero k
  · simpa using hoff j hj

theorem exists_analytic_graph_chart {e c : ℕ} (f : (Fin (e + c) → ℂ) → (Fin c → ℂ))
    (p : Fin (e + c) → ℂ) (hp : f p = 0) (hf : AnalyticAt ℂ f p)
    (hsurj : Function.Surjective (fderiv ℂ f p)) :
    ∃ (σ : Equiv.Perm (Fin (e + c))) (U : Set (Fin (e + c) → ℂ)) (V : Set (Fin e → ℂ))
      (g : (Fin e → ℂ) → (Fin (e + c) → ℂ)),
      IsOpen U ∧ p ∈ U ∧ IsOpen V ∧ AnalyticOnNhd ℂ g V ∧
      Set.BijOn g V {x | x ∈ U ∧ f x = 0} ∧
      ∀ w ∈ V, (fun i => g w (σ (Fin.castAdd c i))) = w := by
  classical
  set A := fderiv ℂ f p with hAdef
  obtain ⟨σ, hσ⟩ := exists_perm_coord_complement (A : (Fin (e + c) → ℂ) →ₗ[ℂ] (Fin c → ℂ)) hsurj
  let Pr : (Fin (e + c) → ℂ) →L[ℂ] (Fin e → ℂ) :=
    ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (σ (Fin.castAdd c i))
  have hPr : ∀ x, Pr x = fun i => x (σ (Fin.castAdd c i)) := fun x => rfl
  let Lm : (Fin (e + c) → ℂ) →L[ℂ] (Fin e → ℂ) × (Fin c → ℂ) := Pr.prod A
  have hinj : Injective Lm := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    have h1 : Pr v = 0 := congrArg Prod.fst hv
    have h2 : A v = 0 := congrArg Prod.snd hv
    exact hσ v (fun i => by simpa [hPr] using congrFun h1 i) h2
  have hsurjL : Surjective Lm := by
    have hdim : Module.finrank ℂ (Fin (e + c) → ℂ) =
        Module.finrank ℂ ((Fin e → ℂ) × (Fin c → ℂ)) := by
      simp [Module.finrank_prod]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (Lm : (Fin (e + c) → ℂ) →ₗ[ℂ] (Fin e → ℂ) × (Fin c → ℂ)))).mp hinj
  let Le := ContinuousLinearEquiv.ofBijective Lm (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurjL)
  have hLe : (Le : (Fin (e + c) → ℂ) →L[ℂ] (Fin e → ℂ) × (Fin c → ℂ)) = Lm :=
    ContinuousLinearEquiv.coe_ofBijective _ _ _
  let φ : (Fin (e + c) → ℂ) → (Fin e → ℂ) × (Fin c → ℂ) := fun x => (Pr x, f x)
  have hφ : HasStrictFDerivAt φ (Le : (Fin (e + c) → ℂ) →L[ℂ] (Fin e → ℂ) × (Fin c → ℂ)) p := by
    rw [hLe]; exact Pr.hasStrictFDerivAt.prodMk hf.hasStrictFDerivAt
  let Φ := hφ.toOpenPartialHomeomorph φ
  have hΦ : ∀ x, Φ x = (Pr x, f x) := fun x => rfl
  have hpS : p ∈ Φ.source := hφ.mem_toOpenPartialHomeomorph_source
  have hφan : AnalyticAt ℂ Φ p := (Pr.analyticAt p).prod hf
  have hsymm : AnalyticAt ℂ Φ.symm (Φ p) :=
    Φ.analyticAt_symm' (i := Le) hpS hφan hφ.hasFDerivAt.fderiv
  obtain ⟨s, hs, hsan⟩ := hsymm.exists_mem_nhds_analyticOnNhd
  obtain ⟨T0, hT0s, hT0o, hT0p⟩ := mem_nhds_iff.mp hs
  refine ⟨σ, Φ.source ∩ Φ ⁻¹' T0, {w | (w, (0 : Fin c → ℂ)) ∈ Φ.target ∩ T0},
    fun w => Φ.symm (w, 0), ?_, ⟨hpS, hT0p⟩, ?_, ?_, ?_, ?_⟩
  · exact Φ.continuousOn.isOpen_inter_preimage Φ.open_source hT0o
  · exact (Φ.open_target.inter hT0o).preimage (continuous_id.prodMk continuous_const)
  · intro w hw
    have h1 : AnalyticAt ℂ (fun w : Fin e → ℂ => (w, (0 : Fin c → ℂ))) w :=
      analyticAt_id.prod analyticAt_const
    exact AnalyticAt.comp (f := fun w : Fin e → ℂ => (w, (0 : Fin c → ℂ))) (hsan _ (hT0s hw.2)) h1
  · refine ⟨?_, ?_, ?_⟩
    · intro w hw
      have hr := Φ.right_inv hw.1
      refine ⟨⟨Φ.map_target hw.1, ?_⟩, ?_⟩
      · show Φ (Φ.symm (w, 0)) ∈ T0
        rw [hr]; exact hw.2
      · have := congrArg Prod.snd hr
        rwa [hΦ] at this
    · intro w hw w' hw' h
      have h2 : Φ (Φ.symm (w, 0)) = Φ (Φ.symm (w', 0)) := by
        simp only at h; rw [h]
      rw [Φ.right_inv hw.1, Φ.right_inv hw'.1] at h2
      exact congrArg Prod.fst h2
    · rintro x ⟨⟨hxS, hxT⟩, hx0⟩
      have hx : Φ x = (Pr x, 0) := by rw [hΦ, hx0]
      refine ⟨Pr x, ⟨?_, ?_⟩, ?_⟩
      · rw [← hx]; exact Φ.map_source hxS
      · rw [← hx]; exact hxT
      · show Φ.symm (Pr x, 0) = x
        rw [← hx]; exact Φ.left_inv hxS
  · intro w hw
    have := congrArg Prod.fst (Φ.right_inv hw.1)
    rw [hΦ] at this
    simpa [hPr] using this

theorem hasFDerivAt_mvPolynomial_eval {n : ℕ} (Q : MvPolynomial (Fin n) ℂ) (x : Fin n → ℂ) :
    HasFDerivAt (fun y => MvPolynomial.eval y Q)
      (∑ j, MvPolynomial.eval x (MvPolynomial.pderiv j Q) •
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j) x := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval_C, MvPolynomial.pderiv_C, map_zero, zero_smul, Finset.sum_const_zero]
    exact hasFDerivAt_const a x
  | add p q hp hq =>
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    exact hp.add hq
  | mul_X p i hp =>
    have hXi : HasFDerivAt (fun y : Fin n → ℂ => y i)
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i) x := hasFDerivAt_apply i x
    have h2 := hp.mul hXi
    have hfun : (fun y : Fin n → ℂ => MvPolynomial.eval y (p * MvPolynomial.X i)) =
        (fun y => MvPolynomial.eval y p) * (fun y => y i) := by
      funext y
      simp
    have hder : (∑ j, MvPolynomial.eval x (MvPolynomial.pderiv j (p * MvPolynomial.X i)) •
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j) =
        MvPolynomial.eval x p • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) i +
          x i • ∑ j, MvPolynomial.eval x (MvPolynomial.pderiv j p) •
            ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) j := by
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
        Pi.smul_apply, ContinuousLinearMap.proj_apply, ContinuousLinearMap.add_apply, smul_eq_mul,
        Derivation.leibniz, MvPolynomial.pderiv_X, map_add, MvPolynomial.smul_eval, MvPolynomial.eval_X,
        Pi.single_apply]
      simp only [add_mul, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]
      simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X]
      have hs : ∑ j, MvPolynomial.eval x (if i = j then p else 0) * v j = MvPolynomial.eval x p * v i := by
        simp [apply_ite, ite_mul, Finset.sum_ite_eq]
      rw [hs]
      congr 1
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hfun, hder]
    exact h2

theorem exists_analytic_graph_chart_mvPolynomial {e c : ℕ}
    (P : Fin c → MvPolynomial (Fin (e + c)) ℂ) (p : Fin (e + c) → ℂ)
    (hp : ∀ i, MvPolynomial.eval p (P i) = 0)
    (hjac : Function.Surjective (fun v : Fin (e + c) → ℂ =>
      fun i => ∑ j, MvPolynomial.eval p (MvPolynomial.pderiv j (P i)) * v j)) :
    ∃ (σ : Equiv.Perm (Fin (e + c))) (U : Set (Fin (e + c) → ℂ)) (V : Set (Fin e → ℂ))
      (g : (Fin e → ℂ) → (Fin (e + c) → ℂ)),
      IsOpen U ∧ p ∈ U ∧ IsOpen V ∧ AnalyticOnNhd ℂ g V ∧
      Set.BijOn g V {x | x ∈ U ∧ ∀ i, MvPolynomial.eval x (P i) = 0} ∧
      ∀ w ∈ V, (fun i => g w (σ (Fin.castAdd c i))) = w := by
  classical
  let F : (Fin (e + c) → ℂ) → (Fin c → ℂ) := fun x i => MvPolynomial.eval x (P i)
  have hF0 : F p = 0 := funext hp
  have hFan : AnalyticAt ℂ F p := by
    rw [analyticAt_pi_iff]
    intro i
    have h := AnalyticOnNhd.eval_continuousLinearMap
      (ContinuousLinearMap.id ℂ (Fin (e + c) → ℂ)) (P i) p (Set.mem_univ _)
    simpa using h
  have hFd : HasFDerivAt F (ContinuousLinearMap.pi fun i =>
      ∑ j, MvPolynomial.eval p (MvPolynomial.pderiv j (P i)) •
        ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (e + c) => ℂ) j) p :=
    hasFDerivAt_pi.2 fun i => hasFDerivAt_mvPolynomial_eval (P i) p
  have hsurj : Function.Surjective (fderiv ℂ F p) := by
    rw [hFd.fderiv]
    convert hjac using 1
    ext v i
    simp
  obtain ⟨σ, U, V, g, hU, hpU, hV, hg, hbij, hproj⟩ :=
    exists_analytic_graph_chart F p hF0 hFan hsurj
  refine ⟨σ, U, V, g, hU, hpU, hV, hg, ?_, hproj⟩
  have hset : {x | x ∈ U ∧ F x = 0} = {x | x ∈ U ∧ ∀ i, MvPolynomial.eval x (P i) = 0} := by
    ext x; simp [F, funext_iff]
  rwa [hset] at hbij

end ReciprocityTheory.AnForm
