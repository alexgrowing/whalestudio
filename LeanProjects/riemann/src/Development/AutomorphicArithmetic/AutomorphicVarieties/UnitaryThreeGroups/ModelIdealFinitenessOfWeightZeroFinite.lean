import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Rigid0

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

private theorem map_sub_map_mem_pow_of_dist_le_zpow_neg {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (J : Ideal R)
    (hl : (l : R) ∈ J) {k : ℕ} (φ : (Fin k → ℤ_[l]) →+ R) (n : ℕ) (v w : Fin k → ℤ_[l])
    (h : dist v w ≤ (l : ℝ) ^ (-(n : ℤ))) : φ v - φ w ∈ J ^ n := by
  have hdiv : ∀ i, ∃ u : ℤ_[l], v i - w i = (l : ℤ_[l]) ^ n * u := by
    intro i
    have hi : ‖v i - w i‖ ≤ (l : ℝ) ^ (-(n : ℤ)) := by
      rw [← dist_eq_norm]
      exact (dist_le_pi_dist v w i).trans h
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton] at hi
    obtain ⟨u, hu⟩ := hi
    exact ⟨u, hu⟩
  choose u hu using hdiv
  have hvw : v - w = (l ^ n) • u := by
    ext i
    simp [hu i, nsmul_eq_mul]
  rw [← map_sub, hvw, map_nsmul, nsmul_eq_mul]
  refine Ideal.mul_mem_right _ _ ?_
  rw [Nat.cast_pow]
  exact Ideal.pow_mem_pow hl n

private theorem mem_range_of_approx {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (J : Ideal R)
    [IsHausdorff J R] (hl : (l : R) ∈ J) {k : ℕ} (φ : (Fin k → ℤ_[l]) →+ R) (y : R)
    (h : ∀ n : ℕ, ∃ v, y - φ v ∈ J ^ n) : ∃ v, φ v = y := by
  choose v hv using h
  obtain ⟨a, ψ, hψ, htend⟩ := SeqCompactSpace.tendsto_subseq v
  refine ⟨a, ?_⟩
  have hall : ∀ m : ℕ, y - φ a ∈ J ^ m := by
    intro m
    have hpos : (0 : ℝ) < (l : ℝ) ^ (-(m : ℤ)) := by
      have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
      exact zpow_pos hl0 _
    have hev1 : ∀ᶠ j in Filter.atTop, (v ∘ ψ) j ∈ Metric.closedBall a ((l : ℝ) ^ (-(m : ℤ))) :=
      htend.eventually (Metric.closedBall_mem_nhds a hpos)
    have hev2 : ∀ᶠ j in Filter.atTop, m ≤ ψ j := hψ.tendsto_atTop.eventually_ge_atTop m
    obtain ⟨j, hj1, hj2⟩ := (hev1.and hev2).exists
    have e1 : y - φ (v (ψ j)) ∈ J ^ m := Ideal.pow_le_pow_right hj2 (hv (ψ j))
    have e2 : φ (v (ψ j)) - φ a ∈ J ^ m := map_sub_map_mem_pow_of_dist_le_zpow_neg J hl φ m _ _ hj1
    have e3 := add_mem e1 e2
    rwa [sub_add_sub_cancel] at e3
  have h0 : y - φ a = 0 := by
    refine IsHausdorff.haus' (I := J) (y - φ a) (fun n => ?_)
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact hall n
  exact (sub_eq_zero.mp h0).symm

private theorem norm_coe_coefO_le_one {l : ℕ} [Fact l.Prime] (c : Coef l) (x : c.O) :
    ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  haveI := c.fin
  have hint : IsIntegral ℤ_[l] (x : PadicAlgCl l) := by
    have hx : IsIntegral ℤ_[l] x := Algebra.IsIntegral.isIntegral x
    exact hx.map c.O.val
  obtain ⟨p, hmon, hp⟩ := hint
  by_contra hgt
  push_neg at hgt
  rw [hmon.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum] at hp
  have hcoef : ∀ i ∈ Finset.range p.natDegree,
      ‖Polynomial.eval₂ (algebraMap ℤ_[l] (PadicAlgCl l)) (x : PadicAlgCl l)
        (Polynomial.C (p.coeff i) * Polynomial.X ^ i)‖ ≤ ‖(x : PadicAlgCl l)‖ ^ i := by
    intro i _
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, norm_mul, norm_pow]
    have hc : ‖algebraMap ℤ_[l] (PadicAlgCl l) (p.coeff i)‖ ≤ 1 := by
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends]
      exact PadicInt.norm_le_one _
    calc _ ≤ 1 * ‖(x : PadicAlgCl l)‖ ^ i := by gcongr
      _ = _ := one_mul _
  have hlt : ‖∑ i ∈ Finset.range p.natDegree, Polynomial.eval₂ (algebraMap ℤ_[l] (PadicAlgCl l))
      (x : PadicAlgCl l) (Polynomial.C (p.coeff i) * Polynomial.X ^ i)‖ <
      ‖(x : PadicAlgCl l)‖ ^ p.natDegree := by
    rcases Nat.eq_zero_or_pos p.natDegree with hn | hn
    · rw [hn]
      simp
    · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty
        (Finset.nonempty_range_iff.mpr hn.ne') (fun i => Polynomial.eval₂
          (algebraMap ℤ_[l] (PadicAlgCl l)) (x : PadicAlgCl l) (Polynomial.C (p.coeff i) * Polynomial.X ^ i))
      exact lt_of_le_of_lt (hle.trans (hcoef i hi)) (pow_lt_pow_right₀ hgt (Finset.mem_range.mp hi))
  have heq := eq_neg_of_add_eq_zero_left hp
  have hn := congrArg norm heq
  rw [norm_neg, norm_pow] at hn
  linarith

private theorem natCast_not_isUnit {l : ℕ} [Fact l.Prime] (c : Coef l) : ¬ IsUnit (l : c.O) := by
  rintro ⟨u, hu⟩
  have h1 := norm_coe_coefO_le_one c (↑u⁻¹ : c.O)
  have hprod : (l : PadicAlgCl l) * ((↑u⁻¹ : c.O) : PadicAlgCl l) = 1 := by
    have h := congrArg (fun z : c.O => (z : PadicAlgCl l)) (Units.mul_inv u)
    rw [hu] at h
    simpa using h
  have hl : ‖(l : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), PadicAlgCl.norm_extends, Padic.norm_p]
  have hn := congrArg norm hprod
  rw [norm_mul, norm_one, hl] at hn
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have hle : (l : ℝ)⁻¹ * ‖((↑u⁻¹ : c.O) : PadicAlgCl l)‖ ≤ (l : ℝ)⁻¹ * 1 :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have hinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  linarith

theorem UpperTheory.V.U3.modelIdeal_finiteness_of_weightZero_finite :
    ∀ {l : ℕ} [Fact l.Prime] {c : Coef l} {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      {η : Γ →* ℤˣ} {Ψ : Γ →* (c.O)ˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
      {U : Univ (GCond.noCondition c.O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ} (S : SRing N hι U I cc g₁) (M : Model S (PadicAlgCl l)), l ≠ 2 → Marks η Ψ cc g₁ →
      Module.Finite c.O (weightZeroSubalgebra c.O S.r.hom) → M2 M.𝒜 M.Q.ideal := by
  intro l _ c Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ S M hl2 hmk hfin
  haveI := c.dvr
  haveI := c.fin
  haveI hH : IsHausdorff (maximalIdeal S.R) S.R := (IsCO.complete (O := c.O) (R := S.R)).toIsHausdorff
  haveI hloc : IsLocalHom (algebraMap c.O S.R) := IsCO.isLocalHom (O := c.O) (R := S.R)
  have hlm : ((l : ℕ) : S.R) ∈ maximalIdeal S.R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply natCast_not_isUnit c
    rw [← map_natCast (algebraMap c.O S.R)] at hu
    exact isUnit_of_map_unit (algebraMap c.O S.R) _ hu
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := c.O) (M := weightZeroSubalgebra c.O S.r.hom)
  obtain ⟨t, o, ho⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := c.O)
  let F : (Fin n × Fin t → ℤ_[l]) → Fin n × Fin t → S.R := fun z q =>
    algebraMap c.O S.R (algebraMap ℤ_[l] c.O (z q) * o q.2) * ((b q.1 : weightZeroSubalgebra c.O S.r.hom) : S.R)
  let φ : (Fin (n * t) → ℤ_[l]) →+ S.R :=
    { toFun := fun v => ∑ q : Fin n × Fin t, F (v ∘ finProdFinEquiv) q
      map_zero' := by simp [F]
      map_add' := by
        intro v w
        simp only [F, Function.comp_apply, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib] }
  have hφB : ∀ v, φ v ∈ weightZeroSubalgebra c.O S.r.hom := by
    intro v
    show (∑ q : Fin n × Fin t, F (v ∘ finProdFinEquiv) q) ∈ _
    refine Subalgebra.sum_mem _ (fun q _ => ?_)
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (b q.1).2
  have hBφ : ∀ x ∈ weightZeroSubalgebra c.O S.r.hom, ∃ v, φ v = x := by
    intro x hx
    have hx' : (⟨x, hx⟩ : weightZeroSubalgebra c.O S.r.hom) ∈ Submodule.span c.O (Set.range b) := by
      rw [hb]
      trivial
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun c.O).mp hx'
    have hz : ∀ i, ∃ z : Fin t → ℤ_[l], ∑ j, z j • o j = a i := by
      intro i
      have hai : a i ∈ Submodule.span ℤ_[l] (Set.range o) := by
        rw [ho]
        trivial
      exact (Submodule.mem_span_range_iff_exists_fun ℤ_[l]).mp hai
    choose z hz using hz
    have hx2 : ∑ i, a i • ((b i : weightZeroSubalgebra c.O S.r.hom) : S.R) = x := by
      have h := congrArg Subtype.val ha
      simpa using h
    refine ⟨(fun q : Fin n × Fin t => z q.1 q.2) ∘ finProdFinEquiv.symm, ?_⟩
    show ∑ q : Fin n × Fin t,
      F (((fun q : Fin n × Fin t => z q.1 q.2) ∘ finProdFinEquiv.symm) ∘ finProdFinEquiv) q = x
    have hcomp : ((fun q : Fin n × Fin t => z q.1 q.2) ∘ finProdFinEquiv.symm) ∘ finProdFinEquiv =
        fun q => z q.1 q.2 := by
      funext q
      simp
    rw [hcomp, Fintype.sum_prod_type, ← hx2]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [F]
    rw [← Finset.sum_mul, ← map_sum, Algebra.smul_def, ← hz i]
    congr 2
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Algebra.smul_def]
  have key : ∀ f ∈ M.𝒜 0, M.q f ∈ weightZeroSubalgebra c.O S.r.hom := by
    intro f hf
    obtain ⟨v, hv⟩ := mem_range_of_approx (maximalIdeal S.R) hlm φ (M.q f) (fun m => by
      obtain ⟨y, hy, hdiff⟩ := M.dense 0 f hf m
      have hle : Submodule.span c.O (entMon S.r.hom 0) ≤ Subalgebra.toSubmodule (weightZeroSubalgebra c.O S.r.hom) :=
        Submodule.span_le.mpr (fun z hz => Algebra.subset_adjoin hz)
      obtain ⟨v, hv⟩ := hBφ y (hle hy)
      exact ⟨v, by rw [hv]; exact hdiff⟩)
    rw [← hv]
    exact hφB v
  have hsub : (M.𝒜 0).map M.q.toLinearMap ≤ Subalgebra.toSubmodule (weightZeroSubalgebra c.O S.r.hom) := by
    rintro _ ⟨f, hf, rfl⟩
    exact key f hf
  haveI : Module.Finite c.O (Subalgebra.toSubmodule (weightZeroSubalgebra c.O S.r.hom)) := hfin
  haveI hpir : IsPrincipalIdealRing c.O := c.dvr.toIsPrincipalIdealRing
  haveI hnr : IsNoetherianRing c.O := PrincipalIdealRing.isNoetherianRing
  haveI : IsNoetherian c.O (Subalgebra.toSubmodule (weightZeroSubalgebra c.O S.r.hom)) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  have hfg : ((M.𝒜 0).map M.q.toLinearMap).FG := isNoetherian_submodule.mp inferInstance _ hsub
  show (Submodule.map (Ideal.Quotient.mkₐ c.O M.Q.ideal).toLinearMap (M.𝒜 0)).FG
  rw [← M.ker_q]
  refine Submodule.fg_of_fg_map_injective (Ideal.kerLiftAlg M.q).toLinearMap
    (Ideal.kerLiftAlg_injective M.q) ?_
  rw [← Submodule.map_comp]
  convert hfg using 2
  ext a
  simp [Ideal.kerLiftAlg_mk]
