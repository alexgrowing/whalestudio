import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.LeviInductionForms

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders Formalism.MainNotions.G.symbolGeneratorData

theorem sum_comp_image {R σ M : Type*} [CommSemiring R] [AddCommMonoid M] (wt : σ → M) (φ : MvPolynomial σ R) :
    ∑ D ∈ φ.support.image (Finsupp.weight wt), weightedHomogeneousComponent wt D φ = φ := by
  ext m
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with hm
  · rfl
  · by_contra hne
    exact hm (Finset.mem_image_of_mem _ (mem_support_iff.2 (Ne.symm hne)))

section XX

variable {O : Type} [CommRing O] [IsDomain O] {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] (F : Frames n' r) (j : ℤ)

theorem xx_span_MGen0 (th o : ℤ → ℝ) {xi : SegRing O r K} (hxi : xi ∈ XX' O r K F j (fun _ => 0) th o) :
    xi ∈ Submodule.span O (MGen0 F j O K) := by
  unfold XX' at hxi
  have h1 := (Submodule.mem_inf.1 hxi).1
  have h2 : xi ∈ Submodule.map (plnm F j O K).toLinearMap (Submodule.span O (GenM (O := O) (K := K) F j 0 th)) := by
    rw [Submodule.map_span]
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨A, G, M, hA, hG, hC, rfl⟩
    obtain ⟨A0, rfl⟩ := exists_rename_eq_of_vars_subset_range A _ (md_f_inj F j r) (by
      intro v hv
      obtain ⟨i, hi⟩ := md_eL_surj F j ((mem_supported.1 hA) hv)
      exact ⟨(i, v.2), by simp [hi]⟩)
    obtain ⟨G0, rfl⟩ := exists_rename_eq_of_vars_subset_range G _ (md_f_inj F j K) (by
      intro v hv
      obtain ⟨i, hi⟩ := md_eL_surj F j ((mem_supported.1 hG) hv).1
      exact ⟨(i, v.2), by simp [hi]⟩)
    refine ⟨rename (plVar (K := K)) A0 * rename (tanVar (r := r)) G0,
      ⟨A0, G0, fun i => M (eL F j i), ?_, ?_, ?_, rfl⟩, ?_⟩
    · intro v hv
      obtain ⟨m0, hm0, hvm⟩ := (mem_vars_iff_mem_support _).1 hv
      have h3 : (eL F j v.1, v.2) ∈ (rename (fun v : Fin (Mj F j) × Fin K => (eL F j v.1, v.2)) G0).vars := by
        refine (mem_vars_iff_mem_support _).2
          ⟨Finsupp.mapDomain (fun v : Fin (Mj F j) × Fin K => (eL F j v.1, v.2)) m0, ?_, ?_⟩
        · rw [support_rename_of_injective (md_f_inj F j K)]
          exact Finset.mem_image_of_mem _ hm0
        · rw [Finsupp.mem_support_iff]
          have := Finsupp.mapDomain_apply (md_f_inj F j K) m0 v
          rw [this]
          exact Finsupp.mem_support_iff.1 hvm
      exact ((mem_supported.1 hG) h3).2
    · intro i hi
      have hc := hC (eL F j i) (md_eL_mem F j i) hi
      rw [md_lam_tr F j {y | y ≤ eL F j i} {y | y ≤ i} (fun i' => md_eL_le F j i' i),
        md_lam_tr F j {y | y < eL F j i} {y | y < i} (fun i' => md_eL_lt F j i' i),
        md_val_tr F j {y | y ≤ eL F j i} {y | y ≤ i} (fun i' => md_eL_le F j i' i),
        md_val_tr F j {y | y < eL F j i} {y | y < i} (fun i' => md_eL_lt F j i' i)] at hc
      exact ⟨hc.1, hc.2.1⟩
    · intro i hi
      have hc := (hC (eL F j i) (md_eL_mem F j i) hi).2.2
      rw [md_val_tr F j {y | y < eL F j i} {y | y < i} (fun i' => md_eL_lt F j i' i)] at hc
      exact hc
    · show plnm F j O K _ = _
      unfold plnm plEmb nmEmb
      rw [map_mul, rename_rename, rename_rename, rename_rename, rename_rename]
      rfl
  obtain ⟨ξ0, hξ0, rfl⟩ := h2
  rw [← sum_comp_image letterWeight ξ0, map_sum]
  refine Submodule.sum_mem _ fun D _ => ?_
  have h5 := md_comp_gen F j 0 th D hξ0
  have h6 := Submodule.mem_map_of_mem (f := (plnm F j O K).toLinearMap) h5
  rw [Submodule.map_span] at h6
  refine Submodule.span_mono ?_ h6
  rintro _ ⟨P0, ⟨d', d'', A, G, Mx, a1, a2, _, a4, a5, _, rfl⟩, rfl⟩
  exact ⟨d', d'', A, G, Mx, a1, a2, a4, a5, rfl⟩

end XX

section Ctx

variable {p n' r K : ℕ} [Fact p.Prime] [NeZero n'] [NeZero r] [NeZero K] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra (WF p n') O] (X : Ctx p n' r K O)

local notation "PP" => MvPolynomial (TV n' (r + K)) (KK O)

theorem seg_SyS (hW1 : GeneratorSpanInclusion) (hW2 : GeneratorImageIsSymbol) (j : ℤ) (mg : ℤ → ℤ) (th o : ℤ → ℝ) (hmg : ∀ x, 0 ≤ mg x)
    {x : SegRing O r K} (hx : x ∈ XX' O r K X.Fr j mg th o) :
    MvPolynomial.map (algebraMap O (KK O)) (phSeg O K p X.Fr j x) ∈ X.SyS := by
  have h1 := xx_span_MGen0 X.Fr j th o (xx_mono X.Fr j mg th o hmg hx)
  have h2 : x ∈ Submodule.span O (PGen X.Fr j O K) :=
    (Submodule.span_le.2 fun P hP => hW1 p n' r K O X j P hP) h1
  exact SyS_of_span X hW2 j h2

theorem w_ne : algebraMap O (KK O) X.S.w ≠ 0 := by
  intro h
  exact X.S.w_irr.ne_zero ((IsFractionRing.injective O (KK O)) (by rw [h, map_zero]))

theorem sb_surj (T : PP) : ∃ F0 : PP, X.sb F0 = T := by
  let inv : PP →ₐ[KK O] PP := aeval fun v =>
    (if IsNormal r v then C (algebraMap O (KK O) X.S.w)⁻¹ else 1) * newCoord p n' O n' X.g v
  have h : X.sb.comp inv = AlgHom.id (KK O) PP := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [AlgHom.comp_apply, inv, aeval_X, AlgHom.id_apply]
    unfold Ctx.sb
    rw [map_mul, substitute_new_coordinate X.S.w r X.hg X.hH.2.2.2.2 v]
    unfold newVar
    split_ifs with hv
    · have e2 : subst p n' O X.S.w n' r X.g (C (algebraMap O (KK O) X.S.w)⁻¹) = C (algebraMap O (KK O) X.S.w)⁻¹ := by
        rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      rw [e2, ← mul_assoc, ← C_mul, inv_mul_cancel₀ (w_ne X), C_1, one_mul]
    · rw [map_one, one_mul]
  exact ⟨inv T, by
    have := congrArg (fun f => f T) h
    simpa using this⟩

theorem sb_SPtrue (c' : ℕ) : X.sb (SPtrue p n' O X.Fr X.hH.2.2.1 X.g c' X.Q) = X.fixedSymbolFactor c' * X.DkQ := by
  unfold SPtrue Ctx.fixedSymbolFactor Ctx.DkQ
  have e : DtopProd p n' O X.Fr X.hH.2.2.1 X.g ((2 * X.Q + 3) * c' + (r + K) * X.Q) =
      DtopProd p n' O X.Fr X.hH.2.2.1 X.g ((2 * X.Q + 3) * c') * DtopProd p n' O X.Fr X.hH.2.2.1 X.g ((r + K) * X.Q) := by
    unfold DtopProd
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => pow_add _ _ _
  rw [e]
  simp only [map_mul, map_pow, map_prod]
  ring

theorem sb_multideg {F : PP} {d : Fin n' → ℕ} (h : HasMultideg F d) : HasMultideg (X.sb F) d := by
  rw [hasMultideg_iff_weighted_homog] at h ⊢
  have := weighted_component_substitute_comm X.S.w r X.g d F
  rw [h.weightedHomogeneousComponent_same] at this
  unfold Ctx.sb
  rw [← this]
  exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

theorem exists_pol_family_of_mem_gen_of_vsDeg_le (D : Formalism.BasicNotions.D7) (hW1 : GeneratorSpanInclusion) (hW2 : GeneratorImageIsSymbol) (hMon : RestMon) (c' : ℕ)
    (mg : ℤ → ℤ → ℤ) (th o : ℤ → ℤ → ℝ) (hmg : ∀ j x, 0 ≤ mg j x) (d0 E' dTop : Fin n' → ℕ)
    (hd : ∀ s, d0 s + E' s = dTop s) (hd0 : ∀ s, s ∉ X.Fr.TT → d0 s = 0)
    (hE : HasMultideg (SPtrue p n' O X.Fr X.hH.2.2.1 X.g c' X.Q) E')
    (P : RRing O n' (r + K)) (hP : P ∈ Gen O p K X.Fr (fun j => XX' O r K X.Fr j (mg j) (th j) (o j)) d0)
    (T : ℕ) (hT : ∀ mm ∈ P.support, vsDeg mm ≤ T) :
    ∃ Fs : ℕ → ↥((Pol (KK O) (ι := Fin n') (r + K) dTop).restrictScalars O),
      (∀ o, HasMultideg (X.sb (Fs o : PP)) dTop ∧ InWj X.S.w (X.sb (Fs o : PP)) 0 ∧
        Realisable p n' X.S.w n' r X.g c' o (X.sb (Fs o : PP))) ∧
      ∑ o ∈ Finset.range (T + 1), X.sb (Fs o : PP) =
        MvPolynomial.map (algebraMap O (KK O)) P * X.sb (SPtrue p n' O X.Fr X.hH.2.2.1 X.g c' X.Q) := by
  obtain ⟨x, hx, l, hl, hPe, hPd⟩ := hP

  set Tt : PP := MvPolynomial.map (algebraMap O (KK O)) P * X.sb (SPtrue p n' O X.Fr X.hH.2.2.1 X.g c' X.Q) with hTt
  have hH0 : bc_IT X.Fr (X.fixedSymbolFactor c' * X.DkQ) := bc_IT_mul (fixed_symbol_factor_integral X c') (mn_DkQ_IT X)
  have hmdP : HasMultideg (MvPolynomial.map (algebraMap O (KK O)) P) d0 := by
    unfold HasMultideg Pol
    rw [mem_restrictSupport_iff]
    intro m hm
    unfold RRdeg at hPd
    rw [mem_restrictSupport_iff] at hPd
    exact hPd (Finset.mem_coe.2 (support_map_subset _ _ (Finset.mem_coe.1 hm)))
  have hmdT : HasMultideg Tt dTop := by
    have h1 := (hasMultideg_iff_weighted_homog _ _).1 hmdP
    have h2 := (hasMultideg_iff_weighted_homog _ _).1 (sb_multideg X hE)
    have h3 := h1.mul h2
    have e : d0 + E' = dTop := funext hd
    rw [e] at h3
    exact (hasMultideg_iff_weighted_homog _ _).2 h3
  have hintT : InWj X.S.w Tt 0 := by
    rw [hTt, sb_SPtrue]
    obtain ⟨h0, _, _, e0⟩ := hH0
    rw [e0]
    exact inWPow_zero_mul (inWj_map _) (inWj_map _)
  have hwtT : ∀ m ∈ Tt.support, Finsupp.weight (normalVariableWeight n' (r + K) r) m ≤ T := by
    intro m hm
    rw [hTt, sb_SPtrue] at hm
    have hm' := MvPolynomial.support_mul _ _ hm
    obtain ⟨m1, h1, m2, h2, rfl⟩ := Finset.mem_add.1 hm'
    rw [map_add, IT_hom hH0 (mem_support_iff.1 h2), add_zero, weight_eq_normal_degree, normDeg_eq_vsDeg]
    exact hT m1 (support_map_subset _ _ h1)

  have hreal : ∀ o, Realisable p n' X.S.w n' r X.g c' o (weightedHomogeneousComponent (normalVariableWeight n' (r + K) r) o Tt) := by
    intro o
    by_cases hP0 : P = 0
    · have : Tt = 0 := by rw [hTt, hP0, map_zero, zero_mul]
      rw [this, map_zero]
      refine ⟨0, (inA_iff_inWj0 (w := X.S.w) _).2 (inWj_zero 0), fun d' _ => Submodule.zero_mem _, ?_, ?_⟩
      · rw [map_zero, mul_zero, sub_zero]; exact inWj_zero _
      · intro g' _ _
        show InWj X.S.w (subst p n' O X.S.w n' r g' 0) (o + c')
        rw [map_zero]; exact inWj_zero _
    ·
      have hlT : ∀ v ∈ l.support, v.1 ∈ X.Fr.TT := by
        intro v hv
        by_contra hvT
        have hA0 : (∏ j ∈ Finset.range X.Fr.J, phSeg O K p X.Fr (j : ℤ) (x j)) ≠ 0 := by
          intro h0
          exact hP0 (by rw [hPe, h0, zero_mul])
        obtain ⟨m1, hm1⟩ := MvPolynomial.support_nonempty.2 hA0
        have hmem : m1 + l ∈ P.support := by
          rw [mem_support_iff, hPe, coeff_mul_monomial, mul_one]
          exact mem_support_iff.1 hm1
        unfold RRdeg at hPd
        rw [mem_restrictSupport_iff] at hPd
        have h3 := hPd (Finset.mem_coe.2 hmem) v.1
        rw [hd0 v.1 hvT] at h3
        have h4 := (Finset.sum_eq_zero_iff.1 h3) v.2 (Finset.mem_univ _)
        have h5 : l v = 0 := by
          have : (m1 + l) (v.1, v.2) = m1 v + l v := rfl
          omega
        exact (Finsupp.mem_support_iff.1 hv) h5
      obtain ⟨om, hom⟩ := hMon p n' r K O X l hl hlT
      set Sg : PP := ∏ j ∈ Finset.range X.Fr.J, MvPolynomial.map (algebraMap O (KK O)) (phSeg O K p X.Fr (j : ℤ) (x j))
        with hSg
      have hSgS : Sg ∈ X.SyS := SyS_prod _ _ fun j _ => seg_SyS X hW1 hW2 (j : ℤ) _ _ _ (hmg _) (hx _)
      have hZ : monomial l 1 * X.DkQ * Sg ∈ X.SyS := SyS_mul (SyS_of_Sy hom) hSgS
      have hTe : Tt = (monomial l 1 * X.DkQ * Sg) * X.fixedSymbolFactor c' := by
        rw [hTt, sb_SPtrue, hPe, map_mul, map_monomial, map_one, map_prod, ← hSg]
        ring
      obtain ⟨FinalForm, hZo, hZe⟩ := SyS_compZ (IT_hom (fixed_symbol_factor_integral X c')) hZ o
      rw [hTe, hZe]
      refine core X D c' o _ FinalForm 0 hZo (inWj_zero 0) (by rw [mul_zero, add_zero]) ?_
      rw [← hZe, hom_iff]
      exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

  have hpre : ∀ o, ∃ Fo : ↥((Pol (KK O) (ι := Fin n') (r + K) dTop).restrictScalars O),
      X.sb (Fo : PP) = weightedHomogeneousComponent (normalVariableWeight n' (r + K) r) o Tt := by
    intro o
    obtain ⟨F0, hF0⟩ := sb_surj X (weightedHomogeneousComponent (normalVariableWeight n' (r + K) r) o Tt)
    have hmo : IsWeightedHomogeneous (coordinatePositionWeight n' (r + K)) (weightedHomogeneousComponent (normalVariableWeight n' (r + K) r) o Tt) dTop := by
      intro m hm
      rw [coeff_weightedHomogeneousComponent] at hm
      split_ifs at hm with h1
      · exact (hasMultideg_iff_weighted_homog _ _).1 hmdT hm
      · exact absurd rfl hm
    refine ⟨⟨weightedHomogeneousComponent (coordinatePositionWeight n' (r + K)) dTop F0,
      (hasMultideg_iff_weighted_homog _ _).2 (weightedHomogeneousComponent_isWeightedHomogeneous _ _)⟩, ?_⟩
    show X.sb (weightedHomogeneousComponent (coordinatePositionWeight n' (r + K)) dTop F0) = _
    unfold Ctx.sb at hF0 ⊢
    rw [← weighted_component_substitute_comm, hF0, hmo.weightedHomogeneousComponent_same]
  choose Fs hFs using hpre
  refine ⟨Fs, fun o => ?_, ?_⟩
  · rw [hFs o]
    refine ⟨?_, inWj_compN o hintT, hreal o⟩
    rw [hasMultideg_iff_weighted_homog]
    intro m hm
    rw [coeff_weightedHomogeneousComponent] at hm
    split_ifs at hm with h1
    · exact (hasMultideg_iff_weighted_homog _ _).1 hmdT hm
    · exact absurd rfl hm
  · simp only [hFs]
    exact sum_comp_range _ Tt T hwtT

end Ctx

end Formalism.MainNotions.Pf14
