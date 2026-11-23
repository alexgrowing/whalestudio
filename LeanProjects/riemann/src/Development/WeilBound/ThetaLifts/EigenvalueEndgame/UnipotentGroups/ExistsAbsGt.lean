import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.IsFrPlane
import Development.WeilBound.ThetaLifts.CartanFactorisation.IntegrableOnRight

noncomputable section

namespace PositivityTheory.ThKEnd.Grp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKG.Tow.Levi

section Abs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

theorem abs_uniq [LocallyCompactSpace G] [SecondCountableTopology G] {Γ : Subgroup G} [Countable Γ] {μ μ' : Measure G}
    [μ.IsHaarMeasure] [μ'.IsHaarMeasure] {𝓕 𝓕' : Set G} (h2 : IsFundamentalDomain Γ 𝓕 μ) (h3 : μ 𝓕 = 1)
    (k2 : IsFundamentalDomain Γ 𝓕' μ') (k3 : μ' 𝓕' = 1) {f : G → ℂ} (hf : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x) :
    ∫ u in 𝓕, f u ∂μ = ∫ u in 𝓕', f u ∂μ' := by
  have e := Measure.isMulLeftInvariant_eq_smul μ' μ
  have k4 : IsFundamentalDomain _ 𝓕 μ' := h2.mono (by rw [e]; exact Measure.smul_absolutelyContinuous)
  have k5 := k4.measure_eq k2
  rw [k3, e, Measure.smul_apply, h3, ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_eq_one] at k5
  rw [k5, one_smul] at e
  subst e
  exact h2.setIntegral_eq k2 fun γ x => hf γ γ.2 x

theorem abs_conj {Γ N N₂ : Subgroup G} {γ : G} (hγ : γ ∈ Γ) (hN : ∀ u, u ∈ N₂ ↔ γ * u * γ⁻¹ ∈ N) (μ : Measure N) (𝓕 : Set N)
    [μ.IsHaarMeasure] (h2 : IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ) : ∃ (μ₂ : Measure N₂) (𝓕₂ : Set N₂), μ₂.IsHaarMeasure ∧
      IsFundamentalDomain (Γ.subgroupOf N₂) 𝓕₂ μ₂ ∧ μ₂ 𝓕₂ = μ 𝓕 ∧
      ∀ f : G → ℂ, ∫ u in 𝓕₂, f (γ * u.1 * γ⁻¹) ∂μ₂ = ∫ u in 𝓕, f u.1 ∂μ := by
  let φ : N ≃ₜ* N₂ :=
    { toFun := fun u => ⟨γ⁻¹ * u * γ, (hN _).2 (by simpa [mul_assoc] using u.2)⟩
      invFun := fun u => ⟨γ * u * γ⁻¹, (hN _).1 u.2⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun u v => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
      continuous_invFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _ }
  let ψ := φ.toHomeomorph.toMeasurableEquiv
  have mp : MeasurePreserving ψ μ (μ.map ψ) := ⟨ψ.measurable, rfl⟩
  let e : Γ.subgroupOf N ≃ Γ.subgroupOf N₂ :=
    φ.toEquiv.subtypeEquiv fun u => ⟨fun k => mul_mem (mul_mem (inv_mem hγ) (show u.1 ∈ Γ from k)) hγ, fun k => by
      have := mul_mem (mul_mem hγ (show γ⁻¹ * u.1 * γ ∈ Γ from k)) (inv_mem hγ)
      change u.1 ∈ Γ
      simpa [mul_assoc] using this⟩
  refine ⟨μ.map ψ, ψ.symm ⁻¹' 𝓕, φ.isHaarMeasure_map μ,
    h2.preimage_of_equiv mp.symm.quasiMeasurePreserving e.bijective fun g x => ?_, ?_, fun f => ?_⟩
  · change φ.symm (φ g.1 * x) = g.1 * φ.symm x
    rw [map_mul, φ.symm_apply_apply]
  · rw [ψ.map_apply, ← Set.preimage_comp, ψ.symm_comp_self, Set.preimage_id]
  · exact mp.symm.setIntegral_preimage_emb ψ.symm.measurableEmbedding (fun u : N => f u.1) 𝓕

end Abs

variable {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H : Plane E d d₁}

theorem UnipGood.integrable {N : Subgroup (UA σ W.J)} (hN : UnipGood N) {μ : Measure N} {𝓕 : Set N} (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain ((ratU σ W.J).subgroupOf N) 𝓕 μ) {f : UA σ W.J → ℂ} (hf : IsAut f) (h : UA σ W.J) :
    IntegrableOn (fun u : N => f (u.1 * h)) 𝓕 μ := by
  obtain ⟨C, hC, hc⟩ := hN.cov
  have c : Continuous fun u : N => f (u.1 * h) := hf.1.comp (continuous_subtype_val.mul continuous_const)
  obtain ⟨b, hb⟩ := hC.exists_bound_of_continuousOn c.continuousOn
  refine Measure.integrableOn_of_bounded (hN.fin μ 𝓕 hμ h𝓕).2.ne c.aestronglyMeasurable (M := b)
    (Filter.Eventually.of_forall fun u => ?_)
  obtain ⟨γ, h1, h2⟩ := hc u
  have := hb _ h2
  rwa [Subgroup.coe_mul, mul_assoc, hf.2 _ h1] at this

theorem ct_inv (hN : UnipGood (unip σ W H)) {f c : UA σ W.J → ℂ} (hf : IsAut f) (hc : IsCT H f c) {u : UA σ W.J}
    (hu : u ∈ unip σ W H) (h : UA σ W.J) : c (u * h) = c h := by
  obtain ⟨μ, 𝓕, h1, h2, h3⟩ := hN.ex
  have := hN.cnt
  have := hN.right μ h1
  rw [hc μ 𝓕 h1 h2 h3, hc μ 𝓕 h1 h2 h3,
    ← PositivityTheory.ThKF.L2.integral_right h2 (fun v => f (v.1 * h)) (fun γ hγ x => by rw [Subgroup.coe_mul, mul_assoc]; exact hf.2 _ hγ _) ⟨u, hu⟩]
  simp only [Subgroup.coe_mul, mul_assoc]

theorem exists_ct (hN : UnipGood (unip σ W H)) {f : UA σ W.J → ℂ} (hf : IsAut f) : ∃ c, IsCT H f c := by
  obtain ⟨μ, 𝓕, h1, h2, h3⟩ := hN.ex
  have := hN.cnt
  have := hN.lc
  have := hN.sc
  exact ⟨fun h => ∫ u in 𝓕, f (u.1 * h) ∂μ, fun μ' 𝓕' k1 k2 k3 h => abs_uniq h2 h3 k2 k3 fun γ hγ x => by
    rw [Subgroup.coe_mul, mul_assoc]; exact hf.2 _ hγ _⟩

theorem exists_abs_gt : ∃ t : (AE F E)ˣ, 1 < (absE F E t : ℝ) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨b, h2⟩ : ∃ b : w.Completion, ‖b‖ = 2 := by
    refine ⟨_, (InfinitePlace.Completion.norm_coe w ((WithAbs.equiv w.1).symm (2 : F))).trans ?_⟩
    show w (2 : F) = 2
    rw [← InfinitePlace.mk_embedding w, InfinitePlace.apply, map_ofNat]
    norm_num
  have hne : b ≠ 0 := by
    intro h; rw [h, norm_zero] at h2; norm_num at h2
  refine ⟨GlobalTheory.Doubling.ideleAtInf F E w (Units.map (algebraMap w.Completion (w.Completion ⊗[F] E)).toMonoidHom (Units.mk0 b hne)), ?_⟩
  rw [GlobalTheory.Doubling.absE_ideleAtInf, GlobalTheory.Doubling.absEw_apply]
  change 1 < ((‖Algebra.norm w.Completion (algebraMap w.Completion (w.Completion ⊗[F] E) b)‖₊ ^ w.mult : ℝ≥0) : ℝ)
  rw [Algebra.norm_algebraMap, Module.finrank_baseChange, NNReal.coe_pow, coe_nnnorm, norm_pow, h2, ← pow_mul]
  have hn : 0 < Module.finrank F E := Module.finrank_pos
  have hm : 0 < w.mult := by unfold InfinitePlace.mult; split_ifs <;> norm_num
  exact one_lt_pow₀ (by norm_num) (Nat.mul_ne_zero hn.ne' hm.ne')

theorem ctBasic : CTBasic := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H r s hB hW hH
  have hN := unipGood hB.cm (Or.inr hW.skew) (det_ne_zero hW) hH
  refine ⟨fun f g cf cg c hf hg h1 h2 μ 𝓕 k1 k2 k3 h => ?_, fun f T T' χ χ' z z' hf hz hc l l' u hu h => ?_⟩
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_sub (hN.integrable k1 k2 hf h) ((hN.integrable k1 k2 hg h).const_mul c), integral_const_mul,
      h1 μ 𝓕 k1 k2 k3, h2 μ 𝓕 k1 k2 k3]
  · obtain ⟨t, ht⟩ := exists_abs_gt (F := F) (E := E)
    obtain ⟨L1, L2⟩ := leviPlane F E σ hB.cm d d₁ W W₁ H hW.skew hH
    obtain ⟨m, hm⟩ := L1 t 1
    have e1 := ct_inv hN hf hc hu h
    have e2 := ct_inv hN hf hc (L2 t 1 m hm u hu) (m * h)
    rw [show m * u * m⁻¹ * (m * h) = m * (u * h) by group] at e2
    simp only [Pi.add_apply, l t m hm, l' t m hm] at e1 e2
    have ne : (χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ) - (χ' t : ℂ) * (((absE F E t : ℝ) ^ z' : ℝ) : ℂ) ≠ 0 := fun k => by
      have := congrArg norm (sub_eq_zero.1 k)
      have p : (0 : ℝ) < absE F E t := zero_lt_one.trans ht
      simp only [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg p.le _)] at this
      exact hz ((Real.rpow_right_inj p ht.ne').1 this)
    have e3 : T (u * h) = T h := sub_eq_zero.1 (mul_left_cancel₀ ne (by
      linear_combination e2 - (χ' t : ℂ) * (((absE F E t : ℝ) ^ z' : ℝ) : ℂ) * e1))
    exact ⟨e3, by linear_combination e1 - e3⟩

theorem ct_conj {d₂ : ℕ} {H₂ : Plane E d d₂} {γ : UA σ W.J} (hγ : γ ∈ ratU σ W.J)
    (hN : ∀ u, u ∈ unip σ W H₂ ↔ γ * u * γ⁻¹ ∈ unip σ W H) {f c : UA σ W.J → ℂ} (hf : IsAut f) (hc : IsCT H₂ f c) :
    IsCT H f fun h => c (γ⁻¹ * h) := by
  intro μ 𝓕 h1 h2 h3 h
  obtain ⟨μ₂, 𝓕₂, k1, k2, k3, k4⟩ := abs_conj hγ hN μ 𝓕 h2
  rw [← k4 fun u => f (u * h)]
  refine (hc _ _ k1 k2 (k3.trans h3) _).trans ?_
  congr 1
  funext u
  rw [mul_assoc, mul_assoc, hf.2 _ hγ]

theorem lineMove : LineMove := by
  rintro F E _ _ _ _ _ σ B d d₁ W W₁ H r s χ z f hB hW hH hf ⟨d₂, W₂, H₂, c, hH₂, hc, hl⟩
  have sk := Or.inr (a := ∀ i j, σ (W.J j i) = W.J i j) hW.skew
  have ne : ∀ {k} {Y : Spc F E k} {P : Plane E d k}, IsPlane σ P W Y → P.x ≠ 0 := fun h h0 => by
    have e := h.xy
    rw [h0, form, zero_dotProduct] at e
    exact zero_ne_one e
  obtain ⟨g, g1, g2⟩ := wittVec F E σ hB.cm d W.J hW.skew (det_ne_zero hW) _ _ (ne hH₂) (ne hH) hH₂.xx hH.xx
  let γ : UA σ W.J := ⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) g, by
    change (incM F g.1ᵀ) * incM F W.J * (incM F g.1).map (cA σ) = _
    rw [incM_conj, ← incM_mul, ← incM_mul, g1]⟩
  have hγ : γ ∈ ratU σ W.J := ⟨g, rfl⟩
  have e1 : mat γ *ᵥ incV F H₂.x = (1 : (AE F E)ˣ).1 • incV F H.x := by
    rw [Units.val_one, one_smul, ← g2]; exact incM_mulVec _ _
  have e2 : mat γ⁻¹ *ᵥ incV F H.x = (1 : (AE F E)ˣ).1 • incV F H₂.x := by
    rw [Units.val_one, one_smul] at e1 ⊢; exact inv_vec e1
  refine ⟨_, ct_conj hγ (fun u => ?_) hf hc, fun t m hm h => ?_⟩
  · rw [mem_unip hB.cm sk hH, mem_unip hB.cm sk hH₂]
    exact ⟨fun k => k.conj e1, fun k => by simpa [mul_assoc] using k.conj e2⟩
  · obtain ⟨m₀, h₀⟩ := (leviPlane F E σ hB.cm d d₂ W W₂ H₂ hW.skew hH₂).1 t 1
    have p := ((IsLevi.par (form_yx hB.cm sk hH) hH hm).conj e2).div (IsLevi.par (form_yx hB.cm sk hH₂) hH₂ h₀)
    have := ct_inv (unipGood hB.cm sk (det_ne_zero hW) hH₂) hf hc ((mem_unip hB.cm sk hH₂).2 p) (m₀ * (γ⁻¹ * h))
    rw [hl t m₀ h₀] at this
    rw [← this]
    congr 1
    group

end PositivityTheory.ThKEnd.Grp

end
