import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BasePsiLeviLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthogonalFrameDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaximumBoundField
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormalisedThetaNormInvariant
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LevelTupleSumEqRational
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointwiseNormCanonicalThetaEqSqThetaConstant
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsGeneratorsLattice

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ContDiff

namespace GlobalTheory.ThetaLogSum

open GlobalTheory.LevelTupleSum

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

theorem gen_map {Λ : Submodule (𝓞 E) (Fin r → E)} (e : (Fin r → E) ≃ₗ[E] (Fin r → E))
    (he : ∀ v, v ∈ Λ ↔ e v ∈ Λ) {t : Fin r → Fin r → E} (h : Gen Λ t) :
    Gen Λ fun j => e (t j) := by
  refine ⟨fun j => ?_, fun u hu => ?_⟩
  · rw [← map_smul]
    exact (he _).1 (h.1 j)
  · obtain ⟨c, y, hy, h2⟩ := h.2 (e.symm u) ((he _).2 (by simpa using hu))
    refine ⟨c, e y, (he _).1 hy, ?_⟩
    have := congrArg e h2
    simpa only [LinearEquiv.apply_symm_apply, map_add, map_sum, map_smul] using this

theorem exists_reps_map {Λ : Submodule (𝓞 E) (Fin r → E)} (e : (Fin r → E) ≃ₗ[E] (Fin r → E))
    (he : ∀ v, v ∈ Λ ↔ e v ∈ Λ) (𝒯 : Finset (Fin r → Fin r → E)) (h1 : ∀ t ∈ 𝒯, Gen Λ t)
    (h2 : ∀ t, Gen Λ t → ∃! t', t' ∈ 𝒯 ∧ ∀ j, t j - t' j ∈ Λ) :
    ∃ 𝒯' : Finset (Fin r → Fin r → E), (∀ t ∈ 𝒯', Gen Λ t) ∧
      (∀ t, Gen Λ t → ∃! t', t' ∈ 𝒯' ∧ ∀ j, t j - t' j ∈ Λ) ∧
      ∀ f : (Fin r → Fin r → E) → ℝ, ∑ t ∈ 𝒯', f t = ∑ t ∈ 𝒯, f fun j => e (t j) := by
  let ι : (Fin r → Fin r → E) ↪ (Fin r → Fin r → E) :=
    ⟨fun t j => e (t j), fun t t' h => funext fun j => e.injective (congrFun h j)⟩
  refine ⟨𝒯.map ι, fun t ht => ?_, fun t ht => ?_, fun f => Finset.sum_map _ _ _⟩
  · obtain ⟨s, hs, rfl⟩ := Finset.mem_map.1 ht
    exact gen_map e he (h1 s hs)
  · have he' : ∀ v, v ∈ Λ ↔ e.symm v ∈ Λ := fun v => by
      rw [he (e.symm v), LinearEquiv.apply_symm_apply]
    obtain ⟨s, ⟨hs, hs2⟩, hu⟩ := h2 _ (gen_map e.symm he' ht)
    refine ⟨ι s, ⟨Finset.mem_map_of_mem _ hs, fun j => ?_⟩, ?_⟩
    · have := (he _).1 (hs2 j)
      rwa [map_sub, LinearEquiv.apply_symm_apply] at this
    · rintro _ ⟨ht', h3⟩
      obtain ⟨s', hs', rfl⟩ := Finset.mem_map.1 ht'
      rw [hu s' ⟨hs', fun j => ?_⟩]
      rw [he, map_sub, LinearEquiv.apply_symm_apply]
      exact h3 j

variable [IsCMField E]

theorem contDiffOn_cpt (X : Data E r) (x0 : Frame X.Ψ r) {F : Frame X.Ψ r → ℂ}
    (hF : DifferentiableOn ℂ F X.dom) : ContDiffOn ℝ ∞ (fun z => F (cpt X x0 z)) (OmF X x0) := by
  have hc : Differentiable ℂ (cpt X x0) :=
    differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b =>
      (IW.cpt_entry_cd X x0 τ a b).differentiable (by simp)
  exact (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn _ _ _ (ExF.isOpen_OmF X x0)
    (hF.comp hc.differentiableOn fun z hz => hz)).restrict_scalars ℝ

theorem contDiffOn_nfac (X : Data E r) (x0 : Frame X.Ψ r) (la : Wt X.Ψ r) :
    ContDiffOn ℝ ∞ (fun z => X.nfac la (cpt X x0 z)) (OmF X x0) := by
  have h : ContDiffOn ℝ ∞ (fun z => Real.exp (phla X la (cpt X x0 z) / (-2))) (OmF X x0) :=
    fun z hz => ((IW.phla_cpt_cdAt X x0 hz la).div_const _).exp.contDiffWithinAt
  refine h.congr fun z hz => ?_
  rw [phla, mul_div_cancel_left₀ _ (by norm_num), Real.exp_log (flowTermNormDecay.nfac_pos X la hz)]

theorem log_theta_sum_invariant_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : DataX E r), (∃ ξ : Fin r → E, X.toData.IsIso ξ) → (∃ w0 : 𝓞 E, ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ, Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - cc (w0 : E)) • v)) - Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k) → ∀ ps : Frame X.Ψ r → ℝ, (∀ x ∈ X.dom, ∃ A : TorusAt X.toData x, ps x = Real.log (∑ᶠ (a : Fin A.T.r → Vsp A.T.dim) (_ : a ∈ {a : Fin A.T.r → Vsp A.T.dim | (∀ j, a j ∈ ZSpan.fundamentalDomain A.T.b) ∧ (∀ j, ((5 : ℂ) ^ 2) • a j ∈ A.T.L) ∧ ∀ x ∈ A.T.L, ∃ c : Fin A.T.r → 𝓞 E, ∃ y ∈ A.T.L, x = ∑ j, act (c j) (((5 : ℂ) ^ 2) • a j) + (5 : ℂ) • y}), ∏ b, A.T.ptN2 1 A.s (fun _ => a b) / A.T.l2 1 A.s)) → IsInvFn X.toData ps ∧ ∀ x0 ∈ X.dom, ContDiffOn ℝ ∞ (fun z => ps (cpt X.toData x0 z)) {z | cpt X.toData x0 z ∈ X.dom} := by
  intro E _ _ _ r X _ hw ps hps
  obtain ⟨𝒯, h1, h2⟩ := exists_reps X.Λ X.Λ_fg
  refine ⟨fun γ hγ x hx b hb => ?_, fun x0 _ => ?_⟩
  · have hs := X.Γ_stab γ hγ
    have hy := MajInv.lact_mem_dom X.toData hs (OrthogonalFrameDomain.rmul_mem_dom X.toData hx hb)
    obtain ⟨A, hA⟩ := hps x hx
    obtain ⟨A', hA'⟩ := hps _ hy
    obtain ⟨𝒯', h1', h2', h3⟩ := exists_reps_map (Matrix.GeneralLinearGroup.toLin γ).toLinearEquiv
      hs.2 𝒯 h1 h2
    rw [hA, hA', sum_eq hx A 𝒯 h1 h2 _ (torus_r A), sum_eq hy A' 𝒯' h1' h2' _ (torus_r A'), h3]
    congr 1
    refine Finset.sum_congr rfl fun t _ => Finset.prod_congr rfl fun j _ => ?_
    exact (ThetaRho.normalised_theta_norm_invariant E r X hw x hx b hb γ hs A A' (t j)).1
  · obtain ⟨Θ, D, κ, -, hΘ, hD, hD0, hf⟩ := ThetaHol.normalised_theta_norm_holomorphic E r X hw
    have key : ∀ x ∈ X.dom, 0 < ∑ t ∈ 𝒯, ∏ j, κ * ‖Θ (t j) x‖ ^ 2 * ‖D x‖ *
          X.nfac (fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1) x ∧
        ps x = Real.log (∑ t ∈ 𝒯, ∏ j, κ * ‖Θ (t j) x‖ ^ 2 * ‖D x‖ *
          X.nfac (fun _ j => if X.p0 ≤ (j : ℕ) then 1 else -1) x) := by
      intro x hx
      obtain ⟨A, hA⟩ := hps x hx
      have hp := TupleSumPos.tuple_sum_pos E r X x A
      rw [sum_eq hx A 𝒯 h1 h2 _ (torus_r A)] at hA hp
      simp only [hf x hx A] at hA hp
      exact ⟨hp, hA⟩
    refine ContDiffOn.congr (ContDiffOn.log ?_ fun z hz => (key _ hz).1.ne') fun z hz => (key _ hz).2
    refine ContDiffOn.sum fun t _ => contDiffOn_prod fun j _ => ?_
    exact ((contDiffOn_const.mul ((contDiffOn_cpt X.toData x0 (hΘ _)).norm_sq ℂ)).mul
      ((contDiffOn_cpt X.toData x0 hD).norm ℂ fun z hz => hD0 _ hz)).mul
      (contDiffOn_nfac X.toData x0 _)

end GlobalTheory.ThetaLogSum
