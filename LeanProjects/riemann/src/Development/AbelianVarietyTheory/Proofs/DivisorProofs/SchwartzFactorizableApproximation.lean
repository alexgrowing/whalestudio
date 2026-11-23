import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelArchimedeanUnipotentSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFourierOpenSubgroupSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactSupportPartialFourierIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallUnitaryPreservesSchwartzSupportStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupInNeighbourhoodStatement
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.FixPure

open GlobalTheory.WeilM GlobalTheory.AdelicU Filter Topology ComplexConjugate

open scoped Classical in

theorem continuous_eval {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ}
    {χX χW : Chr F E} {om : Rep σ X W} (hW : M.IsWeil ψ χX χW om) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) (x0 : Fin n × Fin d → AF F) :
    Continuous fun p : UA σ X.J × UA σ W.J => om p Φ x0 := by
  have hl : (LinearMap.proj x0 : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm (Fin n × Fin d) := by
    intro g _
    refine ⟨g (fun i => (x0 i).2) • ((BoundedContinuousFunction.evalCLM ℂ
      (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x0 i).1)).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)), fun f => ?_⟩
    simp only [LinearMap.proj_apply, pureA, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
    rw [mul_comm]
    rfl
  exact hW.2.2 _ hl Φ hΦ

theorem fix_schA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    {r s r' s' : ℕ} (hP : GlobalTheory.ThK.IsPair B M χX χW om r s r' s') (Φ : (Fin n × Fin d → AF F) → ℂ)
    (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    ∃ U : Subgroup (UA σ W.J), IsOpen (U : Set (UA σ W.J)) ∧ ∀ k ∈ U,
      (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 → om (1, k) Φ = Φ := by
  classical
  letI : MeasurableSpace (Fin n × Fin d → AF F) := borel _
  haveI : BorelSpace (Fin n × Fin d → AF F) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  by_cases h0 : Φ = 0
  · exact ⟨⊤, isOpen_univ, fun k _ _ => by rw [h0, map_zero]⟩
  obtain ⟨x0, hx0⟩ := Function.ne_iff.1 h0
  have hx0' : Φ x0 ≠ 0 := hx0
  have hF : IsTotallyReal F := hP.base.cm.1
  have hψ := GlobalTheory.StdCharFromIsStd.isCharAF hP.base.std
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hP.base.cm
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hP.weil
  obtain ⟨Mo, hMo, hper⟩ := GlobalTheory.T.partial_fourier_open_subgroup_support B.ψ hP.base.std Φ hΦ
  obtain ⟨K, hK, hsupp⟩ := GlobalTheory.T.compact_support_partial_fourier_integral B.ψ hP.base.std Φ hΦ
  have hS2 := GlobalTheory.T.small_unitary_preserves_schwartz_support σ X W M Mo K hMo hK
  have hc : Continuous fun k : UA σ W.J => om (1, k) Φ x0 :=
    (continuous_eval hP.weil Φ hΦ x0).comp (continuous_const.prodMk continuous_id)
  have hnear : ∀ᶠ k in 𝓝 (1 : UA σ W.J), ‖om (1, k) Φ x0 / Φ x0 - 1‖ < 1 / 2 := by
    refine (((hc.div_const _).sub continuous_const).norm.continuousAt (x := 1)).eventually_lt continuousAt_const ?_
    have e1 : om ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 := map_one om
    show ‖om ((1 : UA σ X.J), (1 : UA σ W.J)) Φ x0 / Φ x0 - 1‖ < 1 / 2
    rw [e1, Module.End.one_apply, div_self hx0', sub_self, norm_zero]
    norm_num
  have hi : Tendsto (fun k : UA σ W.J => k⁻¹) (𝓝 1) (𝓝 1) := by
    have := (continuous_inv (G := UA σ W.J)).tendsto 1
    rwa [inv_one] at this
  obtain ⟨U, hUo, hUN⟩ := GlobalTheory.T.exists_open_subgroup_in_neighbourhood σ hσ W.J _ ((hS2.and (hi.eventually hS2)).and hnear)
  have hfinv : ∀ k : UA σ W.J, (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 →
      (mat k⁻¹).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 := by
    intro k hk
    have e : mat k⁻¹ * mat k = 1 := by
      show ((k⁻¹ * k : UA σ W.J) : GL (Fin d) (AE F E)).1 = 1
      rw [inv_mul_cancel]; rfl
    have h1 : (mat k⁻¹ * mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) =
        (mat k⁻¹).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) *
          (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) :=
      Matrix.map_mul (f := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom)
    rw [e, Matrix.map_one _ (map_zero _) (map_one _), hk, mul_one] at h1
    exact h1.symm
  have hfpow : ∀ k : UA σ W.J, (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 → ∀ m : ℕ,
      (mat (k ^ m)).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 := by
    intro k hk m
    induction m with
    | zero =>
      show ((1 : UA σ W.J) : GL (Fin d) (AE F E)).1.map _ = 1
      exact Matrix.map_one _ (map_zero _) (map_one _)
    | succ m ih =>
      have e : mat (k ^ (m + 1)) = mat (k ^ m) * mat k := by
        show ((k ^ m * k : UA σ W.J) : GL (Fin d) (AE F E)).1 = _
        rfl
      have h1 : (mat (k ^ m) * mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) =
          (mat (k ^ m)).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) *
            (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) :=
        Matrix.map_mul (f := (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)).toRingHom)
      rw [e, h1, ih, hk, mul_one]
  have key : ∀ k ∈ U, (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 →
      om (1, k) Φ = (om (1, k) Φ x0 / Φ x0) • Φ := by
    intro k hk hfk
    obtain ⟨⟨hPk, hPk'⟩, -⟩ := hUN k hk hfk
    have hfk' := hfinv k hfk
    obtain ⟨c1, b1, i1⟩ := GlobalTheory.SplitSvN.schA_facts hF hΦ
    obtain ⟨c2, b2, i2⟩ := GlobalTheory.SplitSvN.schA_facts hF (hW.pres (1, k) Φ hΦ)
    obtain ⟨c, hc⟩ := GlobalTheory.SplitSvN.proportional_of_coeff B.ψ hψ.1 hψ.2.1
      (GlobalTheory.SWQ.Annihilator.self_annihilator F hF B.ψ hψ).1 1 (one_mul 1) Φ (om (1, k) Φ) (fun _ => 1) Φ (om (1, k) Φ)
      (fun x => by simp) (fun x => by simp) c1 c2 b1 b2 i1 i2 (fun x₁ y₁ _ _ μ hμ => by
        set w : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) := (x₁, y₁) with hw
        set u := M.co.e.symm w with hu
        set u' := actAB (cA σ) ((1 : UA σ X.J), k⁻¹) u with hu'
        have hact : actAB (cA σ) ((1 : UA σ X.J), k) u' = u := by
          have e2 : mat k * mat k⁻¹ = 1 := by
            show ((k * k⁻¹ : UA σ W.J) : GL (Fin d) (AE F E)).1 = 1
            rw [mul_inv_cancel]; rfl
          change (1 : Matrix (Fin n) (Fin n) (AE F E)) * ((1 : Matrix (Fin n) (Fin n) (AE F E)) * u * Matrix.transpose (mat k⁻¹)) * Matrix.transpose (mat k) = u
          rw [Matrix.one_mul, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, e2, Matrix.transpose_one,
            Matrix.mul_one]
        have e1 : schr B.ψ w (om (1, k) Φ) = om (1, k) (M.co.rho B.ψ u' Φ) := by
          rw [hW.impl (1, k) u' Φ hΦ, hact]
          simp only [Darboux.rho, hu, LinearEquiv.apply_symm_apply]
        show ∫ x, om (1, k) Φ x * conj (schr B.ψ w (om (1, k) Φ) x) ∂μ = ∫ x, Φ x * conj (schr B.ψ w Φ x) ∂μ
        rw [e1, GlobalTheory.CptCoeff.integral_mul_conj_map (μ := μ) (schA F _) (fun f hf => GlobalTheory.T.adelic_schwartz_mem_L2 F _ μ hμ f hf)
          (om (1, k)) (fun f hf => hW.pres _ f hf) (fun f hf => hW.unit μ hμ _ f hf) hΦ
          (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hP.base.std u' Φ hΦ)]
        show ∫ x, Φ x * conj (schr B.ψ (M.co.e u') Φ x) ∂μ = _
        by_cases hcw : ∫ x, Φ x * conj (schr B.ψ w Φ x) ∂μ = 0
        · by_cases hcw2 : ∫ x, Φ x * conj (schr B.ψ (M.co.e u') Φ x) ∂μ = 0
          · rw [hcw, hcw2]
          · obtain ⟨h1, h2⟩ := hsupp μ hμ _ hcw2
            obtain ⟨ha, hb1, hb2⟩ := hPk hfk _ h1 h2
            have hback : M.co.e (actAB (cA σ) ((1 : UA σ X.J), k) (M.co.e.symm (M.co.e u'))) = w := by
              rw [LinearEquiv.symm_apply_apply, hact, hu, LinearEquiv.apply_symm_apply]
            rw [hback] at ha hb1 hb2
            have := hper μ hμ (M.co.e u') (w - M.co.e u') ha hb1 hb2
            rw [add_sub_cancel] at this
            exact this.symm
        · obtain ⟨h1, h2⟩ := hsupp μ hμ w hcw
          obtain ⟨ha, hb1, hb2⟩ := hPk' hfk' w h1 h2
          have := hper μ hμ w (M.co.e u' - w) ha hb1 hb2
          rwa [add_sub_cancel] at this)
    have hcx : c = om (1, k) Φ x0 / Φ x0 := by
      rw [hc, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hx0']
    conv_lhs => rw [hc]
    rw [hcx]
  refine ⟨U, hUo, fun k hk hfk => ?_⟩
  set c := om (1, k) Φ x0 / Φ x0 with hcdef
  have hpow : ∀ m : ℕ, om (1, k ^ m) Φ = c ^ m • Φ := by
    intro m
    induction m with
    | zero =>
      rw [pow_zero, pow_zero, one_smul]
      exact congrArg (· Φ) (map_one om)
    | succ m ih =>
      have e : ((1 : UA σ X.J), k ^ (m + 1)) = ((1 : UA σ X.J), k ^ m) * (1, k) := by
        rw [Prod.mk_mul_mk, one_mul, pow_succ]
      rw [e, map_mul, Module.End.mul_apply, key k hk hfk, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hc1 : c = 1 := GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le fun m => by
    have hm := (hUN (k ^ m) (pow_mem hk m) (hfpow k hfk m)).2
    rw [hpow m, Pi.smul_apply, smul_eq_mul, mul_div_cancel_right₀ _ hx0'] at hm
    exact hm.le
  rw [key k hk hfk, ← hcdef, hc1, one_smul]

theorem fix_pure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.KP → GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      ∃ U : Subgroup (UA σ W.J), IsOpen (U : Set (UA σ W.J)) ∧ ∀ k ∈ U,
        (mat k).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 → om (1, k) (pure f φ) = pure f φ := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' _ hP f φ hφ hvac
  have hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
    filter_upwards [hvac, hP.good.std] with v h1 h2
    rw [h1, h2]
  exact fix_schA hP _ (GlobalTheory.TensUniq.pure_mem_schA f φ hφ hstd)

end GlobalTheory.FixPure
