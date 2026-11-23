import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFactorizableApproximation
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer
open GlobalTheory.DblDatum

noncomputable section
namespace GlobalTheory.DblFinSmooth

open ComplexConjugate

theorem fst_eq_one_of_mem_UAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {m : ℕ} (X : Spc F E m) (g : UA σ X.J) (hg : g ∈ UAt σ X (sndA F)) :
    (mat g).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 := by
  let a : AF F := ((1 : Ainf F), (0 : Af F))
  have ha : sndA F a = 0 := rfl
  have h0 : a • (mat g - 1) = 0 := hg a ha
  have hfa : fstA F a = 1 := rfl
  have key : ∀ x : AE F E, Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (a • x) =
      Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) x := by
    intro x
    rw [Algebra.smul_def, map_mul]
    have : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (algebraMap (AF F) (AE F E) a) = 1 := by
      show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (a ⊗ₜ[F] (1 : E)) = 1
      rw [Algebra.TensorProduct.map_tmul, hfa]; rfl
    rw [this, one_mul]
  ext i j
  have hij := congrFun (congrFun h0 i) j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply] at hij
  have := congrArg (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) hij
  rw [key, map_zero, map_sub] at this
  have e1 : (1 : Matrix (Fin m) (Fin m) (AE F E)).map (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  rw [Matrix.map_apply, ← sub_eq_zero, ← e1, Matrix.map_apply]
  exact this

theorem fix_schA_of_weil {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    (hB : B.IsGood σ) (hweil : M.IsWeil B.ψ χX χW om) (Φ : (Fin n × Fin d → AF F) → ℂ)
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
  have hF : IsTotallyReal F := hB.cm.1
  have hψ := GlobalTheory.StdCharFromIsStd.isCharAF hB.std
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hB.cm
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hweil
  obtain ⟨Mo, hMo, hper⟩ := GlobalTheory.T.partial_fourier_open_subgroup_support B.ψ hB.std Φ hΦ
  obtain ⟨K, hK, hsupp⟩ := GlobalTheory.T.compact_support_partial_fourier_integral B.ψ hB.std Φ hΦ
  have hS2 := GlobalTheory.T.small_unitary_preserves_schwartz_support σ X W M Mo K hMo hK
  have hc : Continuous fun k : UA σ W.J => om (1, k) Φ x0 :=
    (GlobalTheory.FixPure.continuous_eval hweil Φ hΦ x0).comp (continuous_const.prodMk continuous_id)
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
          (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hB.std u' Φ hΦ)]
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

theorem fix_near_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ →
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F Xs.J) (incM F W₂.J)) (Fin n × Fin (d + d)),
      (∀ x : Matrix (Fin n) (Fin (d + d)) E, ∃ y z : Fin n × Fin (d + d) → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      (∀ u, (∀ i, u i ∈ diagSub (AE F E) finSumFinEquiv) → (co.e u).1 = 0) →
      (∀ u, (∀ i, u i ∈ antiSub (AE F E) finSumFinEquiv) → (co.e u).2 = 0) →
    ∀ om₂ : Rep σ Xs W₂, IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F Xs.J) (incM F W₂.J) co χX 1 om₂ →
    ∀ Ψ ∈ schA F (Fin n × Fin (d + d)), ∃ N ∈ 𝓝 (1 : UA σ W₂.J), ∀ u ∈ N, u ∈ UAt σ W₂ (sndA F) → om₂ (1, u) Ψ = Ψ := by
  intro F E _ _ _ _ _ σ B n d Xs W M χX χW om r s' r₁ s₁ hP W₂ _ _ _ co _ _ _ om₂ hweil Ψ hΨ
  let M₂ : Model σ Xs W₂ := ⟨co, fun _ _ => 0, 0, ∅⟩
  obtain ⟨U, hUo, hU⟩ := fix_schA_of_weil (M := M₂) (χW := 1) (om := om₂) hP.base hweil Ψ hΨ
  exact ⟨U, hUo.mem_nhds U.one_mem, fun u hu hfin => hU u hu (fst_eq_one_of_mem_UAt W₂ u hfin)⟩

end GlobalTheory.DblFinSmooth
