import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSkewComplement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplitBasisCompl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedBasisHermitianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesGoodModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedBasisHermitianUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRestrictionExtendByZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchAStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroSchwartzBruhatMapStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKIsoEv

open GlobalTheory.ThKMixXEx in

theorem exists_isEv_iso : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ →
    M₂.IsGood B.ψ → B.IsGood σ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    ∃ e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁, IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e' := by
  intro _ F E _ _ _ _ _ σ B n d d₁ X W W₁ M H' i₀ i₁ hH' hM n₁ X₁ H j₀ j₁ M₁ hH hM₁ hB hXW
  classical
  obtain ⟨r, s, r', s', hX, hW⟩ := hXW
  have hW₁ := GlobalTheory.ThK.KernelZero.isSkew_complement F E σ B hB d d₁ W W₁ H' i₀ i₁ r' s' hW hH'
  have hX₁ : X₁.IsHerm σ B (r - 1) (s - 1) := GlobalTheory.HermPlaneCompl.isHerm_compl hB hX hH
  obtain ⟨j, co, hj, hrat, hι, hx, hy⟩ :=
    GlobalTheory.T.exists_adapted_basis_hermitian F E σ B n d₁ X W₁ r s (r' - 1) (s' - 1) hB hX hW₁ n₁ X₁ H j₀ j₁ M₁ (r - 1) (s - 1) hX₁ hH hM₁
  obtain ⟨e₁, ei₁, ev₁, hsurj, hmaps, hheis, hSB, hvac, hstd, hpure⟩ :=
    GlobalTheory.T.darboux_coordinates_good_model F E σ B n d₁ X W₁ M r s (r' - 1) (s' - 1) hB hX hW₁ hM co hrat
  have hres := fun v => GlobalTheory.T.adapted_basis_hermitian_unique F E σ B n d₁ X W₁ r s (r' - 1) (s' - 1) hB hX hW₁ n₁ X₁ H j₀ j₁ M₁ (r - 1) (s - 1) hX₁ hH
    hM₁ j co hj hι hx hy v _ (hvac v)
  choose c hc0 hc using hres
  have hc1 : ∀ᶠ v in cofinite, c v = 1 := by
    filter_upwards [hstd, hM₁.std] with v h1 h2
    have h' := hc v
    rw [h1, h2, std_extend hj v] at h'
    have h := congrFun h' 0
    have hm : (0 : Fin n₁ × Fin d₁ → Fv F v) ∈ {x : Fin n₁ × Fin d₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} :=
      fun i => zero_mem _
    rw [Pi.smul_apply, Set.indicator_of_mem hm, smul_eq_mul] at h
    simpa using h.symm
  obtain ⟨R, hR⟩ := GlobalTheory.T.exists_restriction_extend_by_zero F j hj
  refine ⟨(∏ᶠ v, c v)⁻¹ • (LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d₁ → AF F => Function.extend j y 0) ∘ₗ e₁),
    ⟨?_, ?_, ?_, ?_⟩⟩
  · intro Φ hΦ
    exact Submodule.smul_mem _ _ (GlobalTheory.T.extend_by_zero_mem_schA F j hj _ (hmaps Φ hΦ))
  · intro z Φ hΦ
    have h1 : incM F H.ι * z * (incM F (1 : Matrix (Fin d₁) (Fin d₁) E))ᵀ = incM F H.ι * z := by
      rw [show incM F (1 : Matrix (Fin d₁) (Fin d₁) E) = 1 from Matrix.map_one _ (map_zero _) (map_one _)]
      simp
    rw [h1]
    funext y
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, Function.comp_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [hheis _ Φ hΦ]
    simp only [Darboux.rho, schr, hι, extend_dot hj, ← extend_add hj, Pi.smul_apply, smul_eq_mul,
      LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, Function.comp_apply]
    ring
  · intro u hu Φ hΦ
    obtain ⟨z, rfl⟩ := hu
    funext y
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.funLeft_apply, Function.comp_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [hheis _ Φ hΦ]
    obtain ⟨h1, h2⟩ := hx z
    simp only [Darboux.rho, schr, h1, extend_dot_zero _ _ h2, zero_dotProduct, mul_zero, add_zero,
      AddChar.map_zero_eq_one, one_mul]
  · obtain ⟨b, hb0⟩ : ∃ b : SInf F (Fin n × Fin d₁), b 0 ≠ 0 := by
      let bb : ContDiffBump (0 : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
      have hs : HasCompactSupport (fun x => ((bb x : ℝ) : ℂ)) :=
        bb.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
      have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((bb x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp bb.contDiff
      refine ⟨hs.toSchwartzMap hcd, ?_⟩
      have h2 : bb 0 = 1 := bb.one_of_mem_closedBall (by simp [bb])
      simp [h2]
    obtain ⟨f₀, hf₀⟩ := hsurj b
    refine ⟨R.comp ei₁, fun v => (c v)⁻¹ •
      (LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d₁ → Fv F v => Function.extend j y 0) ∘ₗ ev₁ v), ?_, ?_, ?_⟩
    · intro h
      have := congrArg (fun T : SInf F (Fin n × Fin d₁) →L[ℂ] SInf F (Fin n₁ × Fin d₁) => T f₀ 0) h
      simp only [ContinuousLinearMap.comp_apply, hR, hf₀, extend_zero' hj, ContinuousLinearMap.zero_apply,
        SchwartzMap.zero_apply] at this
      exact hb0 this
    · intro v
      refine ⟨?_, ?_⟩
      · rw [LinearMap.smul_apply, LinearMap.comp_apply]
        rw [show LinearMap.funLeft ℂ ℂ (fun y : Fin n₁ × Fin d₁ → Fv F v => Function.extend j y 0) (ev₁ v (M.vac v)) =
          c v • M₁.vac v from hc v, smul_smul, inv_mul_cancel₀ (hc0 v), one_smul]
      · rw [Submodule.map_smul _ _ _ (inv_ne_zero (hc0 v)), Submodule.map_comp, hSB v, GlobalTheory.T.extend_by_zero_schwartzBruhat_map F j hj v]
    · intro f φ hφ hφv
      funext y
      rw [LinearMap.smul_apply, LinearMap.comp_apply, hpure f φ hφ hφv]
      simp only [LinearMap.funLeft_apply, Function.comp_apply, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure,
        ContinuousLinearMap.comp_apply, hR, LinearMap.smul_apply, LinearMap.comp_apply]
      have hI : (fun i => evI F (Function.extend j y 0 i)) = Function.extend j (fun i => evI F (y i)) 0 :=
        extend_map hj (evI F) (by unfold evI; exact map_zero _) y
      have hF : ∀ v : Pl F, (fun i => evFin F v (Function.extend j y 0 i)) =
          Function.extend j (fun i => evFin F v (y i)) 0 := fun v => extend_map hj _ (map_zero _) y
      simp only [hI, hF]
      have hfin1 : (Function.mulSupport fun v : Pl F => (c v)⁻¹).Finite := by
        refine (Filter.eventually_cofinite.1 hc1).subset fun v hv h => hv ?_
        simp [h]
      have hfin2 : (Function.mulSupport fun v : Pl F =>
          ev₁ v (φ v) (Function.extend j (fun i => evFin F v (y i)) 0)).Finite := by
        have := GlobalTheory.PureFactor.mulSupport_finite (κ := Fin n₁ × Fin d₁)
          (fun v x => ev₁ v (φ v) (Function.extend j x 0)) (by
            filter_upwards [hφv, hstd] with v h1 h2
            rw [h1, h2]
            exact std_extend hj v) y
        exact this
      rw [finprod_mul_distrib hfin1 hfin2, finprod_inv_distrib]
      ring

end GlobalTheory.ThKIsoEv

end
