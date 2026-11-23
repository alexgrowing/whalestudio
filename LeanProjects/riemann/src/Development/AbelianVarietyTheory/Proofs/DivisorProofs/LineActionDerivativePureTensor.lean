import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormAdelicThetaSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ImportsExtra

noncomputable section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open Filter Topology
open scoped Classical

namespace GlobalTheory.ThKKernelLine

theorem finprod_add_of_at {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (x z : κ → AF F) (hz : At (evI F) z) :
    (∏ᶠ v, φ v fun i => evFin F v ((x + z) i)) = ∏ᶠ v, φ v fun i => evFin F v (x i) := by
  let u : AF F := (show InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F from (0, 1))
  have hu : evI F u = 0 := by
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : InfiniteAdeleRing F) = 0
    exact map_zero _
  have h2 : ∀ v i, evFin F v (z i) = 0 := by
    intro v i
    have h1 : evFin F v u = 1 := by
      show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (1 : FiniteAdeleRing (𝓞 F) F) = 1
      exact map_one _
    have := congrArg (evFin F v) (congrFun (hz u hu) i)
    simpa [h1] using this
  refine finprod_congr fun v => congrArg (φ v) (funext fun i => ?_)
  rw [Pi.add_apply, map_add, h2 v i, add_zero]

theorem hasDerivAt_theta_pure (hP : GlobalTheory.FunPr.Hypotheses₂) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (ψ : AddChar (AF F) ℂ)
    (χY χW : Chr F E) (om : Rep σ Y W) (hcm : IsCMExt F E σ) (hψ : IsStd ψ) (hM : M.IsGood ψ) (hw : M.IsWeil ψ χY χW om)
    {γ : Multiplicative ℝ →* UA σ W.J} (hγ : γ ∈ Lines σ W) (f f₁ : SInf F (Fin n × Fin d))
    (hD : ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁)
    (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _)
    (hvac : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) (g : UA σ Y.J) (h : UA σ W.J) :
    HasDerivAt (fun s : ℝ => theta om (pure f φ) g (h * γ (Multiplicative.ofAdd s))) (theta om (pure f₁ φ) g h) 0 := by
  obtain ⟨c, c', h0, hlim, hacts⟩ := GlobalTheory.WeilArchSmooth.exists_orbit hP M ψ χY χW om hcm hψ hw γ hγ f
  have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (hvac.and hM.std).mono fun v h => h.1.trans h.2
  have hmem : ∀ u : SInf F (Fin n × Fin d), pure u φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun u => GlobalTheory.TensUniq.pure_mem_schA u φ hSB hstd
  have hR : Rest (evI F) (⇑f) (fun x : Fin n × Fin d → AF F => ∏ᶠ v, φ v fun i => evFin F v (x i)) :=
    ⟨fun x z hz => finprod_add_of_at φ x z hz, hmem f⟩
  have hc : ∀ t : ℝ, om (1, γ (Multiplicative.ofAdd t)) (pure f φ) = pure (c t) φ := fun t => hacts t _ hR
  have hfin : (fun y : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
      GlobalTheory.WeilM.SB _ :=
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hSB hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hstd⟩
  have hS := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw
  obtain ⟨l, hl, hlt⟩ := GlobalTheory.WeilM.exists_adm_eq_thetaSum_of_locallyCompact F (Fin n × Fin d)
  obtain ⟨T, hT⟩ := hS.adm (g, h) l hl _ hfin
  have hTθ : ∀ u : SInf F (Fin n × Fin d), theta om (pure u φ) g h = T u := fun u => by
    simp only [theta]
    rw [← hlt _ (hS.pres _ _ (hmem u))]
    exact hT u

  have hg : pure c' φ = pure f₁ φ := by
    funext x
    have h1 := hD _ hR x
    have ev : Continuous fun s : SInf F (Fin n × Fin d) => s (fun j => evI F (x j)) :=
      (continuous_eval_const (F := BoundedContinuousFunction (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)
        (fun j => evI F (x j))).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ).continuous
    have h2 : HasDerivAt (fun t : ℝ => c t (fun j => evI F (x j)) * ∏ᶠ v, φ v fun j => evFin F v (x j))
        (c' (fun j => evI F (x j)) * ∏ᶠ v, φ v fun j => evFin F v (x j)) 0 := by
      rw [hasDerivAt_iff_tendsto_slope]
      refine (((ev.tendsto c').comp hlim).mul_const _).congr' (Filter.Eventually.of_forall fun t => ?_)
      rw [slope_def_module, h0]
      simp only [Function.comp_apply, SchwartzMap.smul_apply, SchwartzMap.sub_apply, sub_zero, Complex.real_smul]
      ring
    have h3 : (fun t : ℝ => c t (fun j => evI F (x j)) * ∏ᶠ v, φ v fun j => evFin F v (x j)) =
        fun t => om (1, γ (Multiplicative.ofAdd t))
          (tens (evI F) (⇑f) (fun x => ∏ᶠ v, φ v fun j => evFin F v (x j))) x := by
      funext t
      show pure (c t) φ x = om (1, γ (Multiplicative.ofAdd t)) (pure f φ) x
      rw [hc t]
    rw [h3] at h2
    exact h2.unique h1
  have hcurve : (fun s : ℝ => theta om (pure f φ) g (h * γ (Multiplicative.ofAdd s))) = fun s => T (c s) := by
    funext s
    rw [← hTθ, ← hc]
    simp only [theta]
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  rw [hcurve, ← hg, hTθ, hasDerivAt_iff_tendsto_slope]
  refine ((T.continuous.tendsto c').comp hlim).congr' (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply, slope_def_module, h0, sub_zero, ← Complex.coe_smul, map_smul, map_sub]

theorem hasDerivAt_theta_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    GlobalTheory.ThK.KP → IsTriple B G X om om' → ∀ γ ∈ Lines σ G.W, ∀ f ∈ G.M.Pol B.ψ B.emb,
    ∀ f₁ : SInf F (Fin a × Fin (a + a')), ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁ →
    ∀ φ : ∀ v : Pl F, (Fin a × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
    (∀ᶠ v in Filter.cofinite, φ v = G.M.vac v) → ∀ g h,
    HasDerivAt (fun s : ℝ => theta om (pure f φ) g (h * γ (Multiplicative.ofAdd s))) (theta om (pure f₁ φ) g h) 0 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hKP hT γ hγ f _ f₁ hD φ hSB hvac g h
  exact hasDerivAt_theta_pure hKP.base G.M B.ψ _ _ om hT.base.cm hT.base.std hT.geo.hM hT.weil hγ f f₁ hD φ hSB hvac g h

end GlobalTheory.ThKKernelLine
