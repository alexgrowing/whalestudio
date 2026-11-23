import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombRSingleNil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmissibleFormAdelicThetaSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelPolynomial

noncomputable section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.FiniteLevelDerivatives
open Filter Topology
open scoped Classical

namespace GlobalTheory.ThK.KernelLineLeft

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

theorem exists_deriv_pure (hP : GlobalTheory.FunPr.Hypotheses₂) {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (M : Model σ Y W) (ψ : AddChar (AF F) ℂ)
    (χY χW : Chr F E) (om : Rep σ Y W) (hψ : IsStd ψ) (hM : M.IsGood ψ) (hw : M.IsWeil ψ χY χW om)
    {γ : Multiplicative ℝ →* UA σ Y.J} (hγ : γ ∈ Lines σ Y) (f : SInf F (Fin n × Fin d))
    (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _)
    (hvac : ∀ᶠ v in Filter.cofinite, φ v = M.vac v)
    (l : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ) (hl : l ∈ (GlobalTheory.WeilM.adeleClass F).adm (Fin n × Fin d))
    (p : UA σ Y.J × UA σ W.J) :
    pure f φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) ∧ ∃ Ψ' ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d),
      (∀ y, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) (pure f φ) y) (Ψ' y) 0) ∧
      HasDerivAt (fun t : ℝ => l (om p (om (γ (Multiplicative.ofAdd t), 1) (pure f φ)))) (l (om p Ψ')) 0 := by
  have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (hvac.and hM.std).mono fun v h => h.1.trans h.2
  have hmem : ∀ u : SInf F (Fin n × Fin d), pure u φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) :=
    fun u => GlobalTheory.TensUniq.pure_mem_schA u φ hSB hstd
  have hR : Rest (evI F) (⇑f) (fun x : Fin n × Fin d → AF F => ∏ᶠ v, φ v fun i => evFin F v (x i)) :=
    ⟨fun x z hz => finprod_add_of_at φ x z hz, hmem f⟩
  obtain ⟨c, c', hacts, hlim⟩ := GlobalTheory.ArchLinePair.exists_curve_lineY hP M ψ χY χW om hψ hM hw γ hγ f _ hR
  have hc : ∀ t : ℝ, om (γ (Multiplicative.ofAdd t), 1) (pure f φ) = pure (c t) φ := fun t => hacts t
  have hfin : (fun y : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (y i)) ∈
      GlobalTheory.WeilM.SB _ :=
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hSB hstd, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hSB hstd⟩
  have hS := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hw
  obtain ⟨T, hT⟩ := hS.adm p l hl _ hfin
  have hTθ : ∀ u : SInf F (Fin n × Fin d), l (om p (pure u φ)) = T u := fun u => hT u
  refine ⟨hmem f, pure c' φ, hmem c', fun x => ?_, ?_⟩
  · have ev : Continuous fun s : SInf F (Fin n × Fin d) => s (fun j => evI F (x j)) :=
      (continuous_eval_const (F := BoundedContinuousFunction (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)
        (fun j => evI F (x j))).comp
        (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ).continuous
    have h2 : HasDerivAt (fun t : ℝ => c t (fun j => evI F (x j)) * ∏ᶠ v, φ v fun j => evFin F v (x j))
        (c' (fun j => evI F (x j)) * ∏ᶠ v, φ v fun j => evFin F v (x j)) 0 := by
      rw [hasDerivAt_iff_tendsto_slope]
      refine (((ev.tendsto c').comp hlim).mul_const _).congr' (Filter.Eventually.of_forall fun t => ?_)
      rw [slope_def_module]
      simp only [Function.comp_apply, SchwartzMap.smul_apply, SchwartzMap.sub_apply, sub_zero, Complex.real_smul]
      ring
    simp only [hc]
    exact h2
  · simp only [hc, hTθ]
    rw [hasDerivAt_iff_tendsto_slope]
    refine ((T.continuous.tendsto c').comp hlim).congr' (Filter.Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply, slope_def_module, sub_zero, ← Complex.coe_smul, map_smul, map_sub]

theorem hasDerivAt_theta_lineLeft : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ Ψ ∈ GlobalTheory.ThK.PolData B G.M, ∀ γ ∈ Lines σ G.V, ∀ g h,
      HasDerivAt (fun t : ℝ => theta om Ψ (g * γ (Multiplicative.ofAdd t)) h)
        (theta om (derL om (fun t => γ (Multiplicative.ofAdd t)) Ψ) g h) 0 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hKP hT Ψ hΨ γ hγ g h
  have hS := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil
  obtain ⟨l, hl, hlt⟩ := GlobalTheory.WeilM.exists_adm_eq_thetaSum_of_locallyCompact F (Fin a × Fin (a + a'))
  have key : Ψ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')) ∧ ∃ Ψ' ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')),
      (∀ y, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) Ψ y) (Ψ' y) 0) ∧
      HasDerivAt (fun t : ℝ => l (om (g, h) (om (γ (Multiplicative.ofAdd t), 1) Ψ))) (l (om (g, h) Ψ')) 0 := by
    induction hΨ using Submodule.span_induction with
    | mem Φ hΦ =>
      obtain ⟨f, -, φ, hSB, hev, rfl⟩ := hΦ
      exact exists_deriv_pure hKP.base G.M B.ψ _ _ om hT.base.std hT.geo.hM hT.weil hγ f φ hSB hev l hl (g, h)
    | zero =>
      exact ⟨zero_mem _, 0, zero_mem _, fun y => by simpa using hasDerivAt_const (0:ℝ) (0:ℂ),
        by simpa using hasDerivAt_const (0:ℝ) (0:ℂ)⟩
    | add Φ₁ Φ₂ _ _ h₁ h₂ =>
      obtain ⟨s₁, Ψ₁, m₁, d₁, e₁⟩ := h₁
      obtain ⟨s₂, Ψ₂, m₂, d₂, e₂⟩ := h₂
      refine ⟨add_mem s₁ s₂, Ψ₁ + Ψ₂, add_mem m₁ m₂, fun y => ?_, ?_⟩
      · have h := (d₁ y).add (d₂ y)
        simp only [map_add, Pi.add_apply]
        exact h
      · have h := e₁.add e₂
        simp only [map_add]
        exact h
    | smul r Φ₁ _ h₁ =>
      obtain ⟨s₁, Ψ₁, m₁, d₁, e₁⟩ := h₁
      refine ⟨Submodule.smul_mem _ r s₁, r • Ψ₁, Submodule.smul_mem _ r m₁, fun y => ?_, ?_⟩
      · simpa [map_smul] using (d₁ y).const_mul r
      · simp only [map_smul, smul_eq_mul]
        exact e₁.const_mul r
  obtain ⟨hs, Ψ', hs', hd, hD⟩ := key
  have e1 : derL om (fun t => γ (Multiplicative.ofAdd t)) Ψ = Ψ' := funext fun y => (hd y).deriv
  have e2 : (fun t : ℝ => theta om Ψ (g * γ (Multiplicative.ofAdd t)) h) =
      fun t : ℝ => l (om (g, h) (om (γ (Multiplicative.ofAdd t), 1) Ψ)) := by
    funext t
    simp only [theta]
    rw [← hlt _ (hS.pres _ _ hs), ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have e3 : theta om Ψ' g h = l (om (g, h) Ψ') := by
    simp only [theta]
    rw [← hlt _ (hS.pres _ _ hs')]
  rw [e1, e2, e3]
  exact hD

end GlobalTheory.ThK.KernelLineLeft
