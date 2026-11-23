import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.AlgInjective

noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
open scoped Matrix

namespace PositivityTheory.SiegelWeilFormula.TBij

variable {F : Type} [Field F] [NumberField F]

theorem isOp_adm {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} {a : Matrix (κ ⊕ κ) (κ ⊕ κ) F}
    {e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ} {c : ℂ} {ei : SInf F κ →L[ℂ] SInf F κ}
    {ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ} (h : IsOp ψ a e c ei ev)
    (l : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) (hl : l ∈ (adeleClass F).adm κ) : l ∘ₗ e ∈ (adeleClass F).adm κ := by
  have hfamOf : ∀ φ : (v : Pl F) → (κ → Fv F v) → ℂ, (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in Filter.cofinite, φ v = {x : κ → Fv F v | ∀ i, x i ∈
        IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v}.indicator 1) → IsFam φ :=
    fun φ h1 h2 => ⟨h1, h2⟩
  have hSB : ∀ φ : (v : Pl F) → (κ → Fv F v) → ℂ, IsFam φ →
      (fun y : κ → Af F => ∏ᶠ v, φ v fun i => evalV F v (y i)) ∈ SB (κ → Af F) := by
    intro φ hφ
    exact ⟨isLocallyConstant_finprod_evalV φ hφ.1 hφ.2,
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hφ.1 hφ.2⟩
  have hpure : ∀ (f : SInf F κ) (φ : (v : Pl F) → (κ → Fv F v) → ℂ),
      pureA F f (fun y : κ → Af F => ∏ᶠ v, φ v fun i => evalV F v (y i)) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
    intro f φ
    rfl
  intro g hg
  have key : ∀ p ∈ Submodule.span ℂ {p : (κ → Af F) → ℂ | ∃ φ : (v : Pl F) → (κ → Fv F v) → ℂ,
        (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), φ v ∈ SB (κ → Fv F v)) ∧
        (∀ᶠ v in Filter.cofinite, φ v = {x : κ → Fv F v | ∀ i, x i ∈
          IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v}.indicator 1) ∧
        p = fun y => ∏ᶠ v, φ v fun i => evalV F v (y i)},
      ∃ T : SInf F κ →L[ℂ] ℂ, ∀ f : SInf F κ, (l ∘ₗ e) (pureA F f p) = T f := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨φ, h1, h2, rfl⟩ := hp
      have hφ : IsFam φ := hfamOf φ h1 h2
      have hφ' := h.isFam hφ
      obtain ⟨T, hT⟩ := hl _ (hSB _ hφ')
      refine ⟨T.comp ei, fun f => ?_⟩
      rw [LinearMap.comp_apply, hpure, (h.2.2.2.2.2 f φ hφ).1, ← hpure]
      exact hT (ei f)
    | zero =>
      refine ⟨0, fun f => ?_⟩
      have : pureA F f (0 : (κ → Af F) → ℂ) = 0 := by
        funext x
        simp [pureA]
      rw [this, map_zero]
      rfl
    | add p q _ _ hp hq =>
      obtain ⟨T1, h1⟩ := hp
      obtain ⟨T2, h2⟩ := hq
      refine ⟨T1 + T2, fun f => ?_⟩
      have : pureA F f (p + q) = pureA F f p + pureA F f q := by
        funext x
        simp [pureA, mul_add]
      rw [this, map_add, h1, h2]
      rfl
    | smul a p _ hp =>
      obtain ⟨T1, h1⟩ := hp
      refine ⟨a • T1, fun f => ?_⟩
      have : pureA F f (a • p) = a • pureA F f p := by
        funext x
        simp [pureA]
        ring
      rw [this, map_smul, h1]
      rfl
  exact key g (GlobalTheory.SBSpan.mem_span_restrictedProd F κ g hg)

end PositivityTheory.SiegelWeilFormula.TBij

end
