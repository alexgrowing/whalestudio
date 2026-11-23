import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SliceFacts

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

def OpBox : Prop := ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
  ∀ (κ' κ'' : Type) [Fintype κ'] [Fintype κ''] (W : Type) [AddCommGroup W] [Module (AF F) W] (B : W → W → AF F)
    (dd : Darboux B (κ' ⊕ κ'')) (G : Type) [Group G] (act : G → W → W)
    (om : G →* Module.End ℂ ((κ' ⊕ κ'' → AF F) → ℂ)),
    IsSplitting (adeleClass F) ψ dd act om →
    (∀ u v : κ'' → AF F, ∃ w, dd.e w = (Sum.elim (0 : κ' → AF F) u, Sum.elim (0 : κ' → AF F) v)) →
    ∀ x : G, (∀ w, (dd.e w).1 ∘ Sum.inl = 0 → (dd.e w).2 ∘ Sum.inl = 0 → act x w = w) →
    ∀ φ₀ ∈ schA F κ'', φ₀ 0 = 1 →
      (∀ Ψ ∈ schA F (κ' ⊕ κ''), slice0 κ' κ'' (om x Ψ) = slice0 κ' κ'' (om x (boxFun (slice0 κ' κ'' Ψ) φ₀))) ∧
      ∀ φ' ∈ schA F κ', ∀ φ'' ∈ schA F κ'',
        om x (boxFun φ' φ'') = boxFun (slice0 κ' κ'' (om x (boxFun φ' φ₀))) φ''

def SubSplit : Prop := ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
  ∀ (κ' κ'' : Type) [Fintype κ'] [Fintype κ''] (W W' : Type) [AddCommGroup W] [Module (AF F) W] [AddCommGroup W']
    [Module (AF F) W'] (B : W → W → AF F) (B' : W' → W' → AF F) (dd : Darboux B (κ' ⊕ κ'')) (dd' : Darboux B' κ')
    (emb : W' → W), (∀ w', dd.e (emb w') = (Sum.elim (dd'.e w').1 0, Sum.elim (dd'.e w').2 0)) →
  ∀ (G G' : Type) [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] (act : G → W → W)
    (act' : G' → W' → W') (j : G' →* G), Continuous j → (∀ g w', act (j g) (emb w') = emb (act' g w')) →
  ∀ (om : G →* Module.End ℂ ((κ' ⊕ κ'' → AF F) → ℂ)) (om' : G' →* Module.End ℂ ((κ' → AF F) → ℂ)),
    IsUSplitting (adeleClass F) ψ dd act om →
  ∀ φ₀ ∈ schA F κ'', φ₀ 0 = 1 →
    (∀ μ'' : @Measure (κ'' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ'' →
      ∫⁻ x, ‖φ₀ x‖ₑ ^ 2 ∂μ'' ≠ 0 ∧ ∫⁻ x, ‖φ₀ x‖ₑ ^ 2 ∂μ'' ≠ ⊤) →
    (∀ g, ∃ φ₁ ∈ schA F κ'', φ₁ 0 = 1 ∧
      (∀ μ'' : @Measure (κ'' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ'' →
        ∫⁻ x, ‖φ₁ x‖ₑ ^ 2 ∂μ'' = ∫⁻ x, ‖φ₀ x‖ₑ ^ 2 ∂μ'') ∧
      ∀ φ' ∈ schA F κ', om (j g) (boxFun φ' φ₀) = boxFun (om' g φ') φ₁) →
    IsUSplitting (adeleClass F) ψ dd' act' om'

end PositivityTheory.SiegelWeilFormula.Ald

end
