import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ColumnSplitting

section Fub4Proof

variable {α β γ δ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

theorem integral_prod_three (b : Measure β) (c : Measure γ) (a : Measure α) [SFinite a] [SFinite b] [SFinite c]
    (g : β × γ × α → ℂ) (hg : Integrable g (b.prod (c.prod a))) :
    ∫ q, g q ∂(b.prod (c.prod a)) = ∫ h, ∫ u, ∫ k, g (h, u, k) ∂a ∂c ∂b := by
  rw [integral_prod _ hg]
  refine integral_congr_ae ?_
  filter_upwards [hg.prod_right_ae] with h hh
  exact integral_prod _ hh

theorem integral_prod_four (e : Measure δ) (b : Measure β) (c : Measure γ) (a : Measure α)
    [SFinite a] [SFinite b] [SFinite c] [SFinite e]
    (g : δ × β × γ × α → ℂ) (hg : Integrable g (e.prod (b.prod (c.prod a)))) :
    ∫ q, g q ∂(e.prod (b.prod (c.prod a))) = ∫ y, ∫ h, ∫ u, ∫ k, g (y, h, u, k) ∂a ∂c ∂b ∂e := by
  rw [integral_prod _ hg]
  refine integral_congr_ae ?_
  filter_upwards [hg.prod_right_ae] with y hy
  exact integral_prod_three b c a _ hy

theorem lintegral_prod_four (e : Measure δ) (b : Measure β) (c : Measure γ) (a : Measure α)
    [SFinite a] [SFinite b] [SFinite c] [SFinite e]
    (g : δ × β × γ × α → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ q, g q ∂(e.prod (b.prod (c.prod a))) = ∫⁻ y, ∫⁻ h, ∫⁻ u, ∫⁻ k, g (y, h, u, k) ∂a ∂c ∂b ∂e := by
  rw [lintegral_prod _ hg.aemeasurable]
  refine lintegral_congr fun y => ?_
  have h1 : Measurable fun q : β × γ × α => g (y, q) := hg.comp measurable_prodMk_left
  rw [lintegral_prod _ h1.aemeasurable]
  refine lintegral_congr fun h => ?_
  have h2 : Measurable fun q : γ × α => g (y, h, q) := h1.comp measurable_prodMk_left
  exact lintegral_prod _ h2.aemeasurable

def swapFour (α β γ δ : Type) [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ] :
    (α × β × γ × δ) ≃ᵐ (δ × β × γ × α) where
  toFun p := (p.2.2.2, p.2.1, p.2.2.1, p.1)
  invFun p := (p.2.2.2, p.2.1, p.2.2.1, p.1)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    dsimp only [Equiv.coe_fn_mk]
    fun_prop
  measurable_invFun := by
    dsimp only [Equiv.coe_fn_symm_mk]
    fun_prop

theorem measurePreserving_swapFour (a : Measure α) (b : Measure β) (c : Measure γ) (e : Measure δ)
    [SFinite a] [SFinite b] [SFinite c] [SFinite e] :
    MeasurePreserving (swapFour α β γ δ) (a.prod (b.prod (c.prod e))) (e.prod (b.prod (c.prod a))) := by
  have p1 : MeasurePreserving (Prod.map id (MeasurableEquiv.prodAssoc (α := β) (β := γ) (γ := δ)).symm)
      (a.prod (b.prod (c.prod e))) (a.prod ((b.prod c).prod e)) :=
    (MeasurePreserving.id a).prod ((measurePreserving_prodAssoc b c e).symm _)
  have p2 : MeasurePreserving (MeasurableEquiv.prodAssoc (α := α) (β := β × γ) (γ := δ)).symm
      (a.prod ((b.prod c).prod e)) ((a.prod (b.prod c)).prod e) :=
    (measurePreserving_prodAssoc a (b.prod c) e).symm _
  have p3 : MeasurePreserving Prod.swap ((a.prod (b.prod c)).prod e) (e.prod (a.prod (b.prod c))) :=
    Measure.measurePreserving_swap
  have p4 : MeasurePreserving (Prod.map id Prod.swap) (e.prod (a.prod (b.prod c))) (e.prod ((b.prod c).prod a)) :=
    (MeasurePreserving.id e).prod Measure.measurePreserving_swap
  have p5 : MeasurePreserving (Prod.map id (MeasurableEquiv.prodAssoc (α := β) (β := γ) (γ := α)))
      (e.prod ((b.prod c).prod a)) (e.prod (b.prod (c.prod a))) :=
    (MeasurePreserving.id e).prod (measurePreserving_prodAssoc b c a)
  exact (((p5.comp p4).comp p3).comp p2).comp p1

end Fub4Proof

theorem iterated_integrals_four_factors_holds : Fub4 := by
  intro α β γ δ _ _ _ _ a b c e _ _ _ _
  have hm := measurePreserving_swapFour a b c e
  constructor
  · intro f hf
    let g : δ × β × γ × α → ℂ := fun q => f (q.2.2.2, q.2.1, q.2.2.1, q.1)
    have hfg : g ∘ swapFour α β γ δ = f := rfl
    have hg : Integrable g (e.prod (b.prod (c.prod a))) :=
      (hm.integrable_comp_emb (swapFour α β γ δ).measurableEmbedding).1 (by rwa [hfg])
    calc ∫ p, f p ∂(a.prod (b.prod (c.prod e)))
        = ∫ p, g (swapFour α β γ δ p) ∂(a.prod (b.prod (c.prod e))) := rfl
      _ = ∫ q, g q ∂(e.prod (b.prod (c.prod a))) :=
          hm.integral_comp (swapFour α β γ δ).measurableEmbedding g
      _ = _ := integral_prod_four e b c a g hg
  · intro f hf
    let g : δ × β × γ × α → ℝ≥0∞ := fun q => f (q.2.2.2, q.2.1, q.2.2.1, q.1)
    have hg : Measurable g := hf.comp (swapFour α β γ δ).symm.measurable
    calc ∫⁻ p, f p ∂(a.prod (b.prod (c.prod e)))
        = ∫⁻ p, g (swapFour α β γ δ p) ∂(a.prod (b.prod (c.prod e))) := rfl
      _ = ∫⁻ q, g q ∂(e.prod (b.prod (c.prod a))) := hm.lintegral_comp hg
      _ = _ := lintegral_prod_four e b c a g hg

end GlobalTheory.CompanionTheory.ColumnSplitting

end
