import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingNumberFieldTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothXF
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartMapLocalSystemStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartSmoothRelativeDimensionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimGenericOpenStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagDimEqShimuraDimStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam.Pad.RelDim

theorem smooth_chart {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p} (hp : p.Prime) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀)
    (hfull : ∀ τ k, k ≤ Dw.mult τ → k ∈ Z.ty τ) (a : Fin Z.m) :
    SmoothOfRelativeDimension (Dw.dim + ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2) (spMap (Z.alg a)) := by
  obtain ⟨g, hg, hs⟩ := GlobalTheory.T.exists_chart_map_local_system hp hW Z a
  haveI := GlobalTheory.T.chart_smooth_relative_dimension Z hfull a g hg
  haveI := smooth_XF (Xo Z.i.l) Z.i.c
  rw [← hs, add_comm]
  infer_instance

set_option maxHeartbeats 1000000 in

theorem relDim_comp (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (hp : p.Prime)
    (W : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W.nonunits) (z : AdmAt S κ hp hW) (C : (nmodel z.Z).Comp) :
    haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
    ((nmodel z.Z).comp C).relDim = Formalism.DegreeFormula.dimFl D.what₂.Tau N := by
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  haveI : IsNormalScheme z.Z.X := z.Z.normal
  haveI : AlgebraicGeometry.IsNoetherian z.Z.X := (nmodel z.Z).isNoetherian
  obtain ⟨x, hxC, hxo⟩ := z.Z.dense.inter_open_nonempty _ (IsNormalScheme.component C).isOpen C.2.1.nonempty
  rw [← z.Z.cover, Set.mem_iUnion] at hxo
  obtain ⟨a, hxa⟩ := hxo
  have hr : Set.range (z.Z.chart a) = ((z.Z.U a).1 : Set z.Z.X) := (z.Z.U a).2.range_fromSpec
  let V : ((nmodel z.Z).comp C).X.Opens := (nmodel z.Z).compι C ⁻¹ᵁ (z.Z.U a).1
  have hV : V ≤ ((nmodel z.Z).comp C).gen := fun v hv => chart_le_gen hp hW a hv
  have hVne : (V : Set ((nmodel z.Z).comp C).X).Nonempty := ⟨⟨x, hxC⟩, hxa⟩
  have e1 := GlobalTheory.T.topologicalKrullDim_generic_open _ ((nmodel z.Z).comp C) V hV hVne
  let Ω : (Sp Γ(z.Z.X, (z.Z.U a).1)).Opens := z.Z.chart a ⁻¹ᵁ IsNormalScheme.component C
  obtain ⟨y, hy⟩ : x ∈ Set.range (z.Z.chart a) := hr ▸ hxa
  haveI hΩ : Nonempty Ω.toScheme := ⟨⟨y, by
    change z.Z.chart a y ∈ (IsNormalScheme.component C : Set z.Z.X)
    rw [hy]
    exact hxC⟩⟩
  haveI := smooth_chart hp hW z.Z z.full a
  have e2 := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth (Ω.ι ≫ spMap (z.Z.alg a))
    (S.Dw.dim + ∑ τ, (S.Dw.mult τ).choose 2) (by
      have : SmoothOfRelativeDimension (0 + (S.Dw.dim + ∑ τ, (S.Dw.mult τ).choose 2)) (Ω.ι ≫ spMap (z.Z.alg a)) :=
        inferInstance
      simpa using this)
  have e3 : topologicalKrullDim ((C.1 ∩ (z.Z.U a).1 : Set z.Z.X)) =
      topologicalKrullDim (V : Set ((nmodel z.Z).comp C).X) :=
    topologicalKrullDim_eq_of_isEmbedding
      (e := fun v : (V : Set ((nmodel z.Z).comp C).X) => (IsNormalScheme.component C).ι v.1)
      ((IsNormalScheme.component C).ι.isOpenEmbedding.isEmbedding.comp Topology.IsEmbedding.subtypeVal) (by
        ext q
        constructor
        · rintro ⟨v, rfl⟩
          exact ⟨v.1.2, v.2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨⟨q, h1⟩, h2⟩, rfl⟩)
  haveI : IsOpenImmersion (z.Z.chart a) := IsAffineOpen.isOpenImmersion_fromSpec (z.Z.U a).2
  have e4 : topologicalKrullDim ((C.1 ∩ (z.Z.U a).1 : Set z.Z.X)) = topologicalKrullDim Ω.toScheme :=
    topologicalKrullDim_eq_of_isEmbedding (e := fun w : Ω.toScheme => z.Z.chart a (Ω.ι w))
      ((z.Z.chart a).isOpenEmbedding.isEmbedding.comp Ω.ι.isOpenEmbedding.isEmbedding) (by
      ext q
      constructor
      · rintro ⟨w, rfl⟩
        refine ⟨?_, hr ▸ ⟨_, rfl⟩⟩
        have := w.2
        exact this
      · rintro ⟨h1, h2⟩
        obtain ⟨y, rfl⟩ : q ∈ Set.range (z.Z.chart a) := hr ▸ h2
        exact ⟨⟨y, h1⟩, rfl⟩)
  have : (((nmodel z.Z).comp C).relDim : WithBot ℕ∞) = ((S.Dw.dim + ∑ τ, (S.Dw.mult τ).choose 2 : ℕ) : WithBot ℕ∞) :=
    e1.symm.trans (e3.symm.trans (e4.trans e2))
  rw [← GlobalTheory.T.flag_dim_eq_shimura_dim S]
  exact_mod_cast this

end GlobalTheory.ShFam.Pad.RelDim
