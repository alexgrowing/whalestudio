import Formalism.SharpRestriction.Divisibility.WeightAlgebra

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra

def SpanAt {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (ka : WeightFamilies.Wt D j) : Prop :=
  Submodule.span B.KO ((X.shortTh ka : Submodule (𝓞 B.KO) (B.Cusp j ka)) : Set (B.Cusp j ka)) = ⊤

def LatOfLamSt : Prop :=
  ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (large₂ : SizeData₂ D) (C A : ℝ), (∀ i, 0 < D.host.g i) → S.sK ≠ 0 →
    (∀ F : B.Cusp j ka, F ∈ B.Mlat j ka → F ≠ 0 →
      -(WeightFamilies.PP0v D large₂ C A * (1 + Real.log ka.size) * ka.size) ≤ WeightFamilies.meanLogSup B F) →
    SpanAt X ka → H2 X S ka wL wF → Submodule.IsLattice B.KO (B.Mlat j ka)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
