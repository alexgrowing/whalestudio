import Formalism.LocalToGlobal.LatticeGeometry.GeometryDefinitions.ClsSum
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.QuotientMetricDivisors.Statement

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2.Geo.Def

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def UnimodularLatticeLogCovolume : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (K0 : Subfield K),
    Formalism.DivisionValues.IsCMSub K0 → ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ),
    Formalism.DivisionValues.IsRatHerm K0 H X →
    ∀ T : Submodule (𝓞 K) (Fin d → K), Submodule.IsLattice K T →
      Formalism.HermitianLatticesTheory.IsUnimodular (Formalism.DivisionValues.hform H) T → Formalism.DivisionValues.lcv X T = 0

variable (D : D7)

def DegreeHermitianFormula (ell : D.what₂.Tau → HLat D.what₂.LL) : Prop :=
  (SW D).IsPosDef → (∀ τ, (ell τ).Good ∧ (ell τ).rank = 1) →
    ∀ (c : XDef D) (τ : D.what₂.Tau), degHHc D ell c τ = (nW D : ℝ) * (ell τ).mu / 2

def DegreeCompatibility (large₂ : SizeData₂ D) (V : DivX D) (ell : D.what₂.Tau → HLat D.what₂.LL) : Prop :=
  DegreeHermitianFormula D ell → (∀ τ, (ell τ).Good ∧ (ell τ).rank = 1) → (∀ τ, D.gx.logOmMean τ = (ell τ).mu) →
  placeRankTwoOne.Conclusion1 D large₂ →
  ∀ e : V.Comp D.R.m ≃ XDef D, (∀ c τ, V.degHH D.R.m c τ = degHHc D ell (e c) τ) →
    (∀ (c : V.Comp D.R.m) τ, V.degHH D.R.m c τ = placeRankTwoOne.dFl D large₂ D.R.m) ∧
    (∀ (c : V.Comp D.R.m) τ, V.degHH D.R.m c τ = -placeRankTwoOne.c1 D V D.R.m τ) ∧
    (∀ Cc rd Lchi : ℝ, ∀ τ, |placeRankTwoOne.c1 D V D.R.m τ + (D.R.r : ℝ) * large₂.logOm / 2| ≤ Cc * 0 * (Real.log rd + Lchi))

example (τ : D.what₂.Tau) : embT D τ = placeRankTwoOne.embTau D τ := rfl

end Formalism.L2.Geo.Def
