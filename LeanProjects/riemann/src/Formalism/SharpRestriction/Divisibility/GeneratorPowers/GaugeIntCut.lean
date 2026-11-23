import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GermExCut
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBMapPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CanonB

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeIntCut

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB Formalism.L2.Pj

def IntBelow (T : CDVR) (g : ℕ) {σ : Type} (f : MvPowerSeries σ T.Fr) : Prop :=
  ∀ m : σ →₀ ℕ, m.degree < g → coeff m f ∈ (algebraMap T.V T.Fr).range

def SmallUnits (T : CDVR) (g : ℕ) : Prop := ∀ n : ℕ, 0 < n → n < g → IsUnit ((n : ℕ) : T.V)

def ExpLogIntSt : Prop :=
  ∀ (T : CDVR) (g : ℕ), SmallUnits T g → ∀ {σ : Type} [Fintype σ] (f : MvPowerSeries σ T.Fr),
    (constantCoeff f = 0 → IntBelow T g f → IntBelow T g (PowerSeries.subst f (PowerSeries.exp T.Fr))) ∧
    (constantCoeff f = 1 → IntBelow T g f → IntBelow T g (PowerSeries.subst (f - 1) (PowerSeries.log T.Fr)))

def LawLogIntSt : Prop :=
  ∀ (T : CDVR) (g : ℕ), SmallUnits T g → ∀ (d : ℕ) (G : FGLaw T.V d) (ℓ : Pt T.Fr 1 d),
    (∀ i, constantCoeff (ℓ i) = 0) → dLin ℓ = 1 →
    comp1 ℓ ((FBMap.mapG (algebraMap T.V T.Fr) G).add (pt T.Fr (n := 2) d 0) (pt T.Fr (n := 2) d 1)) =
      comp1 ℓ (pt T.Fr (n := 2) d 0) + comp1 ℓ (pt T.Fr (n := 2) d 1) →
    (∀ i, IntBelow T g (ℓ i)) ∧ ∀ ε : Pt T.Fr 1 d, IsInvPair ε ℓ → ∀ i, IntBelow T g (ε i)

def EvIntSt : Prop :=
  ∀ (T : CDVR) (g : ℕ) {d m n : ℕ} (a : Fin m → Pt T.Fr n d) (f : PS T.Fr m d), (∀ j i, constantCoeff (a j i) = 0) →
    (∀ j i, IntBelow T g (a j i)) → IntBelow T g f → IntBelow T g (ev a f)

end Formalism.MainNotions.ModuliIntegralCharts.H1.GaugeIntCut
