import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

def HodgeCpt.OmVB {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω]
    {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y) : Prop :=
  ∀ p ∈ S, (𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p)).IsVBOn {q | InFibre 𝔐.ξ p q} (Module.finrank Ω 𝔐.Li) ⊤ ∧
    ∀ s, ((𝔐.M.htOm 𝔐.t.PP.L (p ^ 𝔐.R p)).map (𝔐.Vgen s).dualRestrict).IsVBOn {q | InFibre 𝔐.ξ p q}
      (labelRk D s) ⊤

def IsTowerOf (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (D.p + D.q)) : Prop :=
  ∃ o : TowerOrigin Y T, ∀ B a, (o.Or B a).𝔐.OmVB

def SplitComps {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) : Prop :=
  ∀ (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ Y.X) (cst : c.F →+* Ω), IsCptGen ξ →
    ξ ≫ Y.s = spMap (cst.comp β) → ∀ a : Ω, IsAlgebraic ℤ a → a ∈ cst.range

end GlobalTheory.CompanionTheory.Ar
