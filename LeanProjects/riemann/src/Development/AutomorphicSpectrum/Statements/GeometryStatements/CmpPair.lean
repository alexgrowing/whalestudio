import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open AlgebraicGeometry CategoryTheory NumberField Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

def CmpPair : Prop :=
  ∀ (II : IntersectionSystem), IsFullIntersectionSystem II →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (_ : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (π : CMType H ≃ CMType H) (S : Finset ℕ) (n : ℕ)
    (M M' : Top.RootModel (CMType H) (D.p + D.q)) (T : HodgeTie Y S n M) (T' : HodgeTie Y S n M'),
    Mono (spMap β) → Φ.hom ≫ Xo.s = Xo.s → (∀ τ, (π τ).1 = τ.1.comp g.σ.toRingHom) →
    IsImageCpt Φ T.A T'.A → (∀ p ∈ S, T'.A.R p = T.A.R p) →
    ∀ w : Fin (Top.dimFl (CMType H) (D.p + D.q) + 1) → CMType H × Fin (D.p + D.q),
      Tendsto (fun t => II _ _ M.P _ (fun j => M.x t (w j)) / M.δ -
        II _ _ M'.P _ (fun j => M'.x t (π (w j).1, (w j).2)) / M'.δ) (𝓝[>] 0) (𝓝 0)

end GlobalTheory.CompanionTheory.Ar.Cmp
