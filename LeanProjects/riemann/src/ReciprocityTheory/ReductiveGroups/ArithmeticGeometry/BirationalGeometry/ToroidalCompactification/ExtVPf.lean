import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVGrp

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

def PullCubDescentSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V],
    IsAdicComplete (maximalIdeal V) V →
    ∀ (t t' : SAB H (Sp V)) (tK : SAB H (Sp (FractionRing V))), IsProper tK.G.hom →
    ∀ (m : SABMap tK t (spMap (algebraMap V (FractionRing V))))
      (m' : SABMap tK t' (spMap (algebraMap V (FractionRing V)))) (ψ : t.G ⟶ t'.G) [IsMonHom ψ],
      m.φ ≫ ψ.left = m'.φ → (CubeMap.ofHom ψ).IsPullCubical t.cub t'.cub

theorem extV_of (hHom : HomExtDvrSt) (hD : PullCubDescentSt) : ExtVStatement := by
  intro E _ _ _ H V _ _ _ hc t t' tK hK m m'
  obtain ⟨ψ, hψm, hψ, hact⟩ := extV_grp hHom t t' tK m m'
  have := hψm
  refine ⟨{ cm := CubeMap.ofHom ψ.hom
            cart := isGrpPullback_of_iso ψ
            base := rfl
            act := fun a => by
              show (t.act.act a).left ≫ ψ.hom.left = ψ.hom.left ≫ (t'.act.act a).left
              rw [← Over.comp_left, hact a, Over.comp_left]
            lin := hD E H V hc t t' tK hK m m' ψ.hom hψ }, hψ⟩

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
