import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeH

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem dualMapR_eq {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') :
    ReciprocityTheory.ChartRestriction.G.Chart.dualMapR φ = dualMap φ := RingHom.ext fun _ => rfl

section BC

variable {S T : Type} [CommRing S] [Algebra c.F S] [Field T] [Algebra c.F T] (ψ : S →ₐ[c.F] T) (y : FrPt Xo c S)

theorem hw0 (i : Fin (Fintype.card (IxB Dw))) :
    (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ψ.toRingHom) ≫ (uS y i).left) ≫
      ((Over.pullback y.x).obj Xo.univ.t.G).hom = (epsR T).hom ≫ spMap ψ.toRingHom := by
  rw [Category.assoc, Over.w (uS y i)]
  show spMap _ ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap _
  rw [spMap_comp_spMap, spMap_comp_spMap, dualMapR_eq, dualMap_comp_alg]

def uT (i : Fin (Fintype.card (IxB Dw))) :
    epsR T ⟶ (Over.pullback (spMap ψ.toRingHom)).obj ((Over.pullback y.x).obj Xo.univ.t.G) :=
  Over.homMk (pullback.lift (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR ψ.toRingHom) ≫ (uS y i).left) (epsR T).hom
    (hw0 ψ y i)) (pullback.lift_snd _ _ _)

end BC

end ReciprocityTheory.ChartRestriction.G.PullbackSections
