import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

def TwistBCSpanStatement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R) (k : ℕ), 1 ≤ k → ∀ (α : D.X)
    (R' : Type) [CommRing R'] [IsLocalRing R'] (f : R →+* R'), IsLocalHom f →
    ∀ s' : LB.Sec (LB.LinComb D.P.L
        (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left ≫ DegPre.famφB D α i)
        (DegPre.famε k)),
      ∃ (n : ℕ) (r : Fin n → Γ(Spec (CommRingCat.of R'), ⊤)) (s : Fin n → D.SecB k α),
        ∀ j, s'.f j = ∑ i,
          ((Over.mk (Spec.map (CommRingCat.ofHom f)) ⊗ D.P.A).left.presheaf.map (homOfLE le_top).op).hom
            ((fst (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left.appTop.hom (r i)) *
          ((Over.mk (Spec.map (CommRingCat.ofHom f)) ⊗ D.P.A).left.presheaf.map
            (homOfLE (wchart_comp_le D.P.L (DegPre.famφB D α)
              (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left j)).op).hom
            (((snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left.app _).hom ((s i).f j))

end ReciprocityTheory.ChartRestriction.G.DVR
