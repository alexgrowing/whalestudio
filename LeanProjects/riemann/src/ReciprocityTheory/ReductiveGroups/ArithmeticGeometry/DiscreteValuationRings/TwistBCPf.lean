import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.AppCompatGeneric

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi

def TwistBaseChangeStatement : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R)
    (k : ℕ), 1 ≤ k →
    ∀ (α : D.X), ∃ (m : ℕ) (b : Fin m → D.SecB k α), m = k ^ D.P.g ∧
      ∀ (R' : Type) [CommRing R'] (f : R →+* R'),
      ∀ b' : Fin m → LB.Sec (LB.LinComb D.P.L
          (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left ≫ DegPre.famφB D α i)
          (DegPre.famε k)),
        (∀ i, IsPullSecLC D.P.L (DegPre.famφB D α) (DegPre.famε k)
          (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left (b i) (b' i)) →
        IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.P.A) _ b'

theorem twistBCSpan_of (h : TwistBaseChangeStatement) : TwistBCSpanStatement := by
  intro R _ _ _ _ D k hk α R' _ _ f _ s'
  obtain ⟨m, b, -, hb⟩ := h R D k hk α
  have hbasis := hb R' f (fun i => pullSec D.P.L (DegPre.famφB D α) (DegPre.famε k) (b i)
      (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left) (fun i j => rfl)
  obtain ⟨r, hr, -⟩ := hbasis s'
  exact ⟨m, r, b, hr⟩

end ReciprocityTheory.ChartRestriction.G.DVR
