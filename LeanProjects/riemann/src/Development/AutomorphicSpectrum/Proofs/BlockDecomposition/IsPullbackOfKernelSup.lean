import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

namespace GlobalTheory.CompanionTheory.GE.PbKer

theorem isPullback_of_ker_eq_sup {X A B Z : Scheme.{0}} (a : A ⟶ X) (b : B ⟶ X) (f : Z ⟶ A)
    (g : Z ⟶ B) [IsClosedImmersion a] [IsClosedImmersion b] [IsClosedImmersion (f ≫ a)]
    (h : f ≫ a = g ≫ b)
    (hk : Scheme.Hom.ker (f ≫ a) = Scheme.Hom.ker a ⊔ Scheme.Hom.ker b) :
    IsPullback f g a b := by
  have hle : ∀ {W : Scheme.{0}} (u : W ⟶ A) (v : W ⟶ B), u ≫ a = v ≫ b →
      Scheme.Hom.ker (f ≫ a) ≤ Scheme.Hom.ker (u ≫ a) := by
    intro W u v huv
    rw [hk]
    refine sup_le (Scheme.Hom.le_ker_comp u a) ?_
    rw [huv]
    exact Scheme.Hom.le_ker_comp v b
  refine IsPullback.of_isLimit' ⟨h⟩ ?_
  refine PullbackCone.IsLimit.mk h
    (fun s => IsClosedImmersion.lift (f ≫ a) (s.fst ≫ a) (hle s.fst s.snd s.condition)) ?_ ?_ ?_
  · intro s
    rw [← cancel_mono a, Category.assoc]
    exact IsClosedImmersion.lift_fac _ _ _
  · intro s
    rw [← cancel_mono b, Category.assoc, ← h, ← s.condition]
    exact IsClosedImmersion.lift_fac _ _ _
  · intro s m hm1 _
    rw [← cancel_mono (f ≫ a), IsClosedImmersion.lift_fac, ← Category.assoc, hm1]

end GlobalTheory.CompanionTheory.GE.PbKer
