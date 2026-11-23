import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace)

namespace GlobalTheory.CompanionTheory.GE

theorem ker_inter_eq_sup {X Y A B Z : Scheme.{0}} (t : Y ⟶ X) (a : A ⟶ Y) (b : B ⟶ Y) (f : Z ⟶ A)
    (g : Z ⟶ B) [IsClosedImmersion t] [IsClosedImmersion a] [IsClosedImmersion b]
    (h : IsPullback f g a b) :
    Scheme.Hom.ker ((f ≫ a) ≫ t) = Scheme.Hom.ker (a ≫ t) ⊔ Scheme.Hom.ker (b ≫ t) := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · set K := Scheme.Hom.ker (a ≫ t) ⊔ Scheme.Hom.ker (b ≫ t) with hK
    have hA : Scheme.Hom.ker (a ≫ t) ≤ K.subschemeι.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]; exact le_sup_left
    have hB : Scheme.Hom.ker (b ≫ t) ≤ K.subschemeι.ker := by
      rw [Scheme.IdealSheafData.ker_subschemeι]; exact le_sup_right
    let u : K.subscheme ⟶ A := IsClosedImmersion.lift (a ≫ t) K.subschemeι hA
    let v : K.subscheme ⟶ B := IsClosedImmersion.lift (b ≫ t) K.subschemeι hB
    have hu : u ≫ a ≫ t = K.subschemeι := IsClosedImmersion.lift_fac _ _ _
    have hv : v ≫ b ≫ t = K.subschemeι := IsClosedImmersion.lift_fac _ _ _
    have huv : u ≫ a = v ≫ b := by
      rw [← cancel_mono t, Category.assoc, Category.assoc, hu, hv]
    have hl : h.lift u v huv ≫ (f ≫ a) ≫ t = K.subschemeι := by
      rw [← Category.assoc, ← Category.assoc, h.lift_fst, Category.assoc]
      exact hu
    calc Scheme.Hom.ker ((f ≫ a) ≫ t) ≤ (h.lift u v huv ≫ (f ≫ a) ≫ t).ker :=
          Scheme.Hom.le_ker_comp _ _
      _ = K := by rw [hl, Scheme.IdealSheafData.ker_subschemeι]
  · rw [Category.assoc]
    exact Scheme.Hom.le_ker_comp _ _
  · rw [h.w, Category.assoc]
    exact Scheme.Hom.le_ker_comp _ _

end GlobalTheory.CompanionTheory.GE
