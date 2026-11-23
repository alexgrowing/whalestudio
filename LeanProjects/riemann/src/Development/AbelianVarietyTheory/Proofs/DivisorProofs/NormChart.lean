import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ProjField

def NormChart {k : Type} [Field k] (B : Over (Sp k)) [GrpObj B] (N₀ : LB B.left) : Prop :=
  ∃ (W V : Over (Sp k)) (π : W ⟶ V) (a : W ⟶ B) (U : B.left.Opens) (N : LB (V ⊗ B).left) (n : N.Sec),
    IsFinite π.left ∧ IsOpenImmersion a.left ∧ Nonempty W.left ∧ LocallyOfFiniteType W.hom ∧
    IsAffineOpen U ∧ (U : Set B.left).Nonempty ∧ N.IsLB ∧ LBIso N (N₀.pull (snd V B).left) ∧
    ∀ x : (V ⊗ B).left, x ∈ Out.nonzeroLocus n ↔
      ∀ z : (W ⊗ B).left, (π ▷ B).left z = x → z ∈ ((fst W B ≫ a) * snd W B).left ⁻¹ᵁ U

end GlobalTheory.ProjField
end
