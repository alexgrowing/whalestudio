import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

namespace GlobalTheory.CechPoset

theorem Φ_one_tmul : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)), Φ w D hD' 0 ((1 : R') ⊗ₜ[R] one s D) = fun _ => 1 := by
  intro R R' _ _ _ X X' s s' φ w κ _ D hD'
  funext t
  have key : GlobalTheory.AbLaw.SecOnR.coord (f := s') (M := (LB.triv X).pull φ) (GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w 1 ((1 : R') ⊗ₜ[R] one s D) t) (i0 φ) = 1 := by
    erw [GlobalTheory.AbLaw.secTermBaseChange_tmul, one_smul]
    refine (GlobalTheory.AbLaw.SecOn.coord_pullLE (M := LB.triv X) φ (GlobalTheory.AbLaw.preimage_biInf D φ t.1).ge ((GlobalTheory.AbLaw.secOnTrivEquiv _).symm 1) (i0 φ)).trans ?_
    have hc : GlobalTheory.LB.coord ((GlobalTheory.AbLaw.secOnTrivEquiv (X := X) (⨅ i ∈ t.1, D i)).symm 1) PUnit.unit = 1 := by
      refine (GlobalTheory.AbLaw.SecOn.coord_chart_symm (M := Out.Inh.trivLB X) (Out.Inh.trivLB_isLB X) PUnit.unit PUnit.unit le_top (1 : Γ(X, ⨅ i ∈ t.1, D i))).trans ?_
      rw [map_one]
      exact (_root_.one_mul _).trans (map_one _)
    exact (congrArg _ hc).trans (map_one _)
  change Sec.res s' _ (GlobalTheory.AbLaw.SecOnR.coord (f := s') (M := (LB.triv X).pull φ) (GlobalTheory.AbLaw.secTermBaseChange (LB.triv X) D w 1 ((1 : R') ⊗ₜ[R] one s D) t) (i0 φ)) = 1
  rw [key]
  exact (Sec.res s' _).map_one

end GlobalTheory.CechPoset
