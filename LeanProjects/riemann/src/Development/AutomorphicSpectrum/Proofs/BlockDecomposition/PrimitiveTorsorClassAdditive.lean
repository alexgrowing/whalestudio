import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechTripleRestrictCompositeInjectiveCohomologyFo
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.SmallLift

theorem primitive_HO1_abelian : DescentSt → LowSt → AxOSt → AllAb fun _ _ A _ _ ↦ ∀ (c : HO1 A.hom) (a b d : HO1 (A ⊗ A).hom), IsPullO (wOver (fst A A * snd A A)) c a → IsPullO (wOver (fst A A)) c b → IsPullO (wOver (snd A A)) c d → a = b + d := by
  intro _ _ hAx R _ A _ g hA hg c a b d ha hb hd
  have hm : fst A A * snd A A = μ[A] := by
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp]
  have p := GlobalTheory.CompanionTheory.HopfSys.primitive_structure_sheaf_cohomology_class A (hAx R A g hA hg) c
  revert ha
  rw [hm]
  intro ha
  rw [ha.eq_pullHO1, hb.eq_pullHO1, hd.eq_pullHO1]
  exact p

end GlobalTheory.CompanionTheory.SmallLift
