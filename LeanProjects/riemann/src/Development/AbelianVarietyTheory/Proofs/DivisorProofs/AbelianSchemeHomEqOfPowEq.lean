import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFlatTorsion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulAFiniteFlatSurjectiveEtale
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatAndSurjectiveOfIsFiniteAbelianEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsEqPowOfTorsionCompEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndFlatMulAbelianScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HomTorsionFree

open ReciprocityTheory.ChartRestriction.G.Out

theorem flat_surjective_mulA (S : Scheme.{0}) (B : Over S) [GrpObj B] (hB : IsAbelianScheme B)
    (d : ℕ) (hd : 1 ≤ d) : Flat (mulA B d).left ∧ Surjective (mulA B d).left := by
  have hc := hB.comm
  obtain ⟨hf, hfl⟩ := GlobalTheory.AbTorsionAnyBase.isFinite_and_flat_mulA S B hB d hd
  refine ⟨hfl, GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => ?_⟩
  have hfin : IsFinite ((Over.pullback t).map (mulA B d)).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) hf
  rw [GlobalTheory.MulFiniteFlat.pullback_map_mulA] at hfin ⊢
  have hab := TLinPf.isAb_pullback t B hB
  have := hab.comm
  exact (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected K _
    hab _ (GlobalTheory.AbLaw.MulN.isMonHom_mulA _ d) hfin).2

theorem eq_of_pow_eq : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (d : ℕ), 0 < d → IsUnit ((d : ℕ) : Γ(S, ⊤)) → ∀ (x y : B ⟶ A), IsMonHom x → IsMonHom y → x ^ d = y ^ d → x = y := by
  intro S A B _ _ _ _ _ hB d hd _ x y hx hy hxy
  obtain ⟨hfl, hsu⟩ := flat_surjective_mulA S B hB d hd
  apply GlobalTheory.DivisibleHom.cancel_of_flat_surjective (mulA B d)
  rw [GlobalTheory.DivisibleHom.mulA_comp, GlobalTheory.DivisibleHom.mulA_comp, hxy]

end GlobalTheory.HomTorsionFree
