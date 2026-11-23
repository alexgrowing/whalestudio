import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsRetractTensorTriple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AmpleDeterminantFramesPullbackOfIsAffineHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardTorsionAbelianVariety

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

noncomputable section

namespace GlobalTheory.Models.RankZero

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {n N : ℕ}

section Point

variable {U : Scheme.{0}} {F O : Type} [Field F] [CommRing O] {c : U ⟶ Sp F} {t₀ : SAB H U}

def pointCpt (hc : IsIso c) (ht : IsIso t₀.G.hom) (β : O →+* F) (hn : Geo.Tor.IsNormalScheme (Sp O)) :
    Cpt c t₀ β where
  X := Sp O
  s := 𝟙 _
  normal := hn
  proj := Inhab.isProjOver_id O
  flat := inferInstance
  jQ := c ≫ inv (pullback.snd _ _)
  jQ_over := by simp
  jQ_open := inferInstance
  jQ_dense := by
    rw [Set.range_eq_univ.2 (c ≫ inv (pullback.snd (𝟙 _) (spMap β))).surjective]
    exact dense_univ
  t := Inhab.zeroTriple H _
  m := (nonempty_sabMap ht (isIso_zeroTriple _) _).some
  ab_gen := by
    rw [Set.range_eq_univ.2 (c ≫ inv (pullback.snd (𝟙 _) (spMap β))).surjective,
      Inhab.abLocus_eq_univ _ (Inhab.isProper_zeroTriple _), Set.preimage_univ]

end Point

theorem zeta_one : zeta 1 = 1 := (pow_one _).symm.trans (BaseRing.zeta_pow_self one_pos)

theorem KA_le_of_eq_one {l₀ : Level H} (h : l₀.A = 1) (l : Level H) : KA l₀ ≤ KA l := by
  refine IntermediateField.adjoin_le_iff.2 ?_
  rintro x (rfl | rfl)
  · exact IntermediateField.subset_adjoin _ _ (by simp)
  · rw [h, zeta_one]; exact one_mem _

end GlobalTheory.Models.RankZero

end
