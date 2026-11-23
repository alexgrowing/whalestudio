import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemFiniteCocyclesIffBcrisTensorCoboundary

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.CrysCoef

open Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {L L' : Type} [Field L] [Algebra Qp L] [Field L'] [Algebra Qp L']

theorem isCrys_mapM [Algebra L L'] [IsScalarTower Qp L L'] [FiniteDimensional L L']
    {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) L) (h : IsCrys PD (matRep M)) :
    IsCrys PD (matRep (mapM (algebraMap L L') M)) := by
  let e := Module.finBasis L L'
  let E : (Fin k → L') ≃ₗ[L] (Fin (finrank L L') → Fin k → L) :=
    { toFun := fun v j i => e.repr (v i) j
      invFun := fun w i => e.equivFun.symm fun j => w j i
      map_add' := fun x y => by funext j i; simp
      map_smul' := fun c x => by funext j i; simp
      left_inv := fun v => by
        funext i
        exact e.equivFun.symm_apply_apply (v i)
      right_inv := fun w => by
        funext j i
        exact congrFun (e.equivFun.apply_symm_apply fun j => w j i) j }
  have : Nonempty (Fin (finrank L L')) := ⟨⟨0, Module.finrank_pos⟩⟩
  refine GlobalTheory.CoeffExt.isCrys_ext PD (E := E) (fun g x j => ?_) (Fintype.card_fin _).symm h
  funext i
  change e.repr (∑ a, algebraMap L L' (M g i a) * x a) j = ∑ a, M g i a * e.repr (x a) j
  simp only [← Algebra.smul_def, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul]

end Generic

theorem isCrys_inclusion (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K L L' : FinExt l) (h : L.1 ≤ L'.1) (k : ℕ)
    (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥L.1) (hM : IsCrys (P.PD K) (matRep M)) :
    IsCrys (P.PD K) (matRep (mapM (IntermediateField.inclusion h).toRingHom M)) := by
  letI : Algebra ↥L.1 ↥L'.1 := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ_[l] ↥L.1 ↥L'.1 :=
    IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion h).commutes x).symm
  haveI := L'.2
  haveI : FiniteDimensional ↥L.1 ↥L'.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  exact isCrys_mapM (P.PD K) M hM

end GlobalTheory.CrysCoef
