import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.ExistsCrOfFinset
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.GaloisSubgroupLBasicPropertiesStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.IsLCrystallinePointOfSaturatedOrdIdealStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtCont
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

def glPart {G R : Type} [Group G] [CommRing R] {m : ℕ} (H : Subgroup G) (r : G →* GG m R)
    (h : ∀ g ∈ H, (r g).right = 1) : H →* GL (Fin m) R where
  toFun g := (r g).left
  map_one' := by simp
  map_mul' g g' := by simp [h g g.2]

theorem ptsCr_IY : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ), GlobalTheory.OrdLoc.PtsCr D U (GlobalTheory.OrdLoc.IY D U) := by
  intro hP l _ O _ _ _ _ _ _ _ D U B _ _ _ _ _ _ _ f hf
  obtain ⟨-, -, hemb, -, -⟩ := GlobalTheory.T.galoisSubgroupL_basic_properties D
  have hright : ∀ g ∈ D.HL, (push f U.r.hom g).right = 1 := fun g hg => by
    rw [show (push f U.r.hom g).right = (U.r.hom g).right from rfl, U.r.hasMult g]
    exact hg.1
  let ρ := glPart D.HL (push f U.r.hom) hright
  refine ⟨ρ, fun _ => rfl, ?_⟩
  refine GlobalTheory.CrLocal.isCr_of_local D.HL.subtype hemb ρ (fun i j => ?_) ?_
  · have h := (ptCont (l := l) U.R B f).1 (GQ l) (fun g => (U.r.hom g).mat i j) (U.r.cont i j)
    unfold QCont at h ⊢
    exact @Continuous.comp ↥D.HL (GQ l) B _ _ (moduleTopology ℚ_[l] B) Subtype.val (fun g => f ((U.r.hom g).mat i j)) h continuous_subtype_val
  · intro B' _ _ _ _ _ _
    letI : Algebra O B' := ((algebraMap B B').comp (algebraMap O B)).toAlgebra
    letI : Algebra ℤ_[l] B' := ((algebraMap B B').comp (algebraMap ℤ_[l] B)).toAlgebra
    haveI : IsScalarTower ℤ_[l] O B' := IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap B B' (algebraMap ℤ_[l] B x) = algebraMap B B' (algebraMap O B (algebraMap ℤ_[l] O x))
      rw [IsScalarTower.algebraMap_apply ℤ_[l] O B]
    haveI : IsScalarTower ℤ_[l] ℚ_[l] B' := IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap B B' (algebraMap ℤ_[l] B x) = algebraMap ℚ_[l] B' (algebraMap ℤ_[l] ℚ_[l] x)
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] B, IsScalarTower.algebraMap_apply ℚ_[l] B B']
    let f' : U.R →ₐ[O] B' :=
      { toRingHom := (algebraMap B B').comp (f : U.R →+* B)
        commutes' := fun x => by
          change algebraMap B B' (f (algebraMap O U.R x)) = algebraMap B B' (algebraMap O B x)
          rw [f.commutes] }
    obtain ⟨ρ', hρ', hcr⟩ := GlobalTheory.T.isLCrystalline_point_of_saturatedOrdIdeal hP D U B' f' (fun a ha => by
      change algebraMap B B' (f a) = 0
      rw [show f a = 0 from hf ha, map_zero])
    have e : ρ' = (Matrix.GeneralLinearGroup.map (algebraMap B B')).comp ρ := by
      ext g i j
      rw [hρ' g]
      rfl
    exact e ▸ hcr

end GlobalTheory.OrdLoc
