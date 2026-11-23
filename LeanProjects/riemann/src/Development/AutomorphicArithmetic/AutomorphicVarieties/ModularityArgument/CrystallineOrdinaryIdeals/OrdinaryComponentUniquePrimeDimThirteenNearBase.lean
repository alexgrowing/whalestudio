import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryLocusIdealLeKerOfIsBasePointStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SaturatedOrdinaryIdealTangentFinrankEqTwelveStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.UnivEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FinrankPointDerivationsVanishingEqOfIsCompl
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

theorem component_basic : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ), GlobalTheory.OrdLoc.primesAt0 D U = {GlobalTheory.OrdLoc.It D U} ∧ (GlobalTheory.OrdLoc.It D U).IsPrime ∧ (l : U.R) ∉ GlobalTheory.OrdLoc.It D U ∧ GlobalTheory.OrdLoc.Icr D U ≤ GlobalTheory.OrdLoc.It D U ∧ ringKrullDim (GlobalTheory.OrdLoc.Rt D U) = 13 ∧ GlobalTheory.OrdLoc.On D U (r0 D.η D.Ψ) ∧ ∀ x, IsBase D.η D.Ψ U.r.hom x → ∃ y, x y ≠ 0 ∧ ∀ a ∈ GlobalTheory.OrdLoc.It D U, y * a ∈ GlobalTheory.OrdLoc.Icr D U := by
  intro hP l _ O _ _ _ _ _ _ _ D U
  have hi : Function.Injective (algebraMap ℤ_[l] O) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra h
    have hp : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsPrime := inferInstance
    have hm : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsMaximal := hp.isMaximal h
    have h2 : (⊥ : Ideal O).IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ℤ_[l]) _ hm
    exact IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal h2).symm
  haveI : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hi2 : Function.Injective (algebraMap ℤ_[l] (FractionRing O)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] O (FractionRing O)]
    exact (IsFractionRing.injective O _).comp hi
  letI : Algebra ℚ_[l] (FractionRing O) := (IsFractionRing.lift hi2).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] (FractionRing O) :=
    IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hi2 x).symm
  haveI : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors ℤ_[l])) (FractionRing O) := inferInstance
  haveI : Module.Finite ℚ_[l] (FractionRing O) :=
    Module.Finite.of_isLocalization ℤ_[l] O (nonZeroDivisors ℤ_[l])
  obtain ⟨x, hx, hxu⟩ := univEx D U
  obtain ⟨-, n, P, φ, hφ, hIP, ⟨y, hy, hyP⟩, hPI, h0, hdim⟩ := GlobalTheory.T.exists_unique_ordinaryPrime_dim_succ_near_base hP D U (FractionRing O) x hx
  have hmem : P ∈ primesAt0 D U := by rw [h0]; rfl
  have hmin := hmem.1
  have hPx : P ≤ RingHom.ker x := hmem.2 x hx
  let T : Submodule (FractionRing O) (U.R →ₗ[O] FractionRing O) :=
    { carrier := {δ | (∀ a b, δ (a * b) = algebraMap O _ (x a) * δ b + algebraMap O _ (x b) * δ a) ∧
        ∀ a ∈ IY D U, δ a = 0}
      zero_mem' := ⟨fun a b => by simp, fun a _ => rfl⟩
      add_mem' := by
        rintro δ δ' ⟨h1, h2⟩ ⟨h3, h4⟩
        refine ⟨fun a b => ?_, fun a ha => ?_⟩
        · simp only [LinearMap.add_apply, h1 a b, h3 a b]; ring
        · simp only [LinearMap.add_apply, h2 a ha, h4 a ha, add_zero]
      smul_mem' := by
        rintro c δ ⟨h1, h2⟩
        refine ⟨fun a b => ?_, fun a ha => ?_⟩
        · simp only [LinearMap.smul_apply, h1 a b, smul_eq_mul]; ring
        · simp only [LinearMap.smul_apply, h2 a ha, smul_zero] }
  have hT : ∀ δ, δ ∈ T ↔ (∀ a b, δ (a * b) = algebraMap O _ (x a) * δ b + algebraMap O _ (x b) * δ a) ∧
      ∀ a ∈ IY D U, δ a = 0 := fun δ => Iff.rfl
  have h1 := GlobalTheory.T.saturatedOrdinaryIdeal_tangent_finrank_eq_twelve hP D U (FractionRing O) x hx T hT
  have h2 : finrank (FractionRing O) ↥T = n := UpperTheory.finrank_pointDerivations_vanishing_eq_of_isCompl n P x φ hφ T fun δ => by
    rw [hT]
    refine and_congr_right fun h => ⟨fun h' a ha => ?_, fun h' a ha => h' a (hIP ha)⟩
    have e := h y a
    rw [h' _ (hyP a ha), show x a = 0 from hPx ha, map_zero, zero_mul, add_zero] at e
    exact (mul_eq_zero.1 e.symm).resolve_left fun h0 =>
      hy (IsFractionRing.injective O (FractionRing O) (h0.trans (map_zero _).symm))
  obtain rfl : n = 12 := by rw [← h2, h1]
  subst hPI
  refine ⟨h0, hmin.1.1, fun hl => ?_, hmin.1.2, hdim, ⟨x, hx, hPx⟩, fun x' hx' => ?_⟩
  · have h2 : x (l : U.R) = 0 := hPx hl
    rw [map_natCast] at h2
    exact (Fact.out : l.Prime).ne_zero (Nat.cast_eq_zero.1 h2)
  · rw [hxu x' hx']
    exact ⟨y, hy, fun a ha => Ideal.le_radical (hyP a ha)⟩

end GlobalTheory.OrdLoc
