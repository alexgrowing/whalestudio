import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryLocusIdealLeKerOfIsBasePointStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SaturatedOrdinaryIdealTangentFinrankEqTwelveStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FinrankPointDerivationsVanishingEqOfIsCompl
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem GlobalTheory.OrdLoc.rtCompl : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : D.Univ) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (x : U.R →ₐ[O] O), IsBase D.η D.Ψ U.r.hom x → GlobalTheory.OrdLoc.primesAt0 D U = {GlobalTheory.OrdLoc.It D U} ∧ ∃ φ : U.R →ₐ[O] MvPowerSeries (Fin 12) E, UpperTheory.V.Loc.IsCompl (GlobalTheory.OrdLoc.It D U) x φ := by
  intro hL l _ O _ _ _ _ _ _ _ D U E _ _ _ _ _ _ _ _ x hx
  obtain ⟨-, n, P, φ, hφ, hIP, ⟨y, hy, hyP⟩, hIt, h0, -⟩ := GlobalTheory.T.exists_unique_ordinaryPrime_dim_succ_near_base hL D U E x hx
  have hPx : P ≤ RingHom.ker x := by
    have hm : P ∈ GlobalTheory.OrdLoc.primesAt0 D U := by rw [h0]; rfl
    exact hm.2 x hx
  let T : Submodule E (U.R →ₗ[O] E) :=
    { carrier := {δ | (∀ a b, δ (a * b) = algebraMap O E (x a) * δ b + algebraMap O E (x b) * δ a) ∧
        ∀ a ∈ GlobalTheory.OrdLoc.IY D U, δ a = 0}
      zero_mem' := ⟨by simp, by simp⟩
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
  have hT : ∀ δ, δ ∈ T ↔ (∀ a b, δ (a * b) = algebraMap O E (x a) * δ b + algebraMap O E (x b) * δ a) ∧
      ∀ a ∈ GlobalTheory.OrdLoc.IY D U, δ a = 0 := fun δ => Iff.rfl
  have h1 := GlobalTheory.T.saturatedOrdinaryIdeal_tangent_finrank_eq_twelve hL D U E x hx T hT
  have h2 : finrank E ↥T = n := UpperTheory.finrank_pointDerivations_vanishing_eq_of_isCompl n P x φ hφ T fun δ => by
    rw [hT]
    refine and_congr_right fun h => ⟨fun h' a ha => ?_, fun h' a ha => h' a (hIP ha)⟩
    have e := h y a
    rw [h' _ (hyP a ha), show x a = 0 from hPx ha, map_zero, zero_mul, add_zero] at e
    exact (mul_eq_zero.1 e.symm).resolve_left fun h0 =>
      hy (IsFractionRing.injective O E (h0.trans (map_zero _).symm))
  obtain rfl : n = 12 := by rw [← h2, h1]
  exact ⟨by rw [← hIt, h0], φ, hIt ▸ hφ⟩
