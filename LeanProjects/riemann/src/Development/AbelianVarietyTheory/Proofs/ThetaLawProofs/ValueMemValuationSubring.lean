import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralOfForallMemDiscreteValuationSubring

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyGenInt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

theorem value_mem_valuationSubring (κ : Rule) (hU : UnitSp κ) (S K : Type) [CommRing S] [Field K] [CharZero K] [Algebra S K]
    (y : KeyIn S) (x : KeyIn K) (h : KeyPB x y (algebraMap S K)) (V : ValuationSubring K) (hV : IsDiscreteValuationRing V)
    (hS : ∀ s : S, algebraMap S K s ∈ V) : (κ K x : K) ∈ V ∧ (κ K x : K)⁻¹ ∈ V := by
  let j : S →+* V := (algebraMap S K).codRestrict V.toSubring hS
  obtain ⟨yV, hyV⟩ := GlobalTheory.KeyPow.exists_keyPB_ring y j
  have hc : (algebraMap V K).comp j = algebraMap S K := RingHom.ext fun _ => rfl
  have hx : KeyPB x yV (algebraMap V K) :=
    GlobalTheory.KeyCancel.keyPB_cancel S V K y yV x j (algebraMap V K) hyV (by rw [hc]; exact h)
  obtain ⟨u, hu, -⟩ := hU V K yV x hx
  refine ⟨?_, ?_⟩
  · rw [hu]; exact (u : V).2
  · have : (κ K x : K)⁻¹ = algebraMap V K (u⁻¹ : Vˣ) := by
      rw [hu]
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← map_mul, Units.mul_inv, map_one]
    rw [this]; exact ((u⁻¹ : Vˣ) : V).2

theorem isIntegral_value : ∀ κ : Rule, UnitSp κ → ∀ (S K : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] [Field K]
    [CharZero K] [Algebra S K] [IsFractionRing S K] (y : KeyIn S) (x : KeyIn K), KeyPB x y (algebraMap S K) →
    IsIntegral S (κ K x : K) ∧ IsIntegral S ((κ K x : K)⁻¹) := by
  intro κ hU S K _ _ _ _ _ _ _ y x h
  exact ⟨GlobalTheory.isIntegral_of_forall_mem_discreteValuationSubring S K _ fun V hV hS => (value_mem_valuationSubring κ hU S K y x h V hV hS).1,
    GlobalTheory.isIntegral_of_forall_mem_discreteValuationSubring S K _ fun V hV hS => (value_mem_valuationSubring κ hU S K y x h V hV hS).2⟩

end GlobalTheory.KeyGenInt
