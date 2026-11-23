import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ValueMemValuationSubring
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl

namespace GlobalTheory.KeyValUnit

theorem valUnit : ∀ κ : Rule, Funct κ → UnitSp κ → ValUnit κ := by
  intro κ hF hU S V K _ _ _ _ _ _ _ _ _ g y x hx
  have := RingHom.ker_isPrime g
  let S₀ := S ⧸ RingHom.ker g
  let K₀ := FractionRing S₀
  let g₀ : S₀ →+* V := RingHom.kerLift g
  let f₀ : S₀ →+* K := (algebraMap V K).comp g₀
  have hf₀ : Function.Injective f₀ := (IsFractionRing.injective V K).comp (RingHom.kerLift_injective g)
  let j : K₀ →+* K := IsFractionRing.lift hf₀
  have hj : j.comp (algebraMap S₀ K₀) = (algebraMap V K).comp g₀ :=
    RingHom.ext fun a => IsFractionRing.lift_algebraMap hf₀ a
  have : CharZero K₀ := j.charZero
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.KeyPow.exists_keyPB_ring y (Ideal.Quotient.mk (RingHom.ker g))
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.KeyPow.exists_keyPB_ring y₀ (algebraMap S₀ K₀)
  have e : j.comp ((algebraMap S₀ K₀).comp (Ideal.Quotient.mk (RingHom.ker g))) = (algebraMap V K).comp g := by
    rw [← RingHom.comp_assoc, hj]
    exact RingHom.ext fun a => congrArg (algebraMap V K) (RingHom.kerLift_mk g a)
  have hxj : KeyPB x x₀ j := GlobalTheory.KeyCancel.keyPB_cancel _ _ _ y x₀ x _ _
    (GlobalTheory.keyPB_trans _ _ _ y y₀ x₀ _ _ hy₀ hx₀) (e.symm ▸ hx)
  have hval := hF K₀ K j x₀ x hxj
  obtain ⟨h₁, h₂⟩ := GlobalTheory.KeyGenInt.isIntegral_value κ hU S₀ K₀ y₀ x₀ hx₀
  have h₁' : IsIntegral V (κ K x : K) := hval ▸ h₁.map_of_comp_eq g₀ j hj.symm
  have h₂' : IsIntegral V ((κ K x : K)⁻¹) := by
    rw [hval, ← map_inv₀]
    exact h₂.map_of_comp_eq g₀ j hj.symm
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 h₁'
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.1 h₂'
  have hab : a * b = 1 := IsFractionRing.injective V K (by
    rw [map_mul, ha, hb, map_one, mul_inv_cancel₀ (κ K x).ne_zero])
  exact ⟨Units.mkOfMulEqOne a b hab, ha.symm⟩

end GlobalTheory.KeyValUnit
