import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThPr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureAdelicFunctionFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedDenominatorsCompactIdeleSetStatement

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

theorem phiA_test : ∀ (F : Type) [Field F] [NumberField F] (G : Ainf F → ℝ) (a : (AF F)ˣ), Continuous G → HasCompactSupport G →
    Continuous (phiA G a) ∧ HasCompactSupport (phiA G a) := by
  intro F _ _ G a hc hs
  have h1 : (a : AF F).1 * ((a⁻¹ : (AF F)ˣ) : AF F).1 = 1 :=
    congrArg Prod.fst (a.mul_inv)
  have h2 : ((a⁻¹ : (AF F)ˣ) : AF F).1 * (a : AF F).1 = 1 :=
    congrArg Prod.fst (a.inv_mul)
  let m : Ainf F ≃ₜ Ainf F :=
    { toFun := fun x => (a : AF F).1 * x
      invFun := fun x => ((a⁻¹ : (AF F)ˣ) : AF F).1 * x
      left_inv := fun x => by simp only [← mul_assoc, h2, one_mul]
      right_inv := fun x => by simp only [← mul_assoc, h1, one_mul]
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  let e : (Unit → Ainf F) ≃ₜ Ainf F := (Homeomorph.funUnique Unit (Ainf F)).trans m
  have he : phiA G a = G ∘ e := by
    funext y
    rfl
  rw [he]
  exact ⟨hc.comp e.continuous, hs.comp_homeomorph e⟩

end GlobalTheory.CompanionTheory.BasePsi

end
