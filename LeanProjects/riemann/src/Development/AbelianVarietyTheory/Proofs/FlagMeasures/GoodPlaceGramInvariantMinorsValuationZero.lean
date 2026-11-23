import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HmUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalExtend
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsIntegralOfQuad
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.StdPlace.UnitVal

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem vE_eq_zero_of_unit (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {c : F}
    (hc : algebraMap F E c ∈ L.O) (hu : ∃ y ∈ L.O, algebraMap F E c * y = 1) :
    vE L ϖ (algebraMap F E c) = 0 := by
  obtain ⟨hadd, -, hint, -⟩ := GlobalTheory.UnramVal.vE_valuation L ϖ hϖ
  obtain ⟨y, hy, hcy⟩ := hu
  have hE : Nontrivial E := Module.nontrivial_of_finrank_pos (R := F) (by rw [L.rank]; omega)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hcy
    exact zero_ne_one hcy
  have hyc : y = algebraMap F E c⁻¹ := by
    have h1 : algebraMap F E c * algebraMap F E c⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
    calc y = (algebraMap F E c⁻¹ * algebraMap F E c) * y := by rw [mul_comm (algebraMap F E c⁻¹), h1, one_mul]
      _ = algebraMap F E c⁻¹ * (algebraMap F E c * y) := by ring
      _ = algebraMap F E c⁻¹ := by rw [hcy, mul_one]
  have hci : c⁻¹ ∈ 𝒪[F] := (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 (hyc ▸ hy)
  have hcO : c ∈ 𝒪[F] := (GlobalTheory.UnramOrder.algebraMap_mem_iff L _).1 hc
  have h1 := (hint c hc0).2 hcO
  have h2 := (hint c⁻¹ (inv_ne_zero hc0)).2 hci
  have h11 := hadd 1 1 one_ne_zero one_ne_zero
  rw [one_mul] at h11
  have h3 := hadd c c⁻¹ hc0 (inv_ne_zero hc0)
  rw [mul_inv_cancel₀ hc0] at h3
  omega

end GlobalTheory.HL.StdPlace.UnitVal

open GlobalTheory.HL.StdPlace.UnitVal in

theorem GlobalTheory.HL.StdPlace.vE_G_D_eq_zero : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), Good S → vE L S.ϖ S.G = 0 ∧ ∀ l, S.D l ≠ 0 → vE L S.ϖ (S.D l * L.cj (S.D l)) = 0 := by
  intro F _ _ _ _ _ E _ _ _ L r k S hS
  obtain ⟨-, -, ⟨c, -, hGc⟩, -⟩ := GlobalTheory.FrameBasic.main L r k S
  refine ⟨?_, fun l hl => ?_⟩
  · rw [hGc]
    obtain ⟨hG, y, hy, hGy⟩ := hS.G_unit
    exact vE_eq_zero_of_unit L S.ϖ_irr (hGc ▸ hG) ⟨y, hy, hGc ▸ hGy⟩
  · obtain ⟨hD, y, hy, hDy⟩ := hS.D_unit l hl
    obtain ⟨c, hc⟩ := GlobalTheory.UnramOrder.exists_norm L hD
    rw [hc]
    refine vE_eq_zero_of_unit L S.ϖ_irr (hc ▸ L.O.mul_mem hD (GlobalTheory.UnramOrder.cj_mem L hD))
      ⟨y * L.cj y, L.O.mul_mem hy (GlobalTheory.UnramOrder.cj_mem L hy), ?_⟩
    rw [← hc]
    calc S.D l * L.cj (S.D l) * (y * L.cj y) = (S.D l * y) * L.cj (S.D l * y) := by rw [map_mul]; ring
      _ = 1 := by rw [hDy, map_one, mul_one]
