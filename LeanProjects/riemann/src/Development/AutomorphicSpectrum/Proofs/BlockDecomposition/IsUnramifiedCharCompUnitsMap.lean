import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.SphTheta

theorem isUnramifiedChar_comp_unitsMap : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [Algebra F E] [ValuativeExtension F E] (c : Eˣ →* ℂˣ), IsUnramifiedChar c → IsUnramifiedChar (c.comp (Units.map (algebraMap F E).toMonoidHom)) := by
  intro F _ _ _ _ E _ _ _ _ _ _ c hc u hu
  have h1 : ValuativeRel.valuation F (u : F) = 1 := mem_unitFiltrationUnits_zero_iff.mp hu
  have ha : (u : F) ≤ᵥ 1 :=
    (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation F) _ _).mpr (by simp [h1])
  have hb : (1 : F) ≤ᵥ (u : F) :=
    (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation F) _ _).mpr (by simp [h1])
  have ha' : algebraMap F E (u : F) ≤ᵥ 1 := by
    simpa using (ValuativeExtension.vle_iff_vle (A := F) (B := E) (u : F) 1).mpr ha
  have hb' : (1 : E) ≤ᵥ algebraMap F E (u : F) := by
    simpa using (ValuativeExtension.vle_iff_vle (A := F) (B := E) 1 (u : F)).mpr hb
  have h2 : Units.map (algebraMap F E).toMonoidHom u ∈ unitFiltrationUnits E 0 := by
    rw [mem_unitFiltrationUnits_zero_iff]
    show ValuativeRel.valuation E (algebraMap F E (u : F)) = 1
    exact le_antisymm
      (by simpa using (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation E) _ _).mp ha')
      (by simpa using (Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation E) _ _).mp hb')
  exact hc h2

end GlobalTheory.CompanionTheory.SphTheta
