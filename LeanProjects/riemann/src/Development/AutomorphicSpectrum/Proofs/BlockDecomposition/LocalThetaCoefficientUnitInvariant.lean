import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnramifiedCharCompUnitsMap

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.FexTheta

theorem fL_mul_unit : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → (¬ L.IsSp ∨ (Unr c v ∧ L.std)) → ∀ (g : GL (Fin 2) (Qv v)) (ξ : K) (x : (Qv v)ˣ),
    ∀ e ∈ unQ v, fL L g ξ (x * e) = fL L g ξ x := by
  intro K _ _ _ c v L _ hL g ξ x e he
  cases L with
  | ns w σ η Φ => rfl
  | sp w₁ w₂ Φ =>
    rcases hL with h | ⟨hU, hstd⟩
    · exact absurd trivial h
    have r₁ : IsUnramifiedChar (cAt c v w₁) :=
      GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₁) (localChar c w₁) (hU w₁).1
    have r₂ : IsUnramifiedChar (cAt c v w₂) :=
      GlobalTheory.CompanionTheory.SphTheta.isUnramifiedChar_comp_unitsMap (Qv v) (Kv K w₂) (localChar c w₂) (hU w₂).1
    have hval : ValuativeRel.valuation (Qv v) (e : Qv v) = 1 := by
      have ha : ValuativeRel.valuation (Qv v) (e : Qv v) ≤ 1 := he.1
      have hb : ValuativeRel.valuation (Qv v) ((e⁻¹ : (Qv v)ˣ) : Qv v) ≤ 1 := he.2
      have hm : ValuativeRel.valuation (Qv v) (e : Qv v) *
          ValuativeRel.valuation (Qv v) ((e⁻¹ : (Qv v)ˣ) : Qv v) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      refine le_antisymm ha ?_
      calc (1 : _) = ValuativeRel.valuation (Qv v) (e : Qv v) *
            ValuativeRel.valuation (Qv v) ((e⁻¹ : (Qv v)ˣ) : Qv v) := hm.symm
        _ ≤ ValuativeRel.valuation (Qv v) (e : Qv v) * 1 := mul_le_mul_right hb _
        _ = _ := mul_one _
    have hmem : e ∈ unitFiltrationUnits (Qv v) 0 := mem_unitFiltrationUnits_zero_iff.mpr hval
    have he₁ : cAt c v w₁ e = 1 := MonoidHom.mem_ker.1 (r₁ hmem)
    have he₂ : cAt c v w₂ e = 1 := MonoidHom.mem_ker.1 (r₂ hmem)
    have hct : (LM.sp w₁ w₂ Φ : LM c v).ct (x * e) = (LM.sp w₁ w₂ Φ : LM c v).ct x := by
      simp [LM.ct, map_mul, he₁, he₂]
    have htw : (LM.sp w₁ w₂ Φ : LM c v).tw (x * e) = (LM.sp w₁ w₂ Φ : LM c v).tw x := by
      have hΦ : Φ = Set.indicator {x : Qv v × Qv v | x.1 ∈ 𝒪[Qv v] ∧ x.2 ∈ 𝒪[Qv v]} 1 := hstd
      simp only [LM.tw]
      congr 1
      funext y
      have hO : ∀ (a : Qv v) (u : (Qv v)ˣ), (u : Qv v) ∈ 𝒪[Qv v] → ((u⁻¹ : (Qv v)ˣ) : Qv v) ∈ 𝒪[Qv v] →
          (a * (u : Qv v) ∈ 𝒪[Qv v] ↔ a ∈ 𝒪[Qv v]) := by
        intro a u h1 h2
        refine ⟨fun h => ?_, fun h => mul_mem h h1⟩
        have h3 := mul_mem h h2
        rwa [mul_assoc, Units.mul_inv, mul_one] at h3
      have key : (y * (((x * e : (Qv v)ˣ) : Qv v), (((x * e)⁻¹ : (Qv v)ˣ) : Qv v))) ∈
            {z : Qv v × Qv v | z.1 ∈ 𝒪[Qv v] ∧ z.2 ∈ 𝒪[Qv v]} ↔
          (y * ((x : Qv v), ((x⁻¹ : (Qv v)ˣ) : Qv v))) ∈
            {z : Qv v × Qv v | z.1 ∈ 𝒪[Qv v] ∧ z.2 ∈ 𝒪[Qv v]} := by
        have e1' : y.1 * ((x * e : (Qv v)ˣ) : Qv v) = (y.1 * (x : Qv v)) * (e : Qv v) := by
          rw [Units.val_mul, mul_assoc]
        have e2' : y.2 * (((x * e)⁻¹ : (Qv v)ˣ) : Qv v) =
            (y.2 * ((x⁻¹ : (Qv v)ˣ) : Qv v)) * ((e⁻¹ : (Qv v)ˣ) : Qv v) := by
          rw [mul_inv, Units.val_mul, mul_assoc]
        have hinv : (((e⁻¹)⁻¹ : (Qv v)ˣ) : Qv v) ∈ 𝒪[Qv v] := by
          rw [inv_inv]; exact he.1
        simp only [Set.mem_ofPred_eq, Prod.fst_mul, Prod.snd_mul]
        rw [e1', e2', hO _ e he.1 he.2, hO _ e⁻¹ he.2 hinv]
      rw [hΦ]
      by_cases h : (y * ((x : Qv v), ((x⁻¹ : (Qv v)ˣ) : Qv v))) ∈
          {z : Qv v × Qv v | z.1 ∈ 𝒪[Qv v] ∧ z.2 ∈ 𝒪[Qv v]}
      · rw [Set.indicator_of_mem (key.2 h), Set.indicator_of_mem h]; rfl
      · rw [Set.indicator_of_notMem (fun h' => h (key.1 h')), Set.indicator_of_notMem h]
    simp only [fL, hct, htw]

end GlobalTheory.CompanionTheory.FexTheta
