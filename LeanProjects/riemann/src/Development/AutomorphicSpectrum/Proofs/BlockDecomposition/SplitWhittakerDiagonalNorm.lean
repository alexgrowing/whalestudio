import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceEmbeddingPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComponentRationalIdeleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilActionDiagonalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilActionTorusEquivariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LFunctionEquationGlobal
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

namespace GlobalTheory.CompanionTheory.FexTheta.SplitW

section Local

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem wcS_eq_integral (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (Φ : F × F → ℂ) (h : GL (Fin 2) F) :
    GL2LocalData.WcS χ c₁ c₂ Φ h = ∫ u : Fˣ, GL2LocalData.piS χ c₁ h Φ ((u : F), ((u⁻¹ : Fˣ) : F)) * ((c₁ u : ℂˣ) : ℂ) *
      (((c₂ u)⁻¹ : ℂˣ) : ℂ) ∂multHaar F := by
  unfold GL2LocalData.WcS GL2LocalData.piS
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [mul_assoc]

theorem wcS_diag [CharZero F] (χ : AddChar F Circle) (hχ : Continuous χ) (hχ1 : χ ≠ 1) (c₁ c₂ : Fˣ →* ℂˣ)
    (Φ : F × F → ℂ) (hl : IsLocallyConstant Φ) (hc : HasCompactSupport Φ) (g : GL (Fin 2) F) (ξ₁ ξ₂ : Fˣ) :
    GL2LocalData.WcS χ c₁ c₂ Φ (dg2 (ξ₁ * ξ₂) 1 * g) =
      ((c₁ ξ₁ : ℂˣ) : ℂ) * ((c₂ ξ₂ : ℂˣ) : ℂ) * mp (ξ₁ * ξ₂) (1 / 2) *
        ∫ x : Fˣ, ((c₁ x * (c₂ x)⁻¹ : ℂˣ) : ℂ) *
          GL2LocalData.piS χ c₁ g (fun y => Φ (y * ((x : F), ((x⁻¹ : Fˣ) : F)))) ((ξ₁ : F), (ξ₂ : F)) ∂multHaar F := by
  rw [wcS_eq_integral, ← integral_mul_left_eq_self _ ξ₂⁻¹, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have e1 := GlobalTheory.T.split_weil_action_diagonal F χ hχ hχ1 c₁ Φ hl hc (ξ₁ * ξ₂) g
    (((ξ₂⁻¹ * x : Fˣ) : F), (((ξ₂⁻¹ * x)⁻¹ : Fˣ) : F))
  have e2 := GlobalTheory.T.split_weil_action_torus_equivariant F χ hχ hχ1 c₁ g Φ x ((ξ₁ : F), (ξ₂ : F))
  have hpt : (((ξ₁ * ξ₂ : Fˣ) : F) * ((ξ₂⁻¹ * x : Fˣ) : F), (((ξ₂⁻¹ * x)⁻¹ : Fˣ) : F)) =
      ((ξ₁ : F), (ξ₂ : F)) * ((x : F), ((x⁻¹ : Fˣ) : F)) := by
    have h2 : (ξ₂ : F) ≠ 0 := ξ₂.ne_zero
    have hx : (x : F) ≠ 0 := x.ne_zero
    refine Prod.ext ?_ ?_
    · simp only [Units.val_mul, Units.val_inv_eq_inv_val, Prod.fst_mul]
      field_simp
    · simp only [Units.val_mul, Units.val_inv_eq_inv_val, Prod.snd_mul, mul_inv, inv_inv]
  beta_reduce
  rw [e1, hpt, e2]
  have n1 : ((c₁ ξ₂ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have n2 : ((c₂ ξ₂ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have n3 : ((c₂ x : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  simp only [map_mul, map_inv, mul_inv, inv_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

end Local

theorem split_alt : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
    L.ok → L.IsSp → ∀ (g : GL (Fin 2) (Qv v)) (κ : Kˣ),
      L.W (dg2 (nv v κ) 1 * g) = cW L κ * mp (nv v κ) (1 / 2) * locI L g κ := by
  intro K _ _ h2 c v L hok hsp g κ
  have hstd : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.RankinQ.isStd_local v
  have hψ := GlobalTheory.CompanionTheory.BaseChangeFunctionalEquation.continuous_charInv (GP.psiF v) hstd.1
  have hψ1 : (GP.psiF v)⁻¹ ≠ 1 := inv_ne_one.2 hstd.2.1
  cases L with
  | ns w σ η Φ => exact hsp.elim
  | @sp w₁ w₂ h₁ h₂ Φ =>
    obtain ⟨hne, hl, hc⟩ := hok
    obtain ⟨d1, d2, dn⟩ := GlobalTheory.T.split_place_embedding_properties K h2 v w₁ w₂ hne
    have hnv : ((nv v κ : (Qv v)ˣ) : Qv v) = dg1 v w₁ (κ : K) * dg1 v w₂ (κ : K) := by
      rw [dn]
      simpa [nv] using GlobalTheory.T.local_component_rational_idele v (Units.map (Algebra.norm ℚ : K →* ℚ) κ)
    have hn0 : dg1 v w₁ (κ : K) * dg1 v w₂ (κ : K) ≠ 0 := hnv ▸ (nv v κ).ne_zero
    let ξ₁ : (Qv v)ˣ := Units.mk0 _ (left_ne_zero_of_mul hn0)
    let ξ₂ : (Qv v)ˣ := Units.mk0 _ (right_ne_zero_of_mul hn0)
    have ha : nv v κ = ξ₁ * ξ₂ := Units.ext (by simpa [ξ₁, ξ₂] using hnv)
    have k1 : cAt c v w₁ ξ₁ = localChar c w₁ (atW w₁ κ) := by
      refine congrArg (localChar c w₁) (Units.ext ?_)
      simpa [ξ₁, atW] using d1 (κ : K)
    have k2 : cAt c v w₂ ξ₂ = localChar c w₂ (atW w₂ κ) := by
      refine congrArg (localChar c w₂) (Units.ext ?_)
      simpa [ξ₂, atW] using d2 (κ : K)
    show GL2LocalData.WcS (GP.psiF v)⁻¹ (cAt c v w₁) (cAt c v w₂) Φ (dg2 (nv v κ) 1 * g) =
      (cK c w₁ κ * cK c w₂ κ) * mp (nv v κ) (1 / 2) * ∫ x, fL (LM.sp w₁ w₂ Φ) g (κ : K) x ∂multHaar (Qv v)
    rw [ha, wcS_diag _ hψ hψ1 _ _ Φ hl hc g ξ₁ ξ₂, k1, k2]
    rfl

end GlobalTheory.CompanionTheory.FexTheta.SplitW
