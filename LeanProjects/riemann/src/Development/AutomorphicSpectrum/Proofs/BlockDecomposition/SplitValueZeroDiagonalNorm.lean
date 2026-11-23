import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceEmbeddingPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComponentRationalIdeleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilActionDiagonalStatement
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

variable {K : Type} [Field K] [NumberField K]

theorem degreeOneEmbedding_zero (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal] : dg1 v w (0 : K) = 0 := by
  have hinj : Function.Injective (algebraMap (Qv v) (Kv K w)) := (algebraMap (Qv v) (Kv K w)).injective
  have h := Function.leftInverse_invFun hinj (0 : Qv v)
  simpa [dg1] using h

theorem value_zero_diagonal_norm : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
    L.ok → L.IsSp → ∀ (g : GL (Fin 2) (Qv v)) (κ : Kˣ),
      L.val (dg2 (nv v κ) 1 * g) 0 = c0 L κ * mp (nv v κ) (1 / 2) * L.val g 0 := by
  intro K _ _ _ c v L hok hsp g κ
  cases L with
  | ns w σ η Φ => exact hsp.elim
  | sp w₁ w₂ Φ =>
    obtain ⟨-, hlc, hcs⟩ := hok
    have hc : Continuous ((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) := by
      have h := (continuous_localAdelicChar (K := ℚ) v).comp continuous_neg
      have e : (⇑((GP.psiF v)⁻¹ : AddChar (Qv v) Circle)) = (⇑(localAdelicChar ℚ v)) ∘ Neg.neg := by
        funext x
        simp [AddChar.inv_apply]
      rw [e]
      exact h
    have hn : ((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) ≠ 1 := inv_ne_one.2 (localAdelicChar_ne_one v)
    have key := GlobalTheory.T.split_weil_action_diagonal (Qv v) ((GP.psiF v)⁻¹) hc hn (cAt c v w₁) Φ hlc hcs (nv v κ) g (0, 0)
    simp only [LM.val, c0, degreeOneEmbedding_zero]
    simpa using key

end GlobalTheory.CompanionTheory.FexTheta
