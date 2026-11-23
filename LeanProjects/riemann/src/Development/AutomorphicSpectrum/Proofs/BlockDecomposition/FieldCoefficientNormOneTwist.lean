import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalNormAtInertPlaceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilInducedRepresentationHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalThetaCentralCharacter
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

noncomputable section

namespace GlobalTheory.CompanionTheory.FexTheta.FieldNormOne

open Ad3.K.GL2LocalData

theorem piE_norm_one : ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η =>
    ∀ (c : Eˣ →* ℂˣ), ∀ Φ ∈ SBc F E c, ∀ (g : GL (Fin 2) F) (u : Eˣ), Algebra.norm F (u : E) = 1 →
      ∀ y : E, piE E χ σ η c g Φ (y * (u : E)) * ((c u : ℂˣ) : ℂ) = piE E χ σ η c g Φ y := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hd hc σ hσ η hη c Φ hΦ g u hu y
  by_cases h : ∃ t : Eˣ, Algebra.norm F (t : E) = (g.val).det
  · have hS := (GlobalTheory.CompanionTheory.WeilPiRep.wPiRep F χ hχ hχ1 E hd hc σ hσ η hη c Φ hΦ 1 g h).2
    rw [hS.2.2 u hu y]
    have hcu : (((c u)⁻¹ : ℂˣ) : ℂ) * ((c u : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    linear_combination (piE E χ σ η c g Φ y) * hcu
  · show piG _ _ _ _ _ _ _ _ * _ = piG _ _ _ _ _ _ _ _
    rw [piG, piG, dif_neg h, zero_mul, dif_neg h]

theorem fL_field : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
    ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
    L.ok → ¬ L.IsSp → ∀ (g : GL (Fin 2) (Qv v)) (ξ : K) (κ : Kˣ), κ ∈ K1 K → ∀ x : (Qv v)ˣ,
      fL L g (ξ * κ) x * cW L κ = fL L g ξ (x * k1 L κ) := by
  intro K _ _ h2 c v L hok hsp g ξ κ hκ x
  have hstd : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
  have hχc : Continuous ((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) := by
    have : (((GP.psiF v)⁻¹ : AddChar (Qv v) Circle) : Qv v → Circle) = fun x => (GP.psiF v x)⁻¹ := by
      funext x; exact AddChar.inv_apply' _ _
    rw [this]
    exact hstd.1.inv
  have hχ1 : (GP.psiF v)⁻¹ ≠ 1 := inv_ne_one.mpr hstd.2.1
  cases L with
  | @sp w₁ w₂ i₁ i₂ Φ => exact absurd trivial hsp
  | @ns w i σ η Φ =>
    haveI := i
    obtain ⟨huq, hσ, hη, hΦ⟩ := hok
    have hκ1 : Algebra.norm ℚ (κ : K) = 1 := by
      have h := congrArg Units.val (MonoidHom.mem_ker.mp hκ)
      simpa using h
    have hN : Algebra.norm (Qv v) ((atW w κ : (Kv K w)ˣ) : Kv K w) = 1 := by
      have h := GlobalTheory.T.local_norm_at_inert_place K h2 v w huq (κ : K)
      rw [hκ1] at h
      simpa [atW] using h
    have key := piE_norm_one (Qv v) _ hχc hχ1 (Kv K w)
      (GlobalTheory.CompanionTheory.QuadPlace.finrank_eq_two_of_ne_refl K h2 v w i σ hσ)
      (continuous_adicCompletionMap v w) σ hσ η hη _ Φ hΦ g (atW w κ) hN (algebraMap K (Kv K w) ξ)
    have e : algebraMap K (Kv K w) (ξ * (κ : K)) =
        algebraMap K (Kv K w) ξ * ((atW w κ : (Kv K w)ˣ) : Kv K w) := by
      rw [map_mul]
      rfl
    show (1 : ℂ) * LM.val (LM.ns w σ η Φ) g (ξ * (κ : K)) * cK c w κ =
      (1 : ℂ) * LM.val (LM.ns w σ η Φ) g ξ
    simp only [one_mul]
    show piG _ _ _ _ _ _ _ (algebraMap K (Kv K w) (ξ * (κ : K))) * _ = piG _ _ _ _ _ _ _ _
    rw [e]
    exact key

end GlobalTheory.CompanionTheory.FexTheta.FieldNormOne
