import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceEmbeddingPropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalComponentRationalIdeleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalNormAtInertPlaceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitWeilActionTorusEquivariant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitInducedRepresentationHypothesis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsStdInvAndTrivialAndNontrivial
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentIdealRat
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

namespace GlobalTheory.CompanionTheory.FexTheta.SplitNormOne

theorem fL_mul_norm_one : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → L.IsSp → ∀ (g : GL (Fin 2) (Qv v)) (ξ : K) (κ : Kˣ), κ ∈ K1 K → ∀ x : (Qv v)ˣ,
    fL L g (ξ * κ) x * cW L κ = fL L g ξ (x * k1 L κ) := by
  intro K _ _ h2 c v L hok hsp g ξ κ hκ x
  cases L with
  | ns w σ η Φ => exact hsp.elim
  | sp w₁ w₂ Φ =>
    obtain ⟨hne, -, -⟩ := hok
    obtain ⟨a1, a2, aN⟩ := GlobalTheory.T.split_place_embedding_properties K h2 v w₁ w₂ hne
    have hψ : IsStd (GP.psiF v) := GlobalTheory.CompanionTheory.StdCharQ.stdChar v
    obtain ⟨hχc, hχ1, -⟩ :=
      (GlobalTheory.CompanionTheory.StdAddChar.isStd_inv_and_trivial_and_nontrivial (Qv v) _ hψ).1
    have inj1 : Function.Injective (algebraMap (Qv v) (Kv K w₁)) :=
      (algebraMap (Qv v) (Kv K w₁)).injective
    have inj2 : Function.Injective (algebraMap (Qv v) (Kv K w₂)) :=
      (algebraMap (Qv v) (Kv K w₂)).injective
    have m1 : dg1 v w₁ (ξ * κ) = dg1 v w₁ ξ * dg1 v w₁ (κ : K) := by
      apply inj1; rw [map_mul, a1, a1, a1, map_mul]
    have m2 : dg1 v w₂ (ξ * κ) = dg1 v w₂ ξ * dg1 v w₂ (κ : K) := by
      apply inj2; rw [map_mul, a2, a2, a2, map_mul]
    have hN : Algebra.norm ℚ (κ : K) = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.mp hκ)
      simpa using this
    have hk : dg1 v w₁ (κ : K) * dg1 v w₂ (κ : K) = 1 := by
      rw [aN, hN]; simp
    have h0 : dg1 v w₁ (κ : K) ≠ 0 := left_ne_zero_of_mul_eq_one hk
    set u : (Qv v)ˣ := Units.mk0 _ h0 with hu
    have hk1 : k1 (LM.sp w₁ w₂ Φ : LM c v) κ = u := by
      have : e1 (LM.sp w₁ w₂ Φ : LM c v) (κ : K) = dg1 v w₁ (κ : K) := rfl
      unfold k1
      rw [dif_neg (by rw [this]; exact h0)]
      exact Units.ext rfl
    have hu1 : (u : Qv v) = dg1 v w₁ (κ : K) := rfl
    have hu2 : ((u⁻¹ : (Qv v)ˣ) : Qv v) = dg1 v w₂ (κ : K) := by
      apply Units.inv_eq_of_mul_eq_one_right
      exact hk
    have c1 : cK c w₁ κ = ((cAt c v w₁ u : ℂˣ) : ℂ) := by
      have : atW w₁ κ = Units.map (algebraMap (Qv v) (Kv K w₁)).toMonoidHom u := by
        apply Units.ext
        exact (a1 (κ : K)).symm
      simp only [cK, cAt, MonoidHom.comp_apply, this]
    have c2 : cK c w₂ κ = ((cAt c v w₂ u⁻¹ : ℂˣ) : ℂ) := by
      have : atW w₂ κ = Units.map (algebraMap (Qv v) (Kv K w₂)).toMonoidHom u⁻¹ := by
        apply Units.ext
        show algebraMap K (Kv K w₂) (κ : K) = algebraMap (Qv v) (Kv K w₂) ((u⁻¹ : (Qv v)ˣ) : Qv v)
        rw [hu2, a2]
      simp only [cK, cAt, MonoidHom.comp_apply, this]
    have tw : ∀ (y : (Qv v)ˣ) (ζ : K), ((LM.sp w₁ w₂ Φ : LM c v).tw y).val g ζ =
        GL2LocalData.piS (GP.psiF v)⁻¹ (cAt c v w₁) g Φ
          ((dg1 v w₁ ζ, dg1 v w₂ ζ) * ((y : Qv v), ((y⁻¹ : (Qv v)ˣ) : Qv v))) := fun y ζ =>
      GlobalTheory.CompanionTheory.SplitTorus.piS_torus (Qv v) _ hχc hχ1 (cAt c v w₁) g Φ y _
    have pt : (dg1 v w₁ (ξ * κ), dg1 v w₂ (ξ * κ)) * ((x : Qv v), ((x⁻¹ : (Qv v)ˣ) : Qv v)) =
        (dg1 v w₁ ξ, dg1 v w₂ ξ) * (((x * u : (Qv v)ˣ) : Qv v), (((x * u)⁻¹ : (Qv v)ˣ) : Qv v)) := by
      rw [m1, m2, mul_inv, Units.val_mul, Units.val_mul, hu1, hu2]
      ext <;> simp <;> ring
    rw [hk1]
    simp only [fL, tw, cW, pt, c1, c2]
    simp only [LM.ct, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, mul_inv]
    ring

end GlobalTheory.CompanionTheory.FexTheta.SplitNormOne
