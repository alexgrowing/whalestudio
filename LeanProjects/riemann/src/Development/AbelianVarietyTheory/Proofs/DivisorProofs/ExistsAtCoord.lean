import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapNegApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponents

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace GlobalTheory.SplitCoord

theorem exists_at_coord : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d), X.J.det ≠ 0 → Y.J.det ≠ 0 → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v)
    (Z : Matrix (Fin n) (Fin d) (Fv F v)),
    (∃ x : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x ∧ x.map (piW t) = 0 ∧
      GlobalTheory.FlipMatch.coY σ X Y t 1 1 x = Z) ∧
    (∃ x : Matrix (Fin n) (Fin d) (AE F E), At (evFin F v) x ∧ x.map (piW (t.comp σ)) = 0 ∧
      GlobalTheory.FlipMatch.coX t 1 1 x = Z) := by
  intro F E _ _ _ _ _ σ hcm n d X Y hdX hdY v t Z
  have hA : IsUnit (X.J.map t).det := by
    rw [show (X.J.map t).det = (t : E →+* Fv F v) X.J.det from (RingHom.map_det _ _).symm]
    exact isUnit_iff_ne_zero.2 fun h => hdX ((t : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  have hB : IsUnit (Y.J.map t)ᵀ.det := by
    rw [Matrix.det_transpose, show (Y.J.map t).det = (t : E →+* Fv F v) Y.J.det from (RingHom.map_det _ _).symm]
    exact isUnit_iff_ne_zero.2 fun h => hdY ((t : E →+* Fv F v).injective (by rw [map_zero]; exact h))
  constructor
  · obtain ⟨x, hat, h0, h1⟩ := GlobalTheory.SplitComps.exists_mat_comps hcm v t (0 : Matrix (Fin n) (Fin d) (Fv F v))
      (-((X.J.map t)⁻¹ * Z * ((Y.J.map t)ᵀ)⁻¹))
    refine ⟨x, hat, h0, ?_⟩
    simp only [GlobalTheory.FlipMatch.coY, h1, Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc, Units.val_one,
      Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hA, Matrix.nonsing_inv_mul _ hB, Matrix.mul_one]
  · obtain ⟨x, hat, h0, h1⟩ := GlobalTheory.SplitComps.exists_mat_comps hcm v t Z (0 : Matrix (Fin n) (Fin d) (Fv F v))
    refine ⟨x, hat, h1, ?_⟩
    simp only [GlobalTheory.FlipMatch.coX, h0, inv_one, Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.SplitCoord
