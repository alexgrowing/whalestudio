import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

theorem isNm_ue_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ h : HA (AF F) σ J, IsNm σ (ue (AF F) σ J h) 1 := by
  intro F E _ _ _ _ _ σ _ J hJ h
  have hg : cT (sigR (AF F) σ) ((HA.mat (AF F) σ J h : GL (Fin 1) (AF F ⊗[F] E)) :
      Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)) * JR (AF F) J *
      ((HA.mat (AF F) σ J h : GL (Fin 1) (AF F ⊗[F] E)) :
      Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)) = JR (AF F) J := h.2
  have hx : ((ue (AF F) σ J h : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      ((HA.mat (AF F) σ J h : GL (Fin 1) (AF F ⊗[F] E)) :
      Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)) 0 0 := by
    simp only [ue, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]
  have he := congrFun (congrFun hg 0) 0
  simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, cT, JR, Matrix.transpose_apply,
    Matrix.map_apply, Fin.default_eq_zero, Fin.isValue] at he
  have hj : J 0 0 ≠ 0 := by
    have := hJ.2
    rwa [Matrix.det_fin_one] at this
  have hu : IsUnit (inclR (F := F) (AF F) (J 0 0)) := (IsUnit.mk0 _ hj).map (inclR (F := F) (AF F))
  show ((1 : (AF F)ˣ) : AF F) ⊗ₜ[F] (1 : E) = sigR (AF F) σ _ * _
  rw [hx, Units.val_one, ← Algebra.TensorProduct.one_def]
  apply hu.mul_left_cancel
  rw [mul_one]
  exact he.symm.trans (by ring)

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
