import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.PairOfLiftAlt

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private def mulHomeo {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n d : ℕ}
    (a : (Matrix (Fin n) (Fin n) k)ˣ) (c : (Matrix (Fin d) (Fin d) k)ˣ) :
    Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin n) (Fin d) k where
  toFun X := a.val * X * c.val
  invFun Y := (a⁻¹).val * Y * (c⁻¹).val
  left_inv X := by
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  right_inv Y := by
    simp only [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
    simp only [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

private def transHomeo {k : Type} [TopologicalSpace k] {n d : ℕ} :
    Matrix (Fin n) (Fin d) k ≃ₜ Matrix (Fin d) (Fin n) k where
  toFun X := X.transpose
  invFun Y := Y.transpose
  left_inv X := Matrix.transpose_transpose X
  right_inv Y := Matrix.transpose_transpose Y
  continuous_toFun := continuous_id.matrix_transpose
  continuous_invFun := continuous_id.matrix_transpose

private theorem comp_homeo_mem_SB {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    {f : Y → ℂ} (hf : f ∈ SB Y) : (fun x => f (e x)) ∈ SB X :=
  ⟨hf.1.comp_continuous e.continuous, hf.2.comp_homeomorph e⟩

theorem UpperTheory.Gal.TP.Loc.keepsSB :
    UpperTheory.Gal.TP.Loc.KeepsSB := by
  intro k _ _ _ _ n d
  refine ⟨fun ν b g h Φ hΦ => ?_, fun Ψ hΨ => comp_homeo_mem_SB transHomeo hΨ⟩
  have hc := comp_homeo_mem_SB (mulHomeo g⁻¹ (GlobalTheory.SplitFlip.invT h)) hΦ
  have key : GlobalTheory.SplitFlip.omA ν b g h Φ =
      ((↑(ν (GlobalTheory.SplitFlip.gdet g))⁻¹ * ↑(b (GlobalTheory.SplitFlip.gdet h)) *
        GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (-↑(Fintype.card (Fin d)) / 2) *
        GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet h) (-↑(Fintype.card (Fin n)) / 2) : ℂ) •
        fun X => Φ (mulHomeo g⁻¹ (GlobalTheory.SplitFlip.invT h) X)) := by
    funext X
    rfl
  rw [key]
  exact (SB _).smul_mem _ hc
