import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PPartRealSmul
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.SgBlocks

variable {j j' : ℕ}

theorem blocks_eqs (u : Matrix (Sg j j') (Sg j j') ℂ) (h : IsSgU u) :
    u.toBlocks₁₁ᴴ * u.toBlocks₁₁ - u.toBlocks₂₁ᴴ * u.toBlocks₂₁ = 1 ∧
    u.toBlocks₁₂ᴴ * u.toBlocks₁₂ - u.toBlocks₂₂ᴴ * u.toBlocks₂₂ = -1 ∧
    u.toBlocks₁₁ᴴ * u.toBlocks₁₂ - u.toBlocks₂₁ᴴ * u.toBlocks₂₂ = 0 := by
  have hu : u = fromBlocks u.toBlocks₁₁ u.toBlocks₁₂ u.toBlocks₂₁ u.toBlocks₂₂ :=
    (fromBlocks_toBlocks u).symm
  generalize u.toBlocks₁₁ = a at hu ⊢
  generalize u.toBlocks₁₂ = b at hu ⊢
  generalize u.toBlocks₂₁ = c at hu ⊢
  generalize u.toBlocks₂₂ = d at hu ⊢
  subst hu
  unfold IsSgU sgI at h
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply] at h
  obtain ⟨h1, h2, h3, h4⟩ := Matrix.fromBlocks_inj.1 h
  simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg,
    Matrix.neg_mul] at h1 h2 h3 h4
  refine ⟨?_, ?_, ?_⟩
  · simpa [sub_eq_add_neg] using h1
  · simpa [sub_eq_add_neg] using h4
  · simpa [sub_eq_add_neg] using h2

theorem det_unit_of_eq {m k : ℕ} {x : Matrix (Fin m) (Fin m) ℂ} {y : Matrix (Fin k) (Fin m) ℂ}
    (e : xᴴ * x = 1 + yᴴ * y) : IsUnit x.det := by
  have pd : (xᴴ * x).PosDef := by
    rw [e]
    exact Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self y)
  have hu : IsUnit (xᴴ * x).det := (Matrix.isUnit_iff_isUnit_det _).1 pd.isUnit
  rw [Matrix.det_mul] at hu
  exact isUnit_of_mul_isUnit_right hu

theorem moebW_zero (u : Matrix (Sg j j') (Sg j j') ℂ) :
    moebW u 0 = u.toBlocks₂₁ * u.toBlocks₁₁⁻¹ := by
  simp [moebW]

theorem one_sub_mul_eq {a : Matrix (Fin j) (Fin j) ℂ} {b : Matrix (Fin j) (Fin j') ℂ}
    {c : Matrix (Fin j') (Fin j) ℂ} {d : Matrix (Fin j') (Fin j') ℂ}
    (ha : IsUnit a.det) (hd : IsUnit d.det) (h2 : bᴴ * b - dᴴ * d = -1)
    (h3 : aᴴ * b - cᴴ * d = 0) :
    (1 - (c * a⁻¹) * (c * a⁻¹)ᴴ) * (d * dᴴ) = 1 := by
  have hab : aᴴ * b = cᴴ * d := sub_eq_zero.1 h3
  have haH : IsUnit aᴴ.det := by
    rw [det_conjTranspose]; exact ha.star
  have hdH : IsUnit dᴴ.det := by
    rw [det_conjTranspose]; exact hd.star

  have hWH : (c * a⁻¹)ᴴ * d = b := by
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, Matrix.mul_assoc, ← hab,
      Matrix.nonsing_inv_mul_cancel_left _ _ haH]
  have hWH' : dᴴ * (c * a⁻¹) = bᴴ := by
    have := congrArg conjTranspose hWH
    simpa [conjTranspose_mul] using this
  have hdd : dᴴ * d = 1 + bᴴ * b := by
    rw [← sub_eq_zero]
    have : bᴴ * b - dᴴ * d + 1 = 0 := by rw [h2]; abel
    rw [← neg_eq_zero, ← this]; abel

  have key : dᴴ * ((1 - (c * a⁻¹) * (c * a⁻¹)ᴴ) * (d * dᴴ)) = dᴴ * 1 := by
    calc dᴴ * ((1 - (c * a⁻¹) * (c * a⁻¹)ᴴ) * (d * dᴴ))
        = (dᴴ * d - (dᴴ * (c * a⁻¹)) * ((c * a⁻¹)ᴴ * d)) * dᴴ := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
      _ = dᴴ * 1 := by
          rw [hWH, hWH', hdd]; simp
  have := congrArg (fun x => (dᴴ)⁻¹ * x) key
  simpa only [Matrix.nonsing_inv_mul_cancel_left _ _ hdH] using this

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.SgBlocks

open GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.SgBlocks in

theorem GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.sgU_blocks : ∀ (j j' : ℕ) (u : Matrix (Sg j j') (Sg j j') ℂ), IsSgU u → IsUnit u.toBlocks₁₁.det ∧ IsUnit u.toBlocks₂₂.det ∧ (1 - moebW u 0 * (moebW u 0)ᴴ) * (u.toBlocks₂₂ * u.toBlocks₂₂ᴴ) = 1 ∧ (1 - moebW u 0 * (moebW u 0)ᴴ).PosDef := by
  intro j j' u hu
  obtain ⟨h1, h2, h3⟩ := blocks_eqs u hu
  have ha : IsUnit u.toBlocks₁₁.det := by
    refine det_unit_of_eq (y := u.toBlocks₂₁) ?_
    rw [← h1]; abel
  have hd : IsUnit u.toBlocks₂₂.det := by
    refine det_unit_of_eq (y := u.toBlocks₁₂) ?_
    rw [← sub_eq_zero]
    have : u.toBlocks₁₂ᴴ * u.toBlocks₁₂ - u.toBlocks₂₂ᴴ * u.toBlocks₂₂ + 1 = 0 := by rw [h2]; abel
    rw [← neg_eq_zero, ← this]; abel
  have hm : (1 - moebW u 0 * (moebW u 0)ᴴ) * (u.toBlocks₂₂ * u.toBlocks₂₂ᴴ) = 1 := by
    rw [moebW_zero]
    exact one_sub_mul_eq ha hd h2 h3
  refine ⟨ha, hd, hm, ?_⟩
  have hpd : (u.toBlocks₂₂ * u.toBlocks₂₂ᴴ).PosDef := by
    have h := Matrix.PosDef.one.mul_mul_conjTranspose_same (B := u.toBlocks₂₂)
      (Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hd))
    simpa using h
  have he : 1 - moebW u 0 * (moebW u 0)ᴴ = (u.toBlocks₂₂ * u.toBlocks₂₂ᴴ)⁻¹ :=
    (Matrix.inv_eq_left_inv hm).symm
  rw [he]
  exact hpd.inv
