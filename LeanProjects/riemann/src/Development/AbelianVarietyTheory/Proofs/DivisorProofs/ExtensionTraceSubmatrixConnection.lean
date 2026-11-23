import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChgFromBlocksEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernOneEqNegDdcLogDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensDetWeightEqNegLeviLog
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockChangeOfBasisViaTwoFamiliesImplicit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.LminorMapConj
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

namespace GlobalTheory.StepTrace

theorem emb_inj {N : ℕ} (i : Fin N) : Function.Injective (emb i) := by
  rintro (a | a) (b | b) h
  · simp only [emb, Sum.elim_inl] at h
    exact congrArg Sum.inl (Fin.castLE_injective _ h)
  · simp only [emb, Sum.elim_inl, Sum.elim_inr] at h
    exact absurd (congrArg Fin.val h) (by simp [Fin.coe_castLE]; exact a.isLt.ne)
  · simp only [emb, Sum.elim_inl, Sum.elim_inr] at h
    exact absurd (congrArg Fin.val h) (by simp [Fin.coe_castLE]; exact (b.isLt.ne).symm)
  · rw [Subsingleton.elim a b]

theorem sum_castLE_eq {N : ℕ} (i : Fin N) (f : Fin N → ℂ) :
    ∑ a : Fin i, f (Fin.castLE i.isLt.le a) = ∑ a ∈ Finset.Iio i, f a := by
  rw [← Finset.sum_image (s := Finset.univ) (g := Fin.castLE i.isLt.le)
    (fun x _ y _ h => Fin.castLE_injective _ h)]
  congr 1
  ext a
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Iio]
  constructor
  · rintro ⟨b, rfl⟩; exact Fin.lt_def.2 (by simp)
  · intro h; exact ⟨⟨a, Fin.lt_def.1 h⟩, Fin.ext (by simp)⟩

theorem extTrace_step_eq_sum : ∀ {N : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (H : E → Matrix (Fin N) (Fin N) ℂ) (p : E) (i : Fin N), MContDiffAt 2 H p → (∀ᶠ v in 𝓝 p, (H v).PosDef) → H p = 1 → ∀ ξ η : E, extTrace (fun v => (H v).submatrix (emb i) (emb i)) p ξ η = kappa * ∑ a ∈ Finset.Iio i, conn H p ξ i a * starRingEnd ℂ (conn H p η i a) := by
  intro N E _ _ _ _ H p i h2 hp h1 ξ η
  have hinj := emb_inj i
  have hS1 : MContDiffAt 1 (fun v => (H v).submatrix (emb i) (emb i)) p :=
    (h2.of_le (by norm_num)).submatrix _ _
  have hSp : ∀ᶠ v in 𝓝 p, ((H v).submatrix (emb i) (emb i)).PosDef :=
    hp.mono fun v hv => hv.submatrix hinj
  have hS1' : (H p).submatrix (emb i) (emb i) = 1 := by
    rw [h1]; exact Matrix.submatrix_one _ hinj
  rw [extTrace_eq_sum_of_eq_one hS1 hSp hS1' ξ η, ← sum_castLE_eq]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fin.sum_univ_one]
  simp only [conn, h1, transpose_one, inv_one, Matrix.one_mul, transpose_apply]
  rfl

end GlobalTheory.StepTrace
