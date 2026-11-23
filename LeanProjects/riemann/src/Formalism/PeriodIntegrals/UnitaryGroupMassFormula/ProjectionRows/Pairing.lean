import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.LatticeFinitelyGenerated
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.LocFree
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.Adapted

noncomputable section

namespace PI.DvRows

open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.HermitianLatticesTheory

section Gen

variable {K : Type} [Field K] [NumberField K]

lemma det_ne_zero_of_comb {V : Type} [AddCommGroup V] [Module K V] {r : ℕ} (x y : Fin r → V)
    (P : Matrix (Fin r) (Fin r) K) (hy : LinearIndependent K y)
    (hxy : ∀ j, y j = ∑ c, P c j • x c) : P.det ≠ 0 := by
  intro h0
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  change P.mulVec c = 0 at hc
  apply hc0
  have hsum : ∑ j, c j • y j = 0 := by
    simp_rw [hxy, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have : ∀ l, ∑ j, (c j * P l j) • x l = ((P.mulVec c) l) • x l := by
      intro l
      rw [← Finset.sum_smul]
      congr 1
      simp [Matrix.mulVec, dotProduct, mul_comm]
    simp_rw [this, hc]
    simp
  funext i
  exact (Fintype.linearIndependent_iff.1 hy) c hsum i

lemma vAdd_inv (w : HeightOneSpectrum (𝓞 K)) (x : K) : vAdd w x⁻¹ = -vAdd w x := by
  unfold vAdd
  rw [map_inv₀, WithZero.log_inv, neg_neg]

lemma vAdd_unit (w : HeightOneSpectrum (𝓞 K)) (T : 𝓞 K) (hT : T ∉ w.asIdeal) :
    vAdd w (algebraMap (𝓞 K) K T) = 0 := by
  have h1 : w.valuation K (algebraMap (𝓞 K) K T) = 1 := by
    refine le_antisymm (w.valuation_le_one T) ?_
    by_contra hlt
    exact hT ((w.valuation_lt_one_iff_mem T).1 (not_le.1 hlt))
  unfold vAdd
  rw [h1, WithZero.log_one, neg_zero]

end Gen

end PI.DvRows
