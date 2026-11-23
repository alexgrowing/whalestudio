import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TransvOther

theorem mul_transv_apply {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (ca cb r c : Fin N) :
    (h * (1 + Matrix.single cb ca t)) r c = h r c + if c = ca then t * h r cb else 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  congr 1
  by_cases hc : c = ca
  · subst hc
    simp [Matrix.mul_apply, Matrix.single_apply, mul_comm]
  · simp [Matrix.mul_apply, Matrix.single_apply, hc, Ne.symm hc]

private lemma det_submatrix_mul_transvection_eq {N k : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (ca cb : Fin N)
    (hne : ca ≠ cb) (f g : Fin k → Fin N) (hg : Function.Injective g)
    (hJ : ca ∈ Set.range g ↔ cb ∈ Set.range g) :
    ((h * (1 + Matrix.single cb ca t)).submatrix f g).det = (h.submatrix f g).det := by
  by_cases hca : ca ∈ Set.range g
  · obtain ⟨qa, hqa⟩ := hca
    obtain ⟨qb, hqb⟩ := hJ.mp ⟨qa, hqa⟩
    have hq : qb ≠ qa := by
      rintro rfl
      exact hne (hqa.symm.trans hqb)
    have hiff : ∀ q, g q = ca ↔ q = qa := fun q => by
      rw [← hqa]
      exact hg.eq_iff
    have hM : (h * (1 + Matrix.single cb ca t)).submatrix f g
        = h.submatrix f g * (1 + Matrix.single qb qa t) := by
      ext p q
      simp only [Matrix.submatrix_apply, mul_transv_apply, hqb, hiff]
    have h1 : (1 + Matrix.single qb qa t : Matrix (Fin k) (Fin k) ℂ) = Matrix.transvection qb qa t :=
      rfl
    rw [hM, Matrix.det_mul, h1, Matrix.det_transvection_of_ne qb qa hq t, mul_one]
  · congr 1
    ext p q
    have hq : g q ≠ ca := fun hh => hca ⟨q, hh⟩
    simp only [Matrix.submatrix_apply, mul_transv_apply, hq, if_false, add_zero]

theorem minorIJ_transv {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (ca cb : Fin N) (hne : ca ≠ cb)
    (I J : Finset (Fin N)) (hJ : ca ∈ J ↔ cb ∈ J) :
    minorIJ (h * (1 + Matrix.single cb ca t)) I J = minorIJ h I J := by
  unfold minorIJ
  split_ifs with e
  · apply det_submatrix_mul_transvection_eq h t ca cb hne
    · exact (J.orderEmbOfFin _).injective
    · rw [Finset.range_orderEmbOfFin, Finset.mem_coe, Finset.mem_coe]
      exact hJ
  · rfl

theorem minorIJ_other_step : ∀ (N j : ℕ) (a b ca cb : Fin N), j ≤ N → (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) (i : Fin N), i ≠ a → ∀ I, minorIJ (h * (1 + Matrix.single cb ca t)) I (stepCols N j i) = minorIJ h I (stepCols N j i) := by
  intro N j a b ca cb hjN hb hab hca hcb h t i hi I
  apply minorIJ_transv h t ca cb
  · intro heq
    have := congrArg Fin.val heq
    omega
  · simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
    unfold lastCol at hca
    have hi' : (i : ℕ) ≠ a := fun h' => hi (Fin.ext h')
    have := a.isLt
    have := b.isLt
    have := i.isLt
    have := ca.isLt
    have := cb.isLt
    split_ifs at hca ⊢ <;> omega

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.TransvOther
