import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PhiFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef

noncomputable section

open Finset Matrix
open scoped ComplexOrder

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem posDef_conj_toMK {ε : Fin n → Bool} (k : KG ε) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    (toMK k⁻¹ * x * toMK k).PosDef := by
  rw [toMK_inv]
  refine hx.conjTranspose_mul_mul_same ?_
  intro a b hab
  have h := congrArg (fun y => (toMK k)ᴴ.mulVec y) hab
  simpa only [Matrix.mulVec_mulVec, (toMK_facts k).1, Matrix.one_mulVec] using h

theorem muNext_add_smul (μ D : Fin n → ℤ) (t : ℤ) (i : Fin n) :
    muNext (μ + t • D) i = muNext μ i + t * muNext D i := by
  unfold muNext
  split_ifs <;> simp

theorem phiM_add_smul (μ D : Fin n → ℤ) (t : ℕ) {y : Matrix (Fin n) (Fin n) ℂ} (hy : y ∈ OmegaSet n) :
    PhiM (μ + (t : ℤ) • D) y = PhiM μ y * PhiM D y ^ t := by
  unfold PhiM
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h0 : lead ((i : ℕ) + 1) y ≠ 0 := hy i
  rw [muNext_add_smul, ← zpow_natCast, ← _root_.zpow_mul, ← zpow_add₀ h0]
  congr 1
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem phiMul : PhiMul := by
  intro n ε μ t x hx k
  have hy := posDef_conj_toMK k hx
  have h1 := phiM_posDef μ hy
  have h2 := phiM_posDef (Dz n) hy
  refine ⟨h1.1, ?_⟩
  unfold phiK
  rw [phiM_add_smul μ (Dz n) t (posSet_subset_omega hy)]
  have e1 : PhiM μ (toMK k⁻¹ * x * toMK k) = ((PhiM μ (toMK k⁻¹ * x * toMK k)).re : ℂ) :=
    Complex.ext (by simp) (by simp [h1.2])
  have e2 : PhiM (Dz n) (toMK k⁻¹ * x * toMK k) = ((PhiM (Dz n) (toMK k⁻¹ * x * toMK k)).re : ℂ) :=
    Complex.ext (by simp) (by simp [h2.2])
  rw [e1, e2, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
  simp only [Complex.ofReal_re]

end PositivityTheory.RgFd
