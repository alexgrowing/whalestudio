import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundSingleLiftOfDefinitions

open Finset Module NumberField Formalism.HN Formalism.L2.Indef Formalism.L2.Indef.Tree

noncomputable section

namespace GlobalTheory.MeasureLeaf

section Bound₂

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def withLevel (P : SlopeBoundParameters) (t : ℝ) : SlopeBoundParameters := { P with g12 := t }

def OneConstant {d : ℕ} (X X' : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (c : InfinitePlace K → ℝ) : Prop :=
  ∀ v, 0 < c v ∧ ∀ x y, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y =
    (c v : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X' v x y

theorem lcv_of_oneConstant [IsTotallyComplex K] {d : ℕ} (hd : 0 < d)
    (X X' : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v, IsUnit (X v).det) (hX' : ∀ v, IsUnit (X' v).det)
    (c : InfinitePlace K → ℝ) (hc : OneConstant X X' c) (M : Submodule (𝓞 K) (Fin d → K))
    (hM : Submodule.IsLattice K M) :
    Formalism.DivisionValues.lcv X M / (d : ℝ) = Formalism.DivisionValues.lcv X' M / (d : ℝ) + 2 / (finrank ℚ K : ℝ) * ∑ v, Real.log (c v) := by
  have hli : LinearIndependent K (fun i : Fin d => (Pi.basisFun K (Fin d)) i) := (Pi.basisFun K (Fin d)).linearIndependent
  rw [(Formalism.DivisionValues.covolume_via_basis K d X hX M hM _ hli).2, (Formalism.DivisionValues.covolume_via_basis K d X' hX' M hM _ hli).2]
  have hv : ∀ v, Real.log (Formalism.DivisionValues.gram X v (fun i : Fin d => (Pi.basisFun K (Fin d)) i)).det.re =
      d * Real.log (c v) + Real.log (Formalism.DivisionValues.gram X' v (fun i : Fin d => (Pi.basisFun K (Fin d)) i)).det.re := by
    intro v
    have e : Formalism.DivisionValues.gram X v (fun i : Fin d => (Pi.basisFun K (Fin d)) i) =
        (c v : ℂ) • Formalism.DivisionValues.gram X' v (fun i : Fin d => (Pi.basisFun K (Fin d)) i) := by
      ext a b
      simp only [Formalism.DivisionValues.gram, gramPl, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
      exact (hc v).2 _ _
    have hne : (Formalism.DivisionValues.gram X' v (fun i : Fin d => (Pi.basisFun K (Fin d)) i)).det.re ≠ 0 := by
      have g : Formalism.DivisionValues.gram X' v (fun i : Fin d => (Pi.basisFun K (Fin d)) i) =
          ((X' v)⁻¹).conjTranspose * (X' v)⁻¹ := by
        ext a b
        simp [Formalism.DivisionValues.gram, gramPl, Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, Formalism.HermitianLatticesTheory.vecAt, Matrix.mul_apply,
          Matrix.mulVec, dotProduct, Pi.single_apply, apply_ite v.embedding]
      rw [g, Matrix.det_mul, Matrix.det_conjTranspose]
      have hu : ((X' v)⁻¹).det ≠ 0 := (Matrix.isUnit_nonsing_inv_det _ (hX' v)).ne_zero
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
      exact (Complex.normSq_pos.mpr hu).ne'
    rw [e, Matrix.det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
      Real.log_mul (pow_pos (hc v).1 d).ne' hne, Real.log_pow]
  simp only [hv, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp
  ring

end Bound₂

end GlobalTheory.MeasureLeaf
