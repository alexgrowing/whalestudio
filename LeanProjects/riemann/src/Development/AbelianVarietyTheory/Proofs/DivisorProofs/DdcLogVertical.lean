import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff

namespace GlobalTheory.DdcVert

theorem ddc_log_vert {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ} {B : Set E}
    {h : Pt E g → ℝ} (hB : IsOpen B) (hh : ContDiffOn ℝ ∞ h (cov B g))
    (hpos : ∀ P ∈ cov B g, 0 < h P) {b : E} (hb : b ∈ B) (z v w : Fin g → ℂ) :
    ddc (fun Q => Real.log (h Q)) (b, z) (0, v) (0, w) =
      (1 / (4 * π)) *
        (fderiv ℝ (fun z' => fderiv ℝ (fun z'' => Real.log (h (b, z''))) z' (Complex.I • v)) z w -
          fderiv ℝ (fun z' => fderiv ℝ (fun z'' => Real.log (h (b, z''))) z' (Complex.I • w)) z v) := by
  set u : Pt E g → ℝ := fun Q => Real.log (h Q) with hu
  have hU : IsOpen (cov B g) := hB.prod isOpen_univ
  have hmem : ∀ z' : Fin g → ℂ, ((b, z') : Pt E g) ∈ cov B g := fun z' => ⟨hb, Set.mem_univ _⟩
  have hu_cd : ContDiffOn ℝ ∞ u (cov B g) := hh.log (fun P hP => (hpos P hP).ne')
  have hu_at : ∀ z' : Fin g → ℂ, ContDiffAt ℝ ∞ u (b, z') :=
    fun z' => hu_cd.contDiffAt (hU.mem_nhds (hmem z'))
  have hinr : ∀ z' : Fin g → ℂ, HasFDerivAt (fun z'' : Fin g → ℂ => ((b, z'') : Pt E g))
      (ContinuousLinearMap.inr ℝ E (Fin g → ℂ)) z' := fun z' => hasFDerivAt_prodMk_right b z'
  have key1 : ∀ z' y : Fin g → ℂ,
      fderiv ℝ u (b, z') (0, y) = fderiv ℝ (fun z'' => u (b, z'')) z' y := by
    intro z' y
    have hd : DifferentiableAt ℝ u (b, z') := (hu_at z').differentiableAt (by simp)
    exact (DFunLike.congr_fun (hd.hasFDerivAt.comp z' (hinr z')).fderiv y).symm
  have key2 : ∀ y w' : Fin g → ℂ,
      fderiv ℝ (fun Q => fderiv ℝ u Q (0, y)) (b, z) (0, w') =
        fderiv ℝ (fun z' => fderiv ℝ (fun z'' => u (b, z'')) z' y) z w' := by
    intro y w'
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ u) (b, z) := (hu_at z).fderiv_right (by exact WithTop.coe_le_coe.2 le_top)
    have hφ : DifferentiableAt ℝ (fun Q => fderiv ℝ u Q (0, y)) (b, z) :=
      (h1.differentiableAt one_ne_zero).clm_apply (differentiableAt_const _)
    have he : (fun z' => fderiv ℝ (fun z'' => u (b, z'')) z' y) =
        (fun Q => fderiv ℝ u Q (0, y)) ∘ (fun z'' : Fin g → ℂ => ((b, z'') : Pt E g)) := by
      funext z'; simp only [Function.comp_apply, key1]
    rw [he]
    exact (DFunLike.congr_fun (hφ.hasFDerivAt.comp z (hinr z)).fderiv w').symm
  have hs : ∀ y : Fin g → ℂ, Complex.I • ((0 : E), y) = ((0 : E), Complex.I • y) := by
    intro y; simp [Prod.smul_mk]
  unfold ddc
  rw [hs v, hs w, key2, key2]

end GlobalTheory.DdcVert
