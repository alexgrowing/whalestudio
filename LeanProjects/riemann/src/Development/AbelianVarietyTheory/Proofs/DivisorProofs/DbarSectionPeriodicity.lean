import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff

namespace GlobalTheory.FlatAcycShift

theorem dbar_coeff_transl : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ} {B : Set E}
    {τ : E → Matrix (Fin g) (Fin g) ℂ} {M : Submodule ℤ (Fl g)} {j : Fl g → Pt E g → ℂ}
    (hB : IsOpen B) (hj : IsFactor B τ M j) {b : E} (hb : b ∈ B) {m : ℕ}
    (f : (Fin g → ℂ) → Ext m) (hf : IsSec τ M j b f) (l : Fl g) (hl : l ∈ M) (z : Fin g → ℂ)
    (c : Fin g) (S : Finset (Fin m)),
    d01 (fun z' => f z' S) (z + per (τ b) l) (ev c) = j l (b, z) * d01 (fun z' => f z' S) z (ev c) := by
  intro E _ _ g B τ M j hB hj b hb m f hf l hl z c S
  have hopen : IsOpen (cov B g) := hB.prod isOpen_univ
  have hmem : ((b, z) : Pt E g) ∈ cov B g := ⟨hb, Set.mem_univ _⟩
  have hjd : DifferentiableAt ℂ (fun z' : Fin g → ℂ => j l (b, z')) z := by
    have h1 : DifferentiableAt ℂ (j l) (b, z) :=
      ((hj.1 l hl).1).differentiableAt (hopen.mem_nhds hmem)
    exact h1.comp z ((differentiableAt_const b).prodMk differentiableAt_id)
  have hfd : DifferentiableAt ℝ (fun z' => f z' S) z := by
    have h2 : Differentiable ℝ f := hf.1.differentiable (by simp)
    exact differentiableAt_pi.1 (h2 z) S
  have hfun : (fun z' => f (z' + per (τ b) l) S) = fun z' => j l (b, z') * f z' S := by
    funext z'
    rw [hf.2 l hl z']
    rfl
  rw [← dbar_comp_translate (fun z' => f z' S) z (per (τ b) l) (ev c), hfun,
    dbar_mul_leibniz (hjd.restrictScalars ℝ) hfd, dbar_eq_zero_of_holomorphic hjd]
  simp

end GlobalTheory.FlatAcycShift
