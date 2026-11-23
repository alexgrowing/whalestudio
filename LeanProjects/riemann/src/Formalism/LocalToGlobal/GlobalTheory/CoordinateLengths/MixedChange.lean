import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.IntSpanLeRat

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LemB

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms NumberField MvPolynomial Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Classical

variable {D : D7} {u : D.what₂.Word}

def mixF (τ₀ : D.what₂.Tau) (B B' : GL (Fin (D.R.N 0)) D.host.E) : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ :=
  fun τ => if τ = τ₀ then atInf (embT D) (B'⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ
    else atInf (embT D) (B⁻¹ : GL (Fin (D.R.N 0)) D.host.E).1 τ

private theorem atInf_mul' (X Y : GL (Fin (D.R.N 0)) D.host.E) (τ : D.what₂.Tau) :
    atInf (embT D) (X * Y : GL (Fin (D.R.N 0)) D.host.E).1 τ =
      atInf (embT D) X.1 τ * atInf (embT D) Y.1 τ := by
  simp only [atInf, Units.val_mul, Matrix.map_mul]

private theorem atInf_one' (τ : D.what₂.Tau) :
    atInf (embT D) (1 : GL (Fin (D.R.N 0)) D.host.E).1 τ = 1 := by
  simp only [atInf, Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem mixed_change (w : D.what₂.places.Pl) (hw : OverT D u w) (τ₀ : D.what₂.Tau)
    {L L' : Set (Fin (D.R.N 0) → D.host.E)} {B B₁ B' B₁' : GL (Fin (D.R.N 0)) D.host.E}
    (hB : IsLocBasis (D.mem u).A.T L B) (hB₁ : IsLocBasis (D.mem u).A.T L B₁)
    (hB' : IsLocBasis (D.mem u).A.T L' B') (hB₁' : IsLocBasis (D.mem u).A.T L' B₁')
    (P : MvPolynomial (D.what₂.Tau × Fin (D.R.N 0) × Fin (D.R.N 0)) ℂ)
    (hP : P ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0)) :
    ∃ P₁ ∈ Formalism.L2.Forms.IntSpan D w ((D.fm u).lam 0), ∀ y,
      fnOf (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) (shiftOf (lamT u 0)) (mixF τ₀ B B') P y =
        fnOf (gramC (gramN D 0 (Nat.zero_le _)) (embT D)) (shiftOf (lamT u 0)) (mixF τ₀ B₁ B₁') P₁ y := by
  let N : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ := fun τ =>
    if τ = τ₀ then atInf (embT D) (B'⁻¹ * B₁' : GL (Fin (D.R.N 0)) D.host.E).1 τ
    else atInf (embT D) (B⁻¹ * B₁ : GL (Fin (D.R.N 0)) D.host.E).1 τ
  let N' : D.what₂.Tau → Matrix (Fin (D.R.N 0)) (Fin (D.R.N 0)) ℂ := fun τ =>
    if τ = τ₀ then atInf (embT D) (B₁'⁻¹ * B' : GL (Fin (D.R.N 0)) D.host.E).1 τ
    else atInf (embT D) (B₁⁻¹ * B : GL (Fin (D.R.N 0)) D.host.E).1 τ
  have hmul : ∀ τ, N τ * N' τ = 1 := by
    intro τ
    by_cases hτ : τ = τ₀
    · simp only [N, N', if_pos hτ]
      rw [← atInf_mul', show B'⁻¹ * B₁' * (B₁'⁻¹ * B') = 1 by group, atInf_one']
    · simp only [N, N', if_neg hτ]
      rw [← atInf_mul', show B⁻¹ * B₁ * (B₁⁻¹ * B) = 1 by group, atInf_one']
  have hN : ∀ τ a b, N τ a b ∈ bwA_Ow D w := by
    intro τ a b
    by_cases hτ : τ = τ₀
    · simp only [N, if_pos hτ]
      exact bwG_change_mem D u w hw τ hB₁' hB' a b
    · simp only [N, if_neg hτ]
      exact bwG_change_mem D u w hw τ hB₁ hB a b
  have hN' : ∀ τ a b, N' τ a b ∈ bwA_Ow D w := by
    intro τ a b
    by_cases hτ : τ = τ₀
    · simp only [N', if_pos hτ]
      exact bwG_change_mem D u w hw τ hB' hB₁' a b
    · simp only [N', if_neg hτ]
      exact bwG_change_mem D u w hw τ hB hB₁ a b
  have hfac : mixF τ₀ B B' = fun τ => N τ * mixF τ₀ B₁ B₁' τ := by
    funext τ
    by_cases hτ : τ = τ₀
    · simp only [mixF, N, if_pos hτ]
      rw [← atInf_mul', show B'⁻¹ * B₁' * B₁'⁻¹ = B'⁻¹ by group]
    · simp only [mixF, N, if_neg hτ]
      rw [← atInf_mul', show B⁻¹ * B₁ * B₁⁻¹ = B⁻¹ by group]
  refine ⟨MvPolynomial.C (∏ τ, (N τ).det ^ shiftOf (lamT u 0) τ) * subP N P,
    bwG_intSpan_allSubP D w _ N _
      (fun τ => local_GL_stabilises_lattice D w _ _ _ (N τ) (N' τ) (hmul τ) (hN τ) (hN' τ)) P hP, fun y => ?_⟩
  rw [hfac, fnOf_mul]

end Formalism.L2.GlobalTheoryTheory.LemB
