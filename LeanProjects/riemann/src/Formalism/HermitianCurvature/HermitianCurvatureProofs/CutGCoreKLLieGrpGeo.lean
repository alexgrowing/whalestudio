import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankFour
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsFrameTwo

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

namespace KLG

open Formalism.FourierDecayAlt.P.HermitianFormRankFour

variable {k r : ℕ}

def cvec2 (k r : ℕ) (z e : Fin (2 * r + k + 1) → ℂ) : JJ r ⊕ Unit → Fin (2 * r + k + 1) → ℂ :=
  Sum.elim (cvec k r z) (fun _ => e)

def cvec2' (k r : ℕ) (z e : Fin (2 * r + k + 1) → ℂ) : JJ r ⊕ Unit → Fin (2 * r + k + 1) → ℂ :=
  Sum.elim (cvec' k r z) (fun _ => e)

theorem sum_unitB {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (B : Matrix (Fin m) (Fin m) ℂ) :
    colM Bs * B * ((colM Bs)ᴴ * Hpk k r) = ∑ p : Fin m × Fin m, B p.1 p.2 • unitB (Hpk k r) Bs p.1 p.2 := by
  ext i j
  have hu : ∀ a b, unitB (Hpk k r) Bs a b i j = Bs a i * ∑ q, star (Bs b q) * Hpk k r q j := by
    intro a b
    simp only [unitB, Matrix.of_apply, herm, dotProduct, Matrix.mulVec, bvec, Pi.star_apply]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [Pi.single_apply]
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, hu, Matrix.mul_apply, colM, Matrix.of_apply,
    Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, b]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem stab_exp {z e : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (he : inWb k r e)
    (hez : herm (Hpk k r) e z = 0) (hee : herm (Hpk k r) e e = 1) {Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [z, e] Bs) {h : Mx k r} (hh : h ∈ UWset k r z) (hhe : h *ᵥ e = e) :
    ∃ B : Matrix (Fin (k - 1)) (Fin (k - 1)) ℂ, Bᴴ = -B ∧
      NormedSpace.exp (colM Bs * B * ((colM Bs)ᴴ * Hpk k r)) = h := by
  have hzz : herm (Hpk k r) z z ≠ 0 := by
    intro e0
    unfold Tz at hT
    rw [e0] at hT
    simp at hT
  have hBz : IsFrameOf k r [z] Bs := ⟨hB.1, hB.2.1, fun a v hv => hB.2.2 a v (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; exact Or.inl hv)⟩
  have hE : IsFrameOf k r [z] (fun _ : Fin 1 => e) := ⟨fun _ => he, fun a b => by
    simp [Subsingleton.elim a b, hee], fun _ v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    subst hv
    exact hez⟩
  have hBe : ∀ a, herm (Hpk k r) (Bs a) e = 0 := fun a => hB.2.2 a e (by simp)
  have hBe' : ∀ a, herm (Hpk k r) e (Bs a) = 0 := fun a => by rw [← Qx2.herm_star, hBe a, star_zero]
  have g1 : (colM Bs)ᴴ * Hpk k r * colM Bs = 1 := by
    ext a b
    rw [gramM_apply, hB.2.1, Matrix.one_apply]
    simp [eq_comm]
  have g2 : (colM Bs)ᴴ * Hpk k r * colM (cvec2 k r z e) = 0 := by
    ext a j
    rw [gramM_apply]
    rcases j with j | _
    · exact gram_VC hBz a j
    · exact hBe' a
  have g3 : (colM (cvec2' k r z e))ᴴ * Hpk k r * colM Bs = 0 := by
    ext j a
    rw [gramM_apply]
    rcases j with j | _
    · exact gram_CV hBz a j
    · exact hBe a
  have g4 : (colM (cvec2' k r z e))ᴴ * Hpk k r * colM (cvec2 k r z e) = 1 := by
    ext i j
    rw [gramM_apply, Matrix.one_apply]
    rcases i with i | _ <;> rcases j with j | _
    · simp only [cvec2, cvec2', Sum.elim_inl, Sum.inl.injEq]
      exact gram_CC hz hzz i j
    · simp only [cvec2, cvec2', Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
      exact gram_CV hE 0 i
    · simp only [cvec2, cvec2', Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
      exact gram_VC hE 0 j
    · simp [cvec2, cvec2', hee]
  have hJ : Fintype.card (JJ r ⊕ Unit) ≤ Fintype.card (Fin (2 * r + k + 1)) := by
    have h1 := Matrix.rank_mul_le_right ((colM (cvec2' k r z e))ᴴ * Hpk k r) (colM (cvec2 k r z e))
    rw [g4, Matrix.rank_one] at h1
    exact h1.trans (Matrix.rank_le_card_height _)
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at hJ
  have hc := complete (Fintype.equivOfCardEq (by simp; omega)) g1 g2 g3 g4
  have hC : h * colM (cvec2 k r z e) = colM (cvec2 k r z e) := by
    rw [mul_colM]
    congr 1
    funext j
    rcases j with j | _
    · exact fix_c hh j
    · exact hhe
  have hC' : h * colM (cvec2' k r z e) = colM (cvec2' k r z e) := by
    rw [mul_colM]
    congr 1
    funext j
    rcases j with j | _
    · exact fix_c' hh j
    · exact hhe
  have hCd := dual_fix hh.1 hC'
  obtain ⟨e1, e2⟩ := decomp hc g3 h hC hCd
  obtain ⟨B, hBs, hBe⟩ := unitary_log _ (unitary_of Qx8.hpk_herm hh.1 g1 e1)
  refine ⟨B, hBs, ?_⟩
  rw [exp_lift hc g1 g2 B, hBe, ← e2]

end KLG

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
