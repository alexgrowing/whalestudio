import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub

noncomputable section

open Matrix PositivityTheory.Rg.BcB.D1
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.GramWedge

theorem star_dotProduct_self {α : Type} [Fintype α] (w : α → ℂ) :
    star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa using Complex.conj_mul' (w i)

theorem norm_entry_le_sz {ι ι' : Type} [Fintype ι] [Fintype ι'] (g : Matrix ι' ι ℂ) (a : ι') (b : ι) :
    ‖g a b‖ ≤ sz g :=
  le_ciSup (f := fun p : ι' × ι => ‖g p.1 p.2‖) (Set.finite_range _).bddAbove (a, b)

theorem sum_norm_mulVec_sq_le {ι ι' : Type} [Fintype ι] [Fintype ι'] (g : Matrix ι' ι ℂ) (v : ι → ℂ) :
    ∑ a, ‖(g *ᵥ v) a‖ ^ 2 ≤
      (Fintype.card ι * Fintype.card ι' : ℝ) * sz g ^ 2 * ∑ b, ‖v b‖ ^ 2 := by
  have row : ∀ a, ‖(g *ᵥ v) a‖ ^ 2 ≤ (Fintype.card ι : ℝ) * sz g ^ 2 * ∑ b, ‖v b‖ ^ 2 := by
    intro a
    have h1 : ‖(g *ᵥ v) a‖ ≤ sz g * ∑ b, ‖v b‖ := by
      rw [Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_entry_le_sz g a b) (norm_nonneg _)
    have h2 : (∑ b, ‖v b‖) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ b, ‖v b‖ ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun b => ‖v b‖)
    calc ‖(g *ᵥ v) a‖ ^ 2 ≤ (sz g * ∑ b, ‖v b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = sz g ^ 2 * (∑ b, ‖v b‖) ^ 2 := mul_pow _ _ _
      _ ≤ sz g ^ 2 * ((Fintype.card ι : ℝ) * ∑ b, ‖v b‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = _ := by ring
  calc ∑ a, ‖(g *ᵥ v) a‖ ^ 2
      ≤ ∑ _a : ι', (Fintype.card ι : ℝ) * sz g ^ 2 * ∑ b, ‖v b‖ ^ 2 := Finset.sum_le_sum fun a _ => row a
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem posSemidef_smul_gram_sub {ι ι' κ : Type} [Fintype ι] [Fintype ι'] [Fintype κ] [DecidableEq κ]
    (g : Matrix ι' ι ℂ) (A : Matrix ι κ ℂ) :
    (((((Fintype.card ι * Fintype.card ι' : ℝ) * sz g ^ 2 : ℝ) : ℂ) • (Aᴴ * A)) -
      (g * A)ᴴ * (g * A)).PosSemidef := by
  set c : ℝ := (Fintype.card ι * Fintype.card ι' : ℝ) * sz g ^ 2 with hc
  have hG : (Aᴴ * A).IsHermitian := isHermitian_conjTranspose_mul_self A
  have hH : ((g * A)ᴴ * (g * A)).IsHermitian := isHermitian_conjTranspose_mul_self _
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    ((hG.smul (show star (c : ℂ) = c from Complex.conj_ofReal c)).sub hH) fun x => ?_
  have e : ∀ {α : Type} [Fintype α] (B : Matrix α κ ℂ),
      star x ⬝ᵥ ((Bᴴ * B) *ᵥ x) = star (B *ᵥ x) ⬝ᵥ (B *ᵥ x) := by
    intro α _ B
    rw [← mulVec_mulVec, star_mulVec, dotProduct_mulVec]
  have e1 := e A
  have e2 : star x ⬝ᵥ (((g * A)ᴴ * (g * A)) *ᵥ x) = star (g *ᵥ (A *ᵥ x)) ⬝ᵥ (g *ᵥ (A *ᵥ x)) := by
    rw [e (g * A), mulVec_mulVec]
  rw [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, e1, e2, star_dotProduct_self,
    star_dotProduct_self, smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  exact Complex.zero_le_real.2 (sub_nonneg.2 (sum_norm_mulVec_sq_le g (A *ᵥ x)))

theorem gram_mul_det {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (s : Matrix κ κ ℂ) :
    ((A * s)ᴴ * (A * s)).det = ((‖s.det‖ ^ 2 : ℝ) : ℂ) * (Aᴴ * A).det := by
  have h : star s.det * s.det = ((‖s.det‖ ^ 2 : ℝ) : ℂ) := by
    simpa using Complex.conj_mul' s.det
  rw [conjTranspose_mul, show sᴴ * Aᴴ * (A * s) = sᴴ * (Aᴴ * A) * s by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc],
    det_mul, det_mul, det_conjTranspose, ← h]
  ring

theorem mulI_of_detMono : DetMono → MulI := by
  intro hm ι ι' κ _ _ _ _ A
  refine ⟨fun g => ?_, fun s => ?_, fun s => ?_⟩
  · have h := hm κ _ _ (posSemidef_conjTranspose_mul_self (g * A)) (posSemidef_smul_gram_sub g A)
    rw [det_smul, ← Complex.ofReal_pow, Complex.re_ofReal_mul] at h
    exact h
  · simp only [nI]
    rw [gram_mul_det, Complex.re_ofReal_mul, mul_comm]
  · have h := gram_mul_det (1 : Matrix κ κ ℂ) s
    simp only [Matrix.one_mul, conjTranspose_one, Matrix.mul_one, det_one, mul_one] at h
    simp only [nI]
    rw [h, Complex.ofReal_re]

end GlobalTheory.CompanionTheory.GramWedge

end
