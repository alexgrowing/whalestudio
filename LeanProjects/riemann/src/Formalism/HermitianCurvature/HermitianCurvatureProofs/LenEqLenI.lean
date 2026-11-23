import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopRatio

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

section thr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem ntop_eq_N'' (S : C.HidaSetting E Wp Wq) : (S.Ntop : ℝ) = S.G.N := by
  simp only [C.HidaSetting.Ntop, Sz.Glob.N, C.Kst]; push_cast; ring

theorem len_eq_lenI' (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : S.cutHi v - S.cutLo v = S.G.lenI := by
  simp only [C.HidaSetting.cutHi, C.HidaSetting.cutLo, Sz.Glob.lenI, Sz.Glob.place]; ring

theorem glob_posT (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) : 0 < S.G.g ∧ 0 < S.G.ka := by
  obtain ⟨hg1, hg2, -⟩ := hB
  refine ⟨by unfold Sz.Glob.g; exact_mod_cast Nat.mul_pos hg1 hg2, ?_⟩
  unfold Sz.Glob.ka; rw [S.hv]; exact div_pos Real.pi_pos (by linarith [PBD.rd_pos' E])

theorem lenI_posT (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (hS : 0 < S.f) : 0 < S.G.lenI := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hG, -⟩ := hB
  obtain ⟨hlen, -⟩ := hG ⟨0, hS⟩
  rw [len_eq_lenI'] at hlen
  have hN : (0 : ℝ) ≤ S.Ntop := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ S.Ntop := by
    have : 1 ≤ S.Ntop := by unfold C.HidaSetting.Ntop C.Kst; omega
    exact_mod_cast this
  have h6 : (0 : ℝ) < 6 * (S.Ntop : ℝ) ^ 3 + 6 * S.Ntop := by positivity
  linarith

theorem lamTop_thr (hC : 28 * Real.exp 1 ≤ Cc) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (s : ℕ) (hs2 : 2 ≤ s)
    (hsr : s ≤ S.G.r + 1) (v : Fin S.f) :
    0 ≤ lamTop S (S.G.r + 2 - s) v ∧ 2 * lamTop S (S.G.r + 2 - s) v ≤ S.base.szL (S.G.r + 2 - s) s v := by
  refine ⟨Real.sqrt_nonneg _, ?_⟩
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCA, -⟩ := hB'
  obtain ⟨hg, hk⟩ := glob_posT hB
  have hlen := lenI_posT hB (Fin.pos v)
  have hsz : S.base.szL (S.G.r + 2 - s) s v = 2 * J.thrP S.G S.CA S.de S.de' S.T S.T' S.l (S.G.r + 2 - s) (S.pl v) := by
    show (if S.G.r + 2 - s + s ≤ S.G.r + 1 then _ else _) = _
    rw [if_neg (by omega)]
  rw [hsz]
  have hsA : ∀ one, 0 ≤ J.supA S.G S.de S.de' S.T S.T' S.l one (S.pl v) := fun one => supA_nonneg S hg hk v one
  have hFT := (Formalism.FourierDecayAlt.P.frame_threshold_bound_holds (InfinitePlace E) S.G S.CA S.de S.de' S.T S.T' S.l (S.pl v) hg hlen
    (hC.trans hCA) hsA).2 (S.G.r + 2 - s) (Real.exp 1) ((28 * S.G.N / S.G.lenI) ^ (2 * (S.G.r + 2 - s - 1)))
    (by omega) (Real.exp_pos 1).le le_rfl (pow_nonneg (div_nonneg (by unfold Sz.Glob.N; positivity) hlen.le) _) le_rfl
  unfold lamTop
  have e : ((S.G.r : ℤ) + 2 - ((S.G.r + 2 - s : ℕ) : ℤ)) = ((S.G.r : ℤ) + 2 - ((S.G.r + 2 - s : ℕ) : ℤ)) := rfl
  linarith [hFT]

end thr

end

end Formalism.FourierDecayAlt.P.PBL
