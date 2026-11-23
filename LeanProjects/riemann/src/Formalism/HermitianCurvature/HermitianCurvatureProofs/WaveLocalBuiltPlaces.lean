import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockKWave

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section wave

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def Xw (S : C.HidaSetting E Wp Wq) (i : ℕ) (v : Fin S.f) : ℝ :=
  (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r i 0)) * Real.exp 1 * (28 * S.G.N / S.G.lenI) ^ (2 * (i - 1) + 0) *
    J.supA S.G S.de S.de' S.T S.T' S.l (decide (i = 1 ∧ 0 + 1 = 1)) (S.pl v)

theorem g_cast (S : C.HidaSetting E Wp Wq) : ((S.g : ℕ) : ℝ) = S.G.g := by
  unfold C.HidaSetting.g Sz.Glob.g; push_cast; rfl

theorem len_eq (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : S.cutHi v - S.cutLo v = S.G.lenI := by
  simp only [C.HidaSetting.cutHi, C.HidaSetting.cutLo, Sz.Glob.lenI, Sz.Glob.place]; ring

theorem T_eq (S : C.HidaSetting E Wp Wq) (hg : 0 < S.G.g) (j : ℕ) :
    ((S.g : ℝ) * lamS S j) / (2 * Real.pi) = (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r (j + 1) 0)) := by
  unfold lamS
  rw [g_cast]
  have hx : 0 < S.G.g / (2 * Real.pi) := by positivity
  have e1 : 2 * Real.pi / S.G.g = (S.G.g / (2 * Real.pi))⁻¹ := by rw [inv_div]
  have key : ∀ n0 n1 : ℤ, n0 = n1 + 1 →
      S.G.g * (S.G.g / (2 * Real.pi)) ^ n1 / (2 * Real.pi) = (2 * Real.pi / S.G.g) ^ (-n0) := by
    intro n0 n1 h
    rw [h, e1, inv_zpow, zpow_neg, inv_inv, zpow_add_one₀ hx.ne']
    field_simp
  exact key _ _ (by unfold S6.nuBlock; push_cast; ring)

end wave

section main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem glob_pos (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) : 0 < S.G.g ∧ 0 < S.G.ka := by
  refine ⟨by unfold Sz.Glob.g; exact_mod_cast Nat.mul_pos hB.1 hB.2.1, ?_⟩
  unfold Sz.Glob.ka; rw [S.hv]; have := PBD.rd_pos' E; positivity

theorem lenI_pos (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) : 0 < S.G.lenI := by
  have hGo := hB.2.2.2.2.2.2.2.2.2.2.1
  have h := (hGo v).1
  rw [len_eq] at h
  have : (0 : ℝ) < 6 * (S.Ntop : ℝ) ^ 3 + 6 * S.Ntop := by have := PBD.ntop_ge S; positivity
  linarith

theorem xw_nonneg (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (i : ℕ) (v : Fin S.f) : 0 ≤ Xw S i v := by
  obtain ⟨hg, hk⟩ := glob_pos hB
  have hl := lenI_pos hB v
  have hN : (0 : ℝ) ≤ S.G.N := by unfold Sz.Glob.N; positivity
  have hA := supA_nonneg S hg hk v (decide (i = 1 ∧ 0 + 1 = 1))
  unfold Xw
  have : 0 < 2 * Real.pi / S.G.g := by positivity
  positivity

theorem thr_wave (hCc : 28 * Real.exp 1 ≤ Cc) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) :
    JC.HidaCurvatureBarriers S (fun i v => Xw S i v) := by
  intro i hi1 _ v
  obtain ⟨hg, hk⟩ := glob_pos hB
  have hl := lenI_pos hB v
  have hCA : Cc ≤ S.CA := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hN : (0:ℝ) ≤ S.G.N := by unfold Sz.Glob.N; positivity
  have hcg : (0:ℝ) ≤ (28 * S.G.N / S.G.lenI) ^ (2 * (i - 1) + 0) := by positivity
  have h := (Formalism.FourierDecayAlt.P.frame_threshold_bound_holds (InfinitePlace E) S.G S.CA S.de S.de' S.T S.T' S.l (S.pl v) hg hl
    (hCc.trans hCA) (fun one => supA_nonneg S hg hk v one)).1 i 0 (Real.exp 1) ((28 * S.G.N / S.G.lenI) ^ (2 * (i - 1) + 0))
    hi1 (Real.exp_pos 1).le le_rfl hcg le_rfl
  refine ⟨xw_nonneg hB i v, ?_⟩
  show Xw S i v ≤ J.thrS S.G S.CA S.de S.de' S.T S.T' S.l i 1 (S.pl v)
  unfold Xw
  exact_mod_cast h

end main

section main2

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem xw_K (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (j K : ℕ) (grid : Fin K → Fin (2 * j + 1) → ℝ)
    (hl1 : ∀ b, ∑ i, |F7.lagCo (grid b) i| ≤ (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ (2 * j)) :
    (∏ b, ∑ i, |F7.lagCo (grid b) i|) * (((S.g : ℝ) * lamS S j) / (2 * Real.pi)) ^ K *
      (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l (decide (j = 0)) (S.pl v)) ^ K ≤ (Xw S (j + 1) v) ^ K := by
  obtain ⟨hg, hk⟩ := glob_pos hB
  have hl := lenI_pos hB v
  rw [T_eq S hg j]
  have hdec : decide (j + 1 = 1 ∧ 0 + 1 = 1) = decide (j = 0) := by
    by_cases h : j = 0 <;> simp [h]
  have hexp : 2 * (j + 1 - 1) + 0 = 2 * j := by omega
  unfold Xw
  rw [hdec, hexp]
  rw [ntop_eq_N', len_eq] at hl1
  set cg := (28 * S.G.N / S.G.lenI) ^ (2 * j) with hcg
  set Tf := (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r (j + 1) 0)) with hTf
  set A := J.supA S.G S.de S.de' S.T S.T' S.l (decide (j = 0)) (S.pl v) with hA
  have hA0 : 0 ≤ A := supA_nonneg S hg hk v _
  have hgg : 0 < 2 * Real.pi / S.G.g := by positivity
  have hTf0 : 0 ≤ Tf := by positivity
  have hprod : (∏ b, ∑ i, |F7.lagCo (grid b) i|) ≤ cg ^ K := by
    calc (∏ b, ∑ i, |F7.lagCo (grid b) i|) ≤ ∏ _b : Fin K, cg :=
          Finset.prod_le_prod (fun b _ => Finset.sum_nonneg fun i _ => abs_nonneg _) fun b _ => hl1 b
      _ = cg ^ K := by simp
  have h1 : 0 ≤ Tf ^ K * (Real.exp 1 * A) ^ K := by positivity
  calc (∏ b, ∑ i, |F7.lagCo (grid b) i|) * Tf ^ K * (Real.exp 1 * A) ^ K
      = (∏ b, ∑ i, |F7.lagCo (grid b) i|) * (Tf ^ K * (Real.exp 1 * A) ^ K) := by ring
    _ ≤ cg ^ K * (Tf ^ K * (Real.exp 1 * A) ^ K) := mul_le_mul_of_nonneg_right hprod h1
    _ = (Tf * Real.exp 1 * cg * A) ^ K := by ring

end main2

def WaveLocB : Prop :=
  P5.ThmPActual → KB.PStd → KB.DegWave → KB.SizeStd → KB.VIso → FormPos →
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    28 * Real.exp 1 ≤ Cc → KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∃ X : ℕ → Fin S.f → ℝ, JC.HidaCurvatureBarriers S X ∧
      ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
        (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.WaveLoc (setC S p F) v fun i => X i v

end

end Formalism.FourierDecayAlt.P.PBL
