import Formalism.HermitianCurvature.HermitianCurvatureProofs.ProdOfFnMap

namespace Formalism.FourierDecayAlt.P.LiftDegreeLemmas

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants NumberField Formalism.FourierDecayAlt.P.PBL
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

section consts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def lamLift (S : C.HidaSetting E Wp Wq) (b s : ℕ) (v : Fin S.f) : ℝ :=
  (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r b s)) * Real.exp 1 * (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s) *
    J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v)

theorem g_cast' (S : C.HidaSetting E Wp Wq) : ((S.g : ℕ) : ℝ) = S.G.g := by
  unfold C.HidaSetting.g Sz.Glob.g; push_cast; rfl

theorem len_eq' (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : S.cutHi v - S.cutLo v = S.G.lenI := by
  simp only [C.HidaSetting.cutHi, C.HidaSetting.cutLo, Sz.Glob.lenI, Sz.Glob.place]; ring

theorem norm_lamB' (S : C.HidaSetting E Wp Wq) (hg : 0 < S.G.g) (b s : ℕ) :
    ‖lamB S b s‖ = (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r b s)) := by
  have hg' : (0 : ℝ) < (S.g : ℝ) := by rw [g_cast']; exact hg
  rw [norm_lamB S hg' b s, g_cast', zpow_neg, ← inv_zpow, inv_div]

variable {Cb Cc : ℝ} {S : C.HidaSetting E Wp Wq} {p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v))}
  {f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {χ : ℝ → ℝ} {A₀ : ℝ}

theorem lenI_pos' (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) : 0 < S.G.lenI := by
  have hGo := hB.2.2.2.2.2.2.2.2.2.2.1
  have h := (hGo v).1
  rw [len_eq'] at h
  have : (0 : ℝ) < 6 * (S.Ntop : ℝ) ^ 3 + 6 * S.Ntop := by have := PBD.ntop_ge S; positivity
  linarith

theorem lamLift_nonneg (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (b s : ℕ) (v : Fin S.f) : 0 ≤ lamLift S b s v := by
  obtain ⟨hg, hk⟩ := glob_pos' hB
  have hl := lenI_pos' hB v
  have hN : (0 : ℝ) ≤ S.G.N := by unfold Sz.Glob.N; positivity
  have hA := supA_nonneg S hg hk v false
  unfold lamLift
  have : 0 < 2 * Real.pi / S.G.g := by positivity
  positivity

theorem thr_lift (hCc : 28 * Real.exp 1 ≤ Cc) (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (b s : ℕ) (hb : 1 ≤ b)
    (hs : 1 ≤ s) (hbs : b + s ≤ S.G.r + 1) (v : Fin S.f) :
    0 ≤ lamLift S b s v ∧ lamLift S b s v ≤ S.base.szL b s v := by
  obtain ⟨hg, hk⟩ := glob_pos' hB
  have hl := lenI_pos' hB v
  have hCA : Cc ≤ S.CA := hB.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hN : (0:ℝ) ≤ S.G.N := by unfold Sz.Glob.N; positivity
  have hcg : (0:ℝ) ≤ (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s) := by positivity
  have h := (Formalism.FourierDecayAlt.P.frame_threshold_bound_holds (InfinitePlace E) S.G S.CA S.de S.de' S.T S.T' S.l (S.pl v) hg hl
    (hCc.trans hCA) (fun one => supA_nonneg S hg hk v one)).1 b s (Real.exp 1)
    ((28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s)) hb (Real.exp_pos 1).le le_rfl hcg le_rfl
  have hdec : decide (b = 1 ∧ s + 1 = 1) = false := decide_eq_false (by omega)
  rw [hdec] at h
  refine ⟨lamLift_nonneg hB b s v, ?_⟩
  show lamLift S b s v ≤ (if b + s ≤ S.G.r + 1 then _ else _)
  rw [if_pos hbs]
  unfold lamLift
  exact h

theorem lift_K (hB : KB.IsLeadingFormSetting Cb Cc S p f χ A₀) (v : Fin S.f) (b s j K : ℕ) (hjb : b + s = j + 1)
    (grid : Fin K → Fin (2 * (j - s) + s + 1) → ℝ)
    (hl1 : ∀ c, ∑ i, |F7.lagCo (grid c) i| ≤ (28 * (S.Ntop : ℝ) / (S.cutHi v - S.cutLo v)) ^ (2 * (j - s) + s)) :
    (∏ c, ∑ i, |F7.lagCo (grid c) i|) * ‖lamB S b s‖ ^ K *
      (Real.exp 1 * J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v)) ^ K ≤ (lamLift S b s v) ^ K := by
  obtain ⟨hg, hk⟩ := glob_pos' hB
  have hl := lenI_pos' hB v
  rw [norm_lamB' S hg b s]
  have hexp : 2 * (j - s) + s = 2 * (b - 1) + s := by omega
  have hl1' : ∀ c, ∑ i, |F7.lagCo (grid c) i| ≤ (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s) := fun c =>
    (hl1 c).trans_eq (by rw [hexp, ntop_eq_N', len_eq'])
  unfold lamLift
  set cg := (28 * S.G.N / S.G.lenI) ^ (2 * (b - 1) + s) with hcg
  set Tf := (2 * Real.pi / S.G.g) ^ (-(S6.nuBlock S.G.r b s)) with hTf
  set A := J.supA S.G S.de S.de' S.T S.T' S.l false (S.pl v) with hA
  have hA0 : 0 ≤ A := supA_nonneg S hg hk v _
  have hgg : 0 < 2 * Real.pi / S.G.g := by positivity
  have hTf0 : 0 ≤ Tf := by positivity
  have hprod : (∏ c, ∑ i, |F7.lagCo (grid c) i|) ≤ cg ^ K := by
    calc (∏ c, ∑ i, |F7.lagCo (grid c) i|) ≤ ∏ _c : Fin K, cg :=
          Finset.prod_le_prod (fun c _ => Finset.sum_nonneg fun i _ => abs_nonneg _) fun c _ => hl1' c
      _ = cg ^ K := by simp
  have h1 : 0 ≤ Tf ^ K * (Real.exp 1 * A) ^ K := by positivity
  calc (∏ c, ∑ i, |F7.lagCo (grid c) i|) * Tf ^ K * (Real.exp 1 * A) ^ K
      = (∏ c, ∑ i, |F7.lagCo (grid c) i|) * (Tf ^ K * (Real.exp 1 * A) ^ K) := by ring
    _ ≤ cg ^ K * (Tf ^ K * (Real.exp 1 * A) ^ K) := mul_le_mul_of_nonneg_right hprod h1
    _ = (Tf * Real.exp 1 * cg * A) ^ K := by ring

theorem norm_u (S : C.HidaSetting E Wp Wq) (hg : (0 : ℝ) < S.g) (b s K : ℕ) :
    ‖((((‖lamB S b s‖ : ℝ) : ℂ) * (-1) ^ (s - 1) * (lamB S b s)⁻¹) ^ K)‖ = 1 := by
  rw [norm_pow, norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), norm_pow,
    norm_neg, norm_one, one_pow, mul_one, mul_inv_cancel₀ (norm_ne_zero_iff.2 (lamB_ne S hg b s)), one_pow]

end consts

def LiftLocB : Prop :=
  P5.ThmPActual → KB.SizeStd → KB.DegLift → FormPos →
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    28 * Real.exp 1 ≤ Cc → KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∃ Λ : ℕ → ℕ → Fin S.f → ℝ,
      (∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ S.G.r + 1 → ∀ v, 0 ≤ Λ b s v ∧ Λ b s v ≤ S.base.szL b s v) ∧
      ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
        (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.LiftLoc (setC S p F) v fun b s => Λ b s v

end

end Formalism.FourierDecayAlt.P.LiftDegreeLemmas
