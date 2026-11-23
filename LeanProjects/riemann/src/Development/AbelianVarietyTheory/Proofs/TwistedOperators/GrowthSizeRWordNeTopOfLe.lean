import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.Grow GlobalTheory.Mem.AutSpace
open scoped ENNReal

namespace GlobalTheory.Size

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {θ : InfFam D} {V : HSp D} {φ : GA D V → ℂ} {N : ℕ}

private lemma rderC_sum_smul (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) (τ : D.what₂.Tau) {ι : Type*}
    [DecidableEq ι] (s : Finset ι) (c : ι → ℂ) (M : ι → Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    RderC θ V τ (∑ a ∈ s, c a • M a) φ = ∑ a ∈ s, c a • RderC θ V τ (M a) φ := by
  induction s using Finset.induction_on with
  | empty =>

    have h0 := GlobalTheory.Mem.RealTranslate.RderC_smul hθ hs τ (0 : ℂ) (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    rw [zero_smul, zero_smul] at h0
    rw [Finset.sum_empty, Finset.sum_empty, h0]
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, GlobalTheory.Mem.RealTranslate.RderC_add hθ hs,
      GlobalTheory.Mem.RealTranslate.RderC_smul hθ hs, ih]

theorem RderC_eq_sum_glDer (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) (τ : D.what₂.Tau)
    (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    RderC θ V τ Z φ = ∑ a : Fin V.rank × Fin V.rank, Z a.1 a.2 • glDer θ V (τ, a) φ := by

  have hZ : Z = ∑ a : Fin V.rank × Fin V.rank, Z a.1 a.2 • Matrix.single a.1 a.2 (1 : ℂ) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Fintype.sum_prod_type]

    rw [Fintype.sum_eq_single i fun x hx => by simp [hx], Fintype.sum_eq_single j fun y hy => by simp [hy]]
    simp
  conv_lhs => rw [hZ]
  rw [rderC_sum_smul hθ hs τ]
  simp only [glDer]

theorem Rder_eq_sum_glDer (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) {τ : D.what₂.Tau}
    {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    Rder θ V τ X φ = ∑ a : Fin V.rank × Fin V.rank, X a.1 a.2 • glDer θ V (τ, a) φ := by

  rw [← GlobalTheory.SmoothAutCheck.RderC_eq θ V τ hX φ]
  exact RderC_eq_sum_glDer hθ hs τ X

variable (θ V N) in

def wordFin (l : List (D.what₂.Tau × Fin V.rank × Fin V.rank)) : Submodule ℂ (GA D V → ℂ) where
  carrier := {f | f ∈ SmFun θ V ∧ growthSize V N (wordAct (glDer θ V) l f) ≠ ∞}
  add_mem' h h' := ⟨add_mem h.1 h'.1, by
    rw [(linOnSm_glWord l).add _ h.1 _ h'.1]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨h.2, h'.2⟩) growthSize_add_le⟩
  zero_mem' := ⟨zero_mem _, by
    have := (linOnSm_glWord (θ := θ) l).smul 0 0
    rw [zero_smul, zero_smul] at this
    rw [this]
    exact (growthSize_const (0 : ℂ)).trans_ne enorm_ne_top⟩
  smul_mem' c _ h := ⟨(SmFun θ V).smul_mem c h.1, by
    rw [(linOnSm_glWord l).smul, growthSize_smul]
    exact ENNReal.mul_ne_top enorm_ne_top h.2⟩

theorem rWord_mem_wordFin (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) {d : ℕ} (h : growthSob θ V d N φ ≠ ∞)
    (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (hl : IsLieWord V l) :
    ∀ l', l'.length + l.length ≤ d → rWord θ V l φ ∈ wordFin θ V N l' := by
  have hsum : wordSum (glDer θ V) (growthSize V N) d φ ≠ ∞ := h
  induction l with
  | nil =>

    intro l' hl'
    have hlen : l'.length ≤ d := by simpa using hl'
    have hw : rWord θ V [] φ = φ := wordAct_nil _ φ
    rw [hw]
    show φ ∈ SmFun θ V ∧ growthSize V N (wordAct (glDer θ V) l' φ) ≠ ∞
    exact ⟨hs, wordSum_ne_top_iff.1 hsum l' hlen⟩
  | cons p t ih =>

    intro l' hl'
    have hp : p.2 ∈ lieAt V p.1 := hl p (List.mem_cons_self ..)
    have ht : IsLieWord V t := fun q hq => hl q (List.mem_cons_of_mem p hq)
    have hψ : rWord θ V t φ ∈ SmFun θ V :=
      (show _ ∧ _ from ih ht [] (by simp only [List.length_cons, List.length_nil] at hl' ⊢; omega)).1
    have hw : rWord θ V (p :: t) φ = Rder θ V p.1 p.2 (rWord θ V t φ) := wordAct_cons _ p t φ
    rw [hw, Rder_eq_sum_glDer hθ hψ hp]
    refine sum_mem fun a _ => Submodule.smul_mem _ _ ?_
    have hm : growthSize V N (wordAct (glDer θ V) (l' ++ [(p.1, a)]) (rWord θ V t φ)) ≠ ∞ :=
      (show _ ∧ _ from ih ht (l' ++ [(p.1, a)])
        (by simp only [List.length_cons, List.length_append, List.length_nil] at hl' ⊢; omega)).2
    have he : wordAct (glDer θ V) (l' ++ [(p.1, a)]) (rWord θ V t φ) =
        wordAct (glDer θ V) l' (glDer θ V (p.1, a) (rWord θ V t φ)) := by
      rw [wordAct_append, wordAct_cons, wordAct_nil]
    show glDer θ V (p.1, a) (rWord θ V t φ) ∈ SmFun θ V ∧
      growthSize V N (wordAct (glDer θ V) l' (glDer θ V (p.1, a) (rWord θ V t φ))) ≠ ∞
    rw [← he]
    exact ⟨(linOnSm_RderC p.1 _).mem _ hψ, hm⟩

theorem growthSize_rWord_ne_top_of_le (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) {d : ℕ} (h : growthSob θ V d N φ ≠ ∞)
    {l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)} (hl : IsLieWord V l) (hd : l.length ≤ d) :
    growthSize V N (rWord θ V l φ) ≠ ∞ := by
  have hm := rWord_mem_wordFin hθ hs h l hl [] (by simpa using hd)
  have h2 : growthSize V N (wordAct (glDer θ V) [] (rWord θ V l φ)) ≠ ∞ := (show _ ∧ _ from hm).2
  rwa [wordAct_nil] at h2

theorem growthSize_rWord_ne_top (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) (h : ∀ d, growthSob θ V d N φ ≠ ∞) :
    ∀ l, IsLieWord V l → growthSize V N (rWord θ V l φ) ≠ ∞ := fun l hl =>
  growthSize_rWord_ne_top_of_le hθ hs (h l.length) hl le_rfl

theorem unifModGrowth_iff_growthSob (hθ : IsInfFam θ) (hs : φ ∈ SmFun θ V) :
    UnifModGrowth V θ φ ↔ ∃ N, ∀ d, growthSob θ V d N φ ≠ ∞ := by
  refine ⟨exists_growthSob_ne_top hs, ?_⟩
  rintro ⟨M, hM⟩
  exact unifModGrowth_iff.2 ⟨M, growthSize_rWord_ne_top hθ hs hM⟩

end GlobalTheory.Size

end
