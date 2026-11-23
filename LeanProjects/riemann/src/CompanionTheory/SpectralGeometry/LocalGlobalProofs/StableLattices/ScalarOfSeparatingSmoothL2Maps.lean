import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.SimpleDistinctness.ScalarCharacterOfL2Embedding
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.AnyAdj
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRTWNeAlg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLExistsOfAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFiniteIdem

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.AdjointSignNormality

open CompanionTheory.RgExh CompanionTheory.RgExh.Fin ReciprocityTheory.ChartRestriction.DS
open Formalism.REAL (GlRel qdet)

variable {n : ℕ} {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem exists_adj_sum {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E)
    (l : List (ℂ × List (Fin n × Fin n))) :
    ∃ B : Module.End ℂ M, ∀ x y : M,
      inner ℂ ((l.map fun c => c.1 • (c.2.map fun p => E p.1 p.2).prod).sum x) y = inner ℂ x (B y) := by
  induction l with
  | nil => exact ⟨0, fun x y => by simp⟩
  | cons c l ih =>
    obtain ⟨B, hB⟩ := ih
    refine ⟨((starRingEnd ℂ) c.1 * (c.2.map fun p => adjSign ε p.1 p.2).prod) •
      ((c.2.reverse.map Prod.swap).map fun p => E p.1 p.2).prod + B, fun x y => ?_⟩
    simp only [List.map_cons, List.sum_cons, LinearMap.add_apply, LinearMap.smul_apply, inner_add_left,
      inner_add_right, inner_smul_left, inner_smul_right, hB, eword_adjoint hU]
    ring

theorem exists_adj_qdet {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E) (u : ℂ) :
    ∃ B : Module.End ℂ M, ∀ x y : M, inner ℂ (qdet E u x) y = inner ℂ x (B y) := by
  obtain ⟨l, hl⟩ := qdet_eq_sum_words E u
  rw [hl]
  exact exists_adj_sum hU l

theorem adjSign_mul_self (ε : Fin n → Bool) (a b : Fin n) : adjSign ε a b * adjSign ε a b = 1 := by
  unfold adjSign
  split_ifs <;> simp

theorem commute_adj {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E)
    {A B : Module.End ℂ M} (hA : ∀ a b, Commute A (E a b)) (hB : ∀ x y : M, inner ℂ (A x) y = inner ℂ x (B y))
    (c d : Fin n) : Commute B (E c d) := by
  have key : ∀ x y : M, inner ℂ x (B (E c d y)) = inner ℂ x (E c d (B y)) := by
    intro x y
    have h1 : inner ℂ (E d c (A x)) y = adjSign ε d c * inner ℂ (A x) (E c d y) := hU d c _ _
    have h2 : inner ℂ (E d c x) (B y) = adjSign ε d c * inner ℂ x (E c d (B y)) := hU d c _ _
    have h3 : E d c (A x) = A (E d c x) := LinearMap.congr_fun (hA d c).symm.eq x
    rw [h3, hB, h2] at h1
    have hs : adjSign ε d c ≠ 0 := left_ne_zero_of_mul_eq_one (adjSign_mul_self ε d c)
    rw [← hB]
    exact (mul_left_cancel₀ hs h1).symm
  refine LinearMap.ext fun y => ?_
  have h := key (B (E c d y) - E c d (B y)) y
  have h0 : inner ℂ (B (E c d y) - E c d (B y)) (B (E c d y) - E c d (B y)) = (0 : ℂ) := by
    rw [inner_sub_right, h, sub_self]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 h0)

theorem normal_sq {A B : Module.End ℂ M} (hB : ∀ x y : M, inner ℂ (A x) y = inner ℂ x (B y)) (hc : Commute A B)
    (y : M) (h : A (A y) = 0) : A y = 0 := by
  have hn : ∀ z : M, inner ℂ (B z) (B z) = inner ℂ (A z) (A z) := by
    intro z
    have h1 : inner ℂ (A (B z)) z = inner ℂ (B z) (B z) := hB _ _
    have h2 : inner ℂ (A z) (A z) = inner ℂ z (B (A z)) := hB _ _
    have h3 : A (B z) = B (A z) := LinearMap.congr_fun hc.eq z
    rw [← h1, h3, ← inner_conj_symm, ← h2, inner_self_conj]
  have h0 : B (A y) = 0 := by
    have := hn (A y)
    rw [h, inner_zero_left] at this
    exact inner_self_eq_zero.1 this
  have h1 : inner ℂ (A y) (A y) = (0 : ℂ) := by rw [hB, h0, inner_zero_right]
  exact inner_self_eq_zero.1 h1

theorem normal_pow {A B : Module.End ℂ M} (hB : ∀ x y : M, inner ℂ (A x) y = inner ℂ x (B y)) (hc : Commute A B)
    (k : ℕ) (y : M) (h : (A ^ k) y = 0) : A y = 0 := by
  induction k generalizing y with
  | zero =>
    have : y = 0 := by simpa using h
    simp [this]
  | succ k ih =>
    refine normal_sq hB hc y (ih (A y) ?_)
    rw [pow_succ] at h
    exact h

theorem qdet_shift_pow {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ M} (hE : GlRel E)
    (hU : IsInfUnitary ε E) (w s : ℂ) (k : ℕ) (y : M)
    (h : ((qdet E w - s • (1 : Module.End ℂ M)) ^ k) y = 0) : (qdet E w - s • (1 : Module.End ℂ M)) y = 0 := by
  obtain ⟨B, hB⟩ := exists_adj_qdet hU w
  have hA : ∀ a b, Commute (qdet E w) (E a b) := fun a b =>
    (Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.TW.qdet_comm hE w a b)
  have hBE := commute_adj hU hA hB
  have hQ : Commute B (qdet E w) := GlobalTheory.CentreFin.commute_qdet hBE w
  have hadj : ∀ x y : M, inner ℂ ((qdet E w - s • (1 : Module.End ℂ M)) x) y =
      inner ℂ x ((B - (starRingEnd ℂ) s • (1 : Module.End ℂ M)) y) := by
    intro x y
    simp [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hB, mul_comm]
  have hc : Commute (qdet E w - s • (1 : Module.End ℂ M)) (B - (starRingEnd ℂ) s • (1 : Module.End ℂ M)) := by
    refine Commute.sub_left (Commute.sub_right hQ.symm ?_) (Commute.sub_right ?_ ?_)
    · exact (Commute.one_right _).smul_right _
    · exact (Commute.one_left _).smul_left _
    · exact ((Commute.one_left _).smul_left _).smul_right _
  exact normal_pow hadj hc k y h

theorem scalar_of_separating_smooth_l2_maps : ScalarCharacterOfL2Embedding := by
  rintro n ε X χ hL ⟨k, hk⟩ Y
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  have hU := isInfUnitary_of_isDerivedOn hσ hD
  have hE : GlRel (smE ε (rreg ε)) := hD.glRep
  refine sub_eq_zero.1 (LinearMap.ext fun u => ?_)
  by_contra hne
  obtain ⟨c, hc, hcu⟩ := hL _ hne
  apply hcu
  set w : ℂ := Y + ((n : ℂ) - 1) / 2
  set s : ℂ := Formalism.QuantumDeterminants.capP χ Y
  have hint : ∀ x, c ((qdet X.E w - s • (1 : Module.End ℂ X.V)) x) =
      (qdet (smE ε (rreg ε)) w - s • (1 : Module.End ℂ (smD ε (rreg ε)))) (c x) := by
    intro x
    simp [Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.KLExA.qdet_int c hc]
  have hpow : ∀ (j : ℕ) x, c (((qdet X.E w - s • (1 : Module.End ℂ X.V)) ^ j) x) =
      ((qdet (smE ε (rreg ε)) w - s • (1 : Module.End ℂ (smD ε (rreg ε)))) ^ j) (c x) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hint]
  have h0 := hpow k u
  rw [hk Y, LinearMap.zero_apply, map_zero] at h0
  rw [hint]
  exact qdet_shift_pow hE hU w s k _ h0.symm

end GlobalTheory.CompanionTheory.AdjointSignNormality
