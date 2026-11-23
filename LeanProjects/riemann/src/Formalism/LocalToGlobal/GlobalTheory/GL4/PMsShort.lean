import Formalism.LocalToGlobal.GlobalTheory.GL4.PMsGram

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions NumberField Formalism.MainNotions.flipTwoThree

section Short

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem keyBound_mono (S : HSpace E) (q : ℕ) {B B' : ℝ} (h : KeyBound S q B) (hB : B ≤ B') : KeyBound S q B' := by
  obtain ⟨K, hK, hL⟩ := h
  exact ⟨K, hK.trans hB, hL⟩

end Short

section ShortRecord

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def radiusSq (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (n : ℕ) : ℝ :=
  C₀ * D.R.f * (n : ℝ) ^ 2 * D.host.v ^ 2 * (Tu D u : ℝ) ^ 2

def msRho (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (n : ℕ) : ℝ := radiusSq D u C₀ n

def coordinateLogBound (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (n : ℕ) : ℝ :=
  4 * D.R.f * n * ((n : ℝ) + 1) * (Real.log (radiusSq D u C₀ n) / 2)

def ShortAt (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (S : HSpace D.host.E) (q n : ℕ) : Prop :=
  ShortFrame S q (msRho D u C₀ n) ∧ CSAt S ∧ CoordCount S q (msRho D u C₀ n) (coordinateLogBound D u C₀ n)

theorem one_le_radius_sq (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (hC : 1 ≤ C₀) (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ radiusSq D u C₀ n := by
  have hv : 1 ≤ D.host.v := one_le_hostv D
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast one_le_f D
  have hT : (1 : ℝ) ≤ (Tu D u : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.one_lt.le
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hC hf) (one_le_pow₀ hn1)) (one_le_pow₀ hv)) (one_le_pow₀ hT)

theorem keyBound_of_shortAt (D : D7) (u : D.what₂.Word) (C₀ : ℝ) (hC : 3 ≤ C₀) (S : HSpace D.host.E) (q n : ℕ)
    (hn : 1 ≤ n) (hr : S.rank = n) (h : ShortAt D u C₀ S q n) : KeyBound S q (msLat D u C₀ n) := by
  obtain ⟨hS, hCS, hCC⟩ := h
  have h1 := one_le_radius_sq D u C₀ (by linarith) n hn
  have hρ : 0 ≤ msRho D u C₀ n := by
    unfold msRho
    linarith
  have hB2 : 0 ≤ coordinateLogBound D u C₀ n := by
    unfold coordinateLogBound
    have := Real.log_nonneg h1
    positivity
  refine keyBound_mono S q (keyBound_of S q _ _ hρ hB2 hS hCS hCC) ?_
  rw [hr, Formalism.MainNotions.flipTwoThree.b_finrank_host]
  have hle : Real.log (2 * msRho D u C₀ n + 1) ≤ Real.log (C₀ * radiusSq D u C₀ n) := by
    unfold msRho
    exact Real.log_le_log (by linarith) (by nlinarith)
  have hn2 : (0 : ℝ) ≤ (n : ℝ) ^ 2 * ((2 * D.R.f : ℕ) : ℝ) := by positivity
  have key := mul_le_mul_of_nonneg_left hle hn2
  unfold msLat coordinateLogBound
  unfold radiusSq at key ⊢
  push_cast at key ⊢
  linarith [key]

theorem msCount_of_short (D : D7) (C₀ : ℝ) (hC : 3 ≤ C₀)
    (h : ∀ u : D.what₂.Word,
      (∀ i ≤ D.R.m, ShortAt D u C₀ (D.sp.X i) (Tu D u ^ (2 * D.R.f)) (D.R.N i)) ∧
      ShortAt D u C₀ D.sp.X' 1 (D.R.N D.R.m - 1)) : MsCount D C₀ := by
  refine msCount_of_keys D C₀ (by linarith) fun u => ⟨fun i hi => ?_, ?_⟩
  · refine keyBound_of_shortAt D u C₀ hC _ _ _ ?_ (D.sp.X_rank i hi) ((h u).1 i hi)
    have := D.R.k_ge
    unfold Ranks.N
    omega
  · have hN : D.R.N D.R.m - 1 = D.R.rankX' := by
      have := Formalism.BasicNotions.factXm D.R
      omega
    refine keyBound_of_shortAt D u C₀ hC _ _ _ ?_ (by rw [D.sp.X'_rank, hN]) (h u).2
    rw [hN]
    unfold Ranks.rankX' Ranks.r
    have := D.R.k_ge
    omega

end ShortRecord

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
