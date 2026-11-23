import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ImportsAlt
import Formalism.HermitianCurvature.HerGenC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.TopVec Filter Topology MeasureTheory

namespace GlobalTheory.TopVec

section

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

omit [FiniteDimensional ℂ Wp] in

theorem hsInner_self_eq_normSq (A : Wq →L[ℂ] Wp) : B.hsInner A A = ((‖B.hsVec A‖ ^ 2 : ℝ) : ℂ) := by
  unfold B.hsInner
  rw [inner_self_eq_norm_sq_to_K]
  simp

omit [FiniteDimensional ℂ Wp] in
theorem hsInner_zero_zero : B.hsInner (0 : Wq →L[ℂ] Wp) 0 = 0 := by
  simp [P.Topx1.hsInner_eq]

theorem levelForm_top_diag (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (a : C.LPt) :
    p.RR H (P.r + 1) w a a = Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP H w a a := by
  by_cases hg : D.IsLocPt a (P.r + 1) ∧ 0 < D.ptG (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r a
  · unfold KB.Pl.RR D.RRplace
    rw [dif_pos ⟨hg.1, hg.1⟩, dif_neg (by omega), if_pos rfl]
    split_ifs with hw
    · subst hw
      exact (Formalism.FourierDecayAlt.P.top_of_empty Formalism.FourierDecayAlt.P.vector_valued_types Wp Wq P p.l0 p.T p.ν' p.m₀ p.Θ p.TP H a a p.hP p.hF
        hg.1 hg.1 hg.2 hg.2).symm
    · rfl
  · have hV : ∀ F, D.vecV p.T.base p.ν' p.m₀ F a = 0 := fun F => by
      unfold D.vecV
      rw [dif_neg hg]
    have ht : Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP H w a a = 0 := by
      simp only [Top.topOf, hV, ContinuousLinearMap.comp_zero, hsInner_zero_zero, mul_zero,
        Finset.sum_const_zero]
    rw [ht]
    unfold KB.Pl.RR D.RRplace
    split_ifs with h1 h2 h3 h4
    · omega
    · rw [hV, hsInner_zero_zero]
    · exact ht
    · rfl
    · rfl

end

theorem Ew_eq_norm_tv_sq : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ), TBB.Ew p (fun _ => 1) H (P.r + 1) w (TBB.bigPt P.r c) = ‖tv p H w c‖ ^ 2 := by
  intro Wp Wq _ _ _ _ _ _ P p H w c
  have h1 : TBB.normC (fun _ => 1) w = 1 := by simp [TBB.normC]
  unfold TBB.Ew TBB.NP
  rw [levelForm_top_diag, h1, div_one, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  unfold Top.topOf
  simp only [hsInner_self_eq_normSq, ← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
  simp only [tv, norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, TBB.TTp, KB.Pl.V]
  ring

end GlobalTheory.TopVec
