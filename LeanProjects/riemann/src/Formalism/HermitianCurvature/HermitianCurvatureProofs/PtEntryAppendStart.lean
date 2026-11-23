import Formalism.HermitianCurvature.HermitianCurvatureProofs.CWConsPlus
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LoeZeroOfPsd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParametersUPrimeForULower

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

open Classical

theorem ptEntry_append_start (rest : C.LPt) : ∀ (H : C.LPt) (a b : ℕ),
    D.ptEntry (H ++ rest) (D.ptSize H + a) b = if D.ptSize H ≤ b then D.ptEntry rest a (b - D.ptSize H) else 0
  | [], a, b => by simp [D.ptSize]
  | (s, t) :: H', a, b => by
    have ih := ptEntry_append_start rest H' a (b - s)
    have hsz : D.ptSize ((s, t) :: H') = s + D.ptSize H' := by simp [D.ptSize]
    rw [hsz]
    show D.ptEntry ((s, t) :: (H' ++ rest)) (s + D.ptSize H' + a) b = _
    simp only [D.ptEntry]
    rw [if_neg (by omega)]
    by_cases hb : s ≤ b
    · rw [if_pos ⟨by omega, hb⟩, show s + D.ptSize H' + a - s = D.ptSize H' + a by omega, ih]
      by_cases h2 : D.ptSize H' ≤ b - s
      · rw [if_pos h2, if_pos (by omega), show b - s - D.ptSize H' = b - (s + D.ptSize H') by omega]
      · rw [if_neg h2, if_neg (by omega)]
    · rw [if_neg (by omega), if_neg (by omega)]

theorem det_big (H : C.LPt) (s : ℕ) (t : ℂ) (r : ℕ) (hs : 2 ≤ s) (hr : D.ptSize H + s = r + 1) :
    (D.ptMatN (H ++ [(s, t)]) r).det = 0 := by
  apply Matrix.det_eq_zero_of_row_eq_zero (⟨D.ptSize H, by omega⟩ : Fin r)
  intro j
  show D.ptEntry (H ++ [(s, t)]) (D.ptSize H) j = 0
  have h := ptEntry_append_start [(s, t)] H 0 j
  rw [add_zero] at h
  rw [h]
  split_ifs with hj
  · simp only [D.ptEntry]
    rw [if_pos ⟨by omega, by omega⟩, if_neg (by omega)]
  · rfl

theorem ptG_big (TT : ℝ) (H : C.LPt) (s : ℕ) (t : ℂ) (r : ℕ) (hs : 2 ≤ s) (hr : D.ptSize H + s = r + 1) :
    D.ptG TT r (H ++ [(s, t)]) = Complex.normSq (D.ptMatN (H ++ [(s, t)]) (r + 1)).det := by
  unfold D.ptG
  rw [det_big H s t r hs hr]
  simp

theorem wPt_big (TT : ℝ) (H : C.LPt) (s : ℕ) (t : ℂ) (r : ℕ) (hs : 2 ≤ s) (hr : D.ptSize H + s = r + 1)
    (hG : 0 < D.ptG TT r (H ++ [(s, t)])) : Top.wPt TT r (H ++ [(s, t)]) = 1 := by
  unfold Top.wPt
  rw [ptG_big TT H s t r hs hr] at hG ⊢
  exact div_self hG.ne'

section top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem hsInner_zero_right' (A : Wq →L[ℂ] Wp) : B.hsInner A 0 = 0 := by
  unfold B.hsInner B.hsVec
  have : (WithLp.toLp 2 fun _ : Fin (Module.finrank ℂ Wq) => (0 : Wp)) = 0 := rfl
  simp only [ContinuousLinearMap.zero_apply, this, inner_zero_left]

theorem vecV_of_G (Bs : B.RealPlaceData P.k P.r Wp Wq) (ν' : Fin (2 * P.r + P.k + 1) → ℂ) (m₀ : B.Mat P.k P.r)
    (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Q : C.LPt)
    (hG : ¬ 0 < D.ptG (Tz P.k P.r Bs.z * Tz P.k P.r Bs.z') P.r Q) : D.vecV Bs ν' m₀ F Q = 0 := by
  unfold D.vecV
  rw [dif_neg (fun h => hG h.2)]

theorem topOf_big (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter)
    (H H' : C.LPt) (s : ℕ) (t t' : ℂ) (hs : 2 ≤ s) (hH : D.ptSize H + s = P.r + 1) (hH' : D.ptSize H' + s = P.r + 1) :
    Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP F w (H ++ [(s, t)]) (H' ++ [(s, t')]) =
      ∑ e : Wd.Ix (Fin w.length), ∑ ρ : M.Ty P,
        ((Real.sqrt (Top.cW P p.l0 w e ρ).re * Real.sqrt (Top.cW P p.l0 w e ρ).re : ℝ) : ℂ) *
          B.hsInner ((p.TP.E ρ).comp (D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e F) (H ++ [(s, t)])))
            ((p.TP.E ρ).comp (D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e F) (H' ++ [(s, t')]))) := by
  unfold Top.topOf
  refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun ρ _ => ?_
  set TT := Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z' with hTT
  by_cases h1 : 0 < D.ptG TT P.r (H ++ [(s, t)])
  · by_cases h2 : 0 < D.ptG TT P.r (H' ++ [(s, t')])
    · unfold Top.dH
      rw [wPt_big TT H s t P.r hs hH h1, wPt_big TT H' s t' P.r hs hH' h2, one_pow, one_mul]
    · rw [vecV_of_G _ _ _ _ _ h2, ContinuousLinearMap.comp_zero, hsInner_zero_right', mul_zero, mul_zero]
  · rw [vecV_of_G _ _ _ _ _ h1, ContinuousLinearMap.comp_zero, Formalism.FourierDecayAlt.P.PBD.hsInner_zero_left]
    simp

end top

end

end Formalism.FourierDecayAlt.P.PBL
