import Formalism.HermitianCurvature.CompositeFormulaLevelZero

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem ofWordRR : OfWordRR := by
  intro A S _ _ _ _ _ r L st w
  induction w with
  | nil =>
    exact ⟨by simp [Fr.ofWord, RRw, Fr.Start.frame], fun Y => by simp [Fr.ofWord, TTw, Fr.Start.frame]⟩
  | cons l w ih =>
    obtain ⟨ih1, ih2⟩ := ih
    cases hl : l.plus
    · exact ⟨by simp [Fr.ofWord, RRw, hl, Fr.FrameData.minus, ih1, ih2],
        fun Y => by simp [Fr.ofWord, TTw, hl, Fr.FrameData.minus, ih2]⟩
    · exact ⟨by simp [Fr.ofWord, RRw, hl, Fr.FrameData.plus, ih1, ih2],
        fun Y => by simp [Fr.ofWord, TTw, hl, Fr.FrameData.plus, ih2]⟩

section

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem tprod_ge (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (Y : ℂ) (i : ℕ) (h : r ≤ i) :
    tprod L Y i = 1 := by
  rw [tprod, dif_neg (by omega)]

theorem QQi_last (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
    (Y : ℂ) : QQi L st (Fin.last r) Y = st.QQ Y := by
  rw [QQi, Fin.val_last, tprod_ge L (star Y) r le_rfl, tprod_ge L Y r le_rfl, Matrix.conjTranspose_one,
    one_mul, mul_one]

end

theorem topIdentFromParts {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ) :
    TopIdentFromParts (S := S) P z z' π π' X μ L st K l0 := by
  intro hD hFA hOW hAdj w hw x y hx hy c hc
  obtain ⟨hint, heq⟩ := hAdj w hw x y hx hy c hc
  refine ⟨hint, ?_⟩
  have hQ : QQi L st (Fin.last P.r) = st.QQ := funext fun Y => QQi_last L st Y
  have hfr := hFA (Pr (RadSp P.k P.r z z' π π')) S P.r L st w hD.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.2 hw.1
  have hRR : RRi L st (Fin.last P.r) w =
      star (Fr.ofWord L st w).F * (Fr.ofWord L st w).d L * (Fr.ofWord L st w).F := by
    rw [RRi, hQ, ← (hOW _ S P.r L st w).1, hfr.form]
  rw [RRform, hRR, heq]

end Formalism.FourierDecayAlt.P5
