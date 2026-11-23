import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceOmBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermPartsCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ToStdAppend

namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt MeasureTheory NumberField

noncomputable section

theorem ptSize_toStd (r : ℕ) (g : ℝ) : ∀ (b : ℕ) (P : C.LPt), D.ptSize (D.toStd r g b P) = D.ptSize P
  | _, [] => rfl
  | b, (s, t) :: rest => by
    simp only [D.toStd, D.ptSize, List.map_cons, List.sum_cons] at *
    have := ptSize_toStd r g (b + s) rest
    simp only [D.ptSize] at this
    rw [this]

section defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def lamP (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (i : ℕ) (P : C.LPt) : ℝ :=
  √(C.nLoc S.G.k S.G.r S.fr (S.pd v).G P) /
    (D.bSt (D.kapG (S.g : ℝ) (S6.rd E)) P *
      √(D.GamLev S.G.k S.G.r (D.kapG (S.g : ℝ) (S6.rd E)) (D.deG (S.g : ℝ) (S6.rd E)) i * S.sizeAt v a))

end defs

def GNSetC : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (v : Fin S.f) (ε : ℝ) (i : ℕ)
    (hi : i ≤ S.G.r) (a : List C.Letter) (P Q : C.LPt) (hP : D.IsLocPt P i) (hQ : D.IsLocPt Q i),
    KB.gN (PBL.setC S p F) v ε i a P Q =
      ((lamP S v a i P * lamP S v a i Q : ℝ) : ℂ) *
        D.formLev (p v).T (M.sgn (D.parOf S v) (p v).l0) ⟨i, by have e : (D.parOf S v).r = S.G.r := rfl; omega⟩ a
          (KB.slv (p v).T (F v ε) i hi a (D.toStd S.G.r (S.g : ℝ) 1 P) (by
            rw [← hP.2]; exact FormNormSumIdentities.ptSize_toStd S.G.r (S.g : ℝ) 1 P))
          (KB.slv (p v).T (F v ε) i hi a (D.toStd S.G.r (S.g : ℝ) 1 Q) (by
            rw [← hQ.2]; exact FormNormSumIdentities.ptSize_toStd S.G.r (S.g : ℝ) 1 Q))

def GermConst : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (a : List C.Letter) (b s : ℕ), 0 < S.G.g1 → 0 < S.G.g2 →
    1 ≤ b → 2 ≤ s → b + s - 1 ≤ S.G.r → ∀ h : C.LPt, D.ptSize h = b - 1 →
    ∃ μ₀ : ℝ, ∀ x D z : ℂ, x ≠ 0 → D ≠ 0 → z ^ s = D →
      (‖x‖ ^ (s - 1) * (√(KB.dlB S (b + s - 1) 1))⁻¹ * lamP S v a (b + s - 1) (h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)]) *
          kapB (s - 2) =
        μ₀ * ((‖GermFibreKernels.fs S.G.r (S.g : ℝ) b (s - 1) x⁻¹‖ ^ (s - 1))⁻¹ *
          ‖GermFibreKernels.fs S.G.r (S.g : ℝ) b (s - 1) x⁻¹‖ ^ ((s - 1) * (U.Mlev S.G.k (S.G.r - (b + s - 1)) + (s - 2))) *
          ‖GermFibreKernels.fs S.G.r (S.g : ℝ) (b + s - 1) 1 (x ^ (s - 1) * D)‖ ^ (U.Mlev S.G.k (S.G.r - (b + s - 1)) - 2))) ∧
      ((s : ℝ) * ‖z‖ ^ (s - 1))⁻¹ * (√(KB.dlB S b s))⁻¹ * lamP S v a (b + s - 1) (h ++ [(s, z)]) *
          Real.pi ^ (s * (s - 1) / 2) =
        μ₀ * (‖GermFibreKernels.fs S.G.r (S.g : ℝ) (b + s - 1) 1 (x ^ (s - 1) * D) *
            GermFibreKernels.fs S.G.r (S.g : ℝ) b (s - 1) x⁻¹ ^ (s - 1)‖ ^ (U.Mlev S.G.k (S.G.r - (b + s - 1)) - 2) *
          ((s : ℝ)⁻¹ * ‖GermFibreKernels.fs S.G.r (S.g : ℝ) b s z‖ ^ ((s - 1) ^ 2)))

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities
