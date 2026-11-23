import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopRatio
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InsertUnitMatrixZeroApply

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd
open scoped ComplexConjugate

noncomputable section

section cs

variable {n : ℕ}

theorem xs_upL (x0 : ℂ → ℂ) : ∀ (L : List (Letter ℂ (Fin n))) (E : Ix (Fin (n + 1))) (Y : ℂ),
    Fr.xs x0 (L.map PBF.upL) E Y = Fr.xs x0 L (fun a => E a.succ) Y
  | [], _, _ => rfl
  | l :: L, E, Y => by
    simp only [List.map_cons, Fr.xs]
    rw [xs_upL x0 L E Y]
    rfl

theorem cs_upL (x0 q0 : ℂ → ℂ) : ∀ (L : List (Letter ℂ (Fin n))) (E : Ix (Fin (n + 1))),
    Fr.cs x0 q0 (L.map PBF.upL) E = Fr.cs x0 q0 L (fun a => E a.succ)
  | [], _ => rfl
  | l :: L, E => by
    simp only [List.map_cons, Fr.cs]
    simp only [cs_upL, xs_upL,
      show qw q0 (L.map PBF.upL) = qw q0 L from funext fun Y => PBF.qw_map_reindex q0 Fin.succ L Y]
    rfl

theorem cW_cons_plus (P : M.Par) (l0 : ℕ) (y : ℝ) (w : List C.Letter) (E : Ix (Fin (w.length + 1))) (ρ : M.Ty P) :
    Top.cW P l0 ((true, y) :: w) E ρ = Top.cW P l0 w (fun a => E a.succ) ρ *
      (if E 0 = 0 then qw (M.qC P) (D.positionted w) (y : ℂ) /
          Fr.xs (fun Y => M.sgn P l0 * M.xC P ρ Y) (D.positionted w) (fun a => E a.succ) ((y : ℂ) + 1)
        else Fr.xs (fun Y => M.sgn P l0 * M.xC P ρ Y) (D.positionted w) (fun a => E a.succ) (y : ℂ)) := by
  unfold Top.cW
  rw [PBF.positioned_cons]
  simp only [Fr.cs, if_true]
  simp only [cs_upL, xs_upL, show qw (M.qC P) ((D.positionted w).map PBF.upL) = qw (M.qC P) (D.positionted w) from
    funext fun Y => PBF.qw_map_reindex _ Fin.succ _ Y]

def topRprod {P : M.Par} (l0 : ℕ) (a : List C.Letter) (e : Ix (Fin a.length)) (ρ : M.Ty P) : List ℝ → ℂ
  | [] => 1
  | y :: ys => topRprod l0 a e ρ ys * topR l0 (KB.plusW ys a) (KB.firstSt ys e) ρ y

theorem cW_plusW (P : M.Par) (l0 : ℕ) (a : List C.Letter) (e : Ix (Fin a.length)) (ρ : M.Ty P) :
    ∀ ys : List ℝ, Top.cW P l0 (KB.plusW ys a) (KB.firstSt ys e) ρ = Top.cW P l0 a e ρ * topRprod l0 a e ρ ys
  | [] => by simp [topRprod, KB.plusW, KB.firstSt]
  | y :: ys => by
    have h := cW_cons_plus P l0 y (KB.plusW ys a) (Fin.cons (0 : Fin 2) (KB.firstSt ys e)) ρ
    simp only [Fin.cons_zero, Fin.cons_succ, if_true] at h
    show Top.cW P l0 ((true, y) :: KB.plusW ys a) (Fin.cons (0 : Fin 2) (KB.firstSt ys e)) ρ = _
    rw [h, cW_plusW P l0 a e ρ ys]
    simp only [topRprod, topR]
    ring

end cs

end

end Formalism.FourierDecayAlt.P.PBL
