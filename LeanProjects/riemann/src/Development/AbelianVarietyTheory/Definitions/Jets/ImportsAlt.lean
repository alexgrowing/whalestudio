import Mathlib
import Formalism.HermitianCurvature.StatementTBB

namespace GlobalTheory.TopVec

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

noncomputable section

def tv {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : Fin (P.r + 1) → ℂ) :
    PiLp 2 (fun _ : Wd.Ix (Fin w.length) × M.Ty P => PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)) :=
  WithLp.toLp 2 fun x =>
    ((Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
        Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) x.1 x.2 : ℝ) : ℂ) •
      B.hsVec ((p.TP.E x.2).comp (p.V (p.Θ.Θ w x.1 H) (TBB.bigPt P.r c)))

end

end GlobalTheory.TopVec
