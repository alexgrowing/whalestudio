import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDom

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

def NFOpOKMulG : Prop :=
  ∀ C : ℝ, ∃ C' : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (N : ℕ) (Th : B.DiffOp P.k P.r Wp Wq), NFOpOK C p N Th →
      ∃ Th' : B.DiffOp P.k P.r Wp Wq, NFOpOK C' p N Th' ∧
        ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r),
          B.opApply Th' F g = ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ N : ℝ) : ℂ) • B.opApply Th F g

end

end Formalism.FourierDecayAlt.P.CutBP
