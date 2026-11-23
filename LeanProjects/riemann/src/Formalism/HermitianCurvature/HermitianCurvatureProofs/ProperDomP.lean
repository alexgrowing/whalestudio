import Formalism.HermitianCurvature.HermitianCurvatureProofs.GNConjTranspose
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerMatrixLeviBlockThree

open Matrix MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBQ

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem properE {k p ρ n : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k n Wp Wq)
    (e : p + ρ = n) (Cs : Set (B.Mat k n)) (hCs : IsCompact Cs) :
    PartialBesselProperness.Proper Bj B0 e Cs (domP k n p B0.z B0.z') := by
  subst e
  exact properA Bj B0 (fun q hq => leviElement_mem_GV q hq)
    (fun y hy hyG => levi_move_into_big_cell k p ρ B0.z B0.z' B0.z_mem B0.z'_mem y hy hyG) Cs hCs

def ProperDomP : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (j : ℕ) (hj : j ≤ P.r) (Cs : Set (B.Mat P.k P.r)), IsCompact Cs →
    PartialBesselProperness.Proper (p.T.bs j) p.T.base (by omega : j + (P.r - j) = P.r) Cs (domP P.k P.r j p.T.base.z p.T.base.z')

end Formalism.FourierDecayAlt.P.PBQ

namespace Formalism.FourierDecayAlt.P

theorem proper_left_variables_domain : PBQ.ProperDomP := by
  intro Wp Wq _ _ _ _ _ _ P p j hj Cs hCs
  exact PBQ.properE (p.T.bs j) p.T.base _ Cs hCs

end Formalism.FourierDecayAlt.P
