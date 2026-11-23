import Formalism.HermitianCurvature.HermitianCurvatureProofs.PointStep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Tower
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBH

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def PointStepT : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (h : C.LPt) (c : ℂ) (hh : D.IsLocPt h j) (hc : D.IsLocPt (h ++ [(1, c)]) (j + 1)),
    KB.CptCoef p.T.base F → ∀ γ ∈ B.GV P.k (P.r - (j + 1)),
    KB.slv p.T F (j + 1) hj [] _ hc.2 (fun a => a.elim0) γ =
      ∫ xx : U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1)),
        (psi P.k (P.r - j) (p.T.bs j).z cStd (rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.1) *
            star (psi P.k (P.r - j) (p.T.bs j).z' cStd (rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.2))) •
          KB.slv p.T F j (by omega) [] h hh.2 (fun a => a.elim0)
            ((rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.1)⁻¹ *
              mc (by omega : P.r - (j + 1) + 1 = P.r - j) c γ * rn1 (by omega : P.r - (j + 1) + 1 = P.r - j) xx.2)
        ∂((U.muRC P.k 1 (P.r - (j + 1))).prod (U.muRC P.k 1 (P.r - (j + 1))))

theorem asm_castV_castV {k a b d : ℕ} (h1 : a = b) (h2 : b = d) (v : Fin (2 * a + k + 1) → ℂ) :
    D.castV h2 (D.castV h1 v) = D.castV (h1.trans h2) v := by
  subst h1; subst h2; rfl

theorem castM_castM' {k a b d : ℕ} (h1 : a = b) (h2 : b = d) (g : B.Mat k a) :
    D.castM h2 (D.castM h1 g) = D.castM (h1.trans h2) g := by
  subst h1; subst h2; rfl

theorem sliceStep_of (hJ : JFStep) (hP : PointStepT) : KB.SliceStep := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj h c hh hc hF γ hγ hΩ
  have e : P.r - (j + 1) + 1 = P.r - j := by omega
  have hc0 : c ≠ 0 := (hc.1 (1, c) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hT := p.hT
  have key := hJ P.k (P.r - (j + 1)) (P.r - j) e Wp Wq (p.T.bs j) (p.T.bs (j + 1))
    (by rw [levTower_bs_z_eq_castV_liftVec p.T j hj, asm_castV_castV])
    (by rw [levTower_bs_z'_eq_castV_liftVec p.T j hj, asm_castV_castV])
    (fun y => by rw [tower_π p.T j hj, lev1, castM_castM'])
    (fun y => by rw [tower_π' p.T j hj, lev1, castM_castM'])
    (hT j (by omega)).1 (hT j (by omega)).2.1 (hT (j + 1) hj).1 (hT (j + 1) hj).2.1
    (hT j (by omega)).2.2 (hT (j + 1) hj).2.2
    (KB.slv p.T F j (by omega) [] h hh.2 fun a => a.elim0)
    (KB.slv p.T F (j + 1) hj [] _ hc.2 fun a => a.elim0) c hc0
    (Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j (by omega) [] h hh hF _)
    (fun γ' hγ' => hP Wp Wq P p F j hj h c hh hc hF γ' hγ') γ hγ hΩ
  rw [key, mc, castM_castM']

end Formalism.FourierDecayAlt.P.PBH
