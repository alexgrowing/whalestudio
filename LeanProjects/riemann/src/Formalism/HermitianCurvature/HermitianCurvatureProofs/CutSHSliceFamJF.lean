import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowVLift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AsmCastVCastV
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSH

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P.PBH

theorem sliceFamJF_cpt {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (j : ℕ)
    (Bs : B.RealPlaceData P.k (P.r - j) Wp Wq) (F : B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp))
    (hF : JFOKCpt (JC.parLev P j) Bs.z Bs.z' F) : KB.CptCoef Bs F := by
  obtain ⟨⟨hCC, ε, hε, hεG⟩, hcpt⟩ := hF
  refine ⟨Formalism.FourierDecayAlt.P.SmoothnessOrderArithmetic.ckOn_top_of_all (fun m => (hCC 0 m).choose_spec.1), ?_, ε, hε, hεG⟩
  have hcont : Continuous (fun g : B.Mat P.k (P.r - j) => B.gN g) := by
    unfold B.gN
    fun_prop
  obtain ⟨R, hR⟩ := (hcpt.isCompact.image hcont).bddAbove
  refine ⟨R, fun g _ hg => hR ⟨g, subset_tsupport F hg, rfl⟩⟩

private theorem liftVec_injective_apply {k i r' : ℕ} {v w : Fin (2 * r' + k + 1) → ℂ}
    (h : liftVec k i r' v = liftVec k i r' w) : v = w := by
  funext q
  have hq := congrFun h ⟨q.1 + i, by omega⟩
  simp only [liftVec] at hq
  rw [dif_pos ⟨by simp, by simp; omega⟩, dif_pos ⟨by simp, by simp; omega⟩] at hq
  simpa using hq

private theorem castM_castM_eq_castM_trans {k a b c : ℕ} (h1 : a = b) (h2 : b = c) (h3 : a = c) (g : B.Mat k a) :
    D.castM h2 (D.castM h1 g) = D.castM h3 g := by
  subst h1 h2
  rfl

theorem slice_family_orbital : SliceFamJF := by
  intro Wp Wq _ _ _ _ _ _ P T _ hN j hj _ _ F hF t ht γ hγ hΩ
  have e : P.r - (j + 1) + 1 = P.r - j := by omega
  have hC := sliceFamJF_cpt P j (T.bs j) F hF
  set c : ℂ := ((‖t‖ ^ (2 * (P.r - j) + P.k) : ℝ) : ℂ) with hc
  let f0 : B.Mat P.k (P.r - (j + 1)) → Wq →L[ℂ] Wp := (B.GV P.k (P.r - (j + 1))).indicator fun g =>
    ∫ xx : U.RC P.k 1 (P.r - (j + 1)) × U.RC P.k 1 (P.r - (j + 1)),
      (psi P.k (P.r - j) (T.bs j).z cStd (rn1 e xx.1) *
          star (psi P.k (P.r - j) (T.bs j).z' cStd (rn1 e xx.2))) •
        F ((rn1 e xx.1)⁻¹ * mc e t g * rn1 e xx.2)
      ∂(U.muRC P.k 1 (P.r - (j + 1))).prod (U.muRC P.k 1 (P.r - (j + 1)))
  have hsf : sliceFam T j hj F t = fun g => c • f0 g := by
    funext g
    simp only [sliceFam, f0, Set.indicator]
    split_ifs
    · rfl
    · rw [smul_zero]
  rw [hsf, JCx2.bc_JF_smul]
  congr 1
  obtain ⟨hW1, hW1', hN1⟩ := hN j (by omega)
  obtain ⟨hW0, hW0', hN0⟩ := hN (j + 1) hj
  refine jfStep P.k (P.r - (j + 1)) (P.r - j) e Wp Wq (T.bs j) (T.bs (j + 1)) ?_ ?_ ?_ ?_
    hW1 hW1' hW0 hW0' hN1 hN0 F f0 t ht hC ?_ γ hγ hΩ
  · apply liftVec_injective_apply (i := j)
    apply castV_inj (h := (by omega : j + (P.r - j) = P.r))
    rw [T.z_lev j (by omega), asm_castV_castV,
      lift_lift_V j (P.r - (j + 1)) (P.r - j) P.r (by omega) (by omega) (by omega), T.z_lev (j + 1) hj]
  · apply liftVec_injective_apply (i := j)
    apply castV_inj (h := (by omega : j + (P.r - j) = P.r))
    rw [T.z'_lev j (by omega), asm_castV_castV,
      lift_lift_V j (P.r - (j + 1)) (P.r - j) P.r (by omega) (by omega) (by omega), T.z'_lev (j + 1) hj]
  · intro y
    rw [T.π_lev (j + 1) hj, T.π_lev j (by omega)]
    congr 1
    simp only [lev1]
    rw [castM_castM_eq_castM_trans _ _ (by omega : 1 + (P.r - (j + 1)) = P.r - j),
      lift_lift_M j (P.r - (j + 1)) (P.r - j) P.r (by omega) (by omega) (by omega)]
  · intro y
    rw [T.π'_lev (j + 1) hj, T.π'_lev j (by omega)]
    congr 1
    simp only [lev1]
    rw [castM_castM_eq_castM_trans _ _ (by omega : 1 + (P.r - (j + 1)) = P.r - j),
      lift_lift_M j (P.r - (j + 1)) (P.r - j) P.r (by omega) (by omega) (by omega)]
  · intro g hg
    simp [f0, Set.indicator, hg]

end Formalism.FourierDecayAlt.P.CutSH
