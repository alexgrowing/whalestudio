import Formalism.HermitianCurvature.HermitianCurvatureProofs.TLChoiceChk
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MinusId
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LetterLiftOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MatrixUnitZeroZeroEqInsert
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IdentityOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellValues
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAlgebraFacts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftCapelliOperators
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftZeroOrder
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftOfFunctions
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftOfXOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvMulVecOfFixedVector
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliVectorFrame
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliVectorEquivariance
import Formalism.HermitianCurvature.HermitianCurvatureProofs.XFibreOfParts

namespace Formalism.FourierDecayAlt.P

theorem lift_of_x : Formalism.FourierDecayAlt.TL.LiftX :=
  lift_of_x_of_parts lift_zero_order lift_closed_under_operations
    (x_fibre_of_parts big_cell_values omega_polynomial_facts capelli_vector_frame capelli_vector_equivariance)

set_option maxHeartbeats 400000 in

theorem top_lift_exists : Formalism.FourierDecayAlt.TL.TopLiftExists3 := by
  classical
  refine ⟨11, by norm_num, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 hl1 hlk hD
  obtain ⟨hA, hcap, hxi⟩ := actual_algebra_facts Wp Wq P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 hD
  obtain ⟨hmono, hzero, hadd, hsmul, hmul⟩ := lift_closed_under_operations Wp Wq P Bs
  have hF := lift_of_functions Wp Wq P Bs X L hD.2.2.1
  have hX := lift_of_x Wp Wq P Bs X μ L st l0 hD
  have hK := lift_capelli_operators Wp Wq P Bs X μ L st l0 hD
  have hpoly : ∀ (p : Polynomial ℂ) (a : Q.Pr ↥(Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')),
      TL.Lifts P Bs 0 0 a → TL.Lifts P Bs 0 0 (Polynomial.aeval a p) := by
    intro p a ha
    have hpow : ∀ m : ℕ, TL.Lifts P Bs 0 0 (a ^ m) := by
      intro m
      induction m with
      | zero => simpa using hF.1
      | succ m ih => simpa [pow_succ] using hmul 0 0 0 0 _ _ ih ha
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa using hadd 0 0 _ _ hp hq
    | monomial m c =>
      rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
      exact hsmul 0 0 _ c (hpow m)
  have hn : P.r + 1 ≤ 2 * P.r + P.k + 1 := by omega
  have hSys : TL.LiftSys L st (2 * P.r + P.k + 1) (TL.Lifts P Bs) :=
    { mono := fun h1 h2 h => hmono _ _ _ _ _ h1 h2 h
      zero := hzero
      add := fun h1 h2 => hadd _ _ _ _ h1 h2
      smul := fun z h => hsmul _ _ _ z h
      one := hF.1
      mul := fun h1 h2 => hmul _ _ _ _ _ _ h1 h2
      fns := hF.2
      x := fun Y _ => hX Y
      xi := fun Y hY _ => by
        obtain ⟨p, hp⟩ := hxi Y hY
        rw [hp]
        exact hpoly p _ (hX Y)
      cap := fun Y hY => by
        rw [← hcap Y hY]
        exact hK Y }
  have hWL := TL.wordLiftOfParts word_recursion
    (letter_lift_of_parts TL.basicLift l_shape m_shape_of_l_shape)
  have hAdm : ∀ w : List C.Letter, KB.CutWord P l0 w → Fr.admitted st (D.positionted w) := by
    intro w hw
    have hM : M.CutWord P l0 (D.positionted w) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [D.positionted, List.map_ofFn]
        exact List.nodup_ofFn.mpr (fun a b h => h)
      · intro a ha
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
        exact ⟨by simp, by simpa using hw.1 i⟩
      · rw [D.positionted, List.pairwise_ofFn]
        intro i j hij
        simpa using hw.2 i j (ne_of_lt hij)
    obtain ⟨h1, h2, h3, h4⟩ := cut_admissible interlacing_sign q_positive_interlacing q_positive_shift
      types_interlace realPoints_statement P hD.1.1 l0 hl1 hlk (Fin w.length) (D.positionted w) hM
    refine ⟨h1, h2, ?_, h4⟩
    rw [hD.2.2.2.2.1, hD.2.2.2.2.2.1]
    exact h3
  have hLift : ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), ∃ Dop : B.DiffOp P.k P.r Wp Wq,
      KB.CutWord P l0 w → ∃ (nf : ℕ) (fib : Fin nf → B.Mat P.k P.r → C6.EndH Wp Wq),
        (∀ j, C6.FibBound Bs (fib j)) ∧
        C6.InDDPlus Bs fib ∅ (w.length * (2 * P.r + P.k + 1))
          (11 * w.length * (P.r + 1) * (2 * P.r + P.k + 1)) Dop ∧
        TL.RadIs P Bs Dop (((Fr.ofWord L st (D.positionted w)).F * TL.bTA L (D.positionted w)) e Wd.e1).1 := by
    intro w e
    by_cases hw : KB.CutWord P l0 w
    · have h := hWL _ (Fin w.length) P.r (2 * P.r + P.k + 1) L st (TL.Lifts P Bs) (D.positionted w) hA hSys hn
        (hAdm w hw) e
      have hl : (D.positionted w).length = w.length := List.length_ofFn
      rw [hl] at h
      obtain ⟨nf, fib, Dop, h1, h2, h3⟩ := h
      exact ⟨Dop, fun _ => ⟨nf, fib, h1, h2, h3⟩⟩
    · obtain ⟨Dop, -⟩ := identity_operator P.k P.r Wp Wq Bs
      exact ⟨Dop, fun h => absurd h hw⟩
  choose Dw hDw using hLift
  obtain ⟨D0, hD0, hD0F⟩ := identity_operator P.k P.r Wp Wq Bs
  refine ⟨⟨fun w e F => if w = [] then F else B.opApply (Dw w e) F, fun e F => by simp⟩, ?_, ?_⟩
  · intro w hw F hFc Φ hΦ e
    dsimp only
    have hact : ∀ (M0 : Wd.SlopeTestRemainingChoices (Fin w.length) (Q.Pr ↥(Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
        P5.act M0 (Top.firstStateVector Φ) e = (M0 e Wd.e1).1 Φ := by
      intro M0
      unfold P5.act Top.firstStateVector
      rw [Finset.sum_eq_single Wd.e1]
      · exact congrArg _ (if_pos rfl)
      · intro b _ hb
        have hb' : ¬ (b = fun _ => 0) := hb
        rw [if_neg hb', map_zero]
      · simp
    rw [hact]
    by_cases hne : w = []
    · subst hne
      simp only [if_true]
      have h1 : (Fr.ofWord L st (D.positionted ([] : List C.Letter))).F * P5.bTall L (D.positionted ([] : List C.Letter)) = 1 := by
        simp [D.positionted, Fr.ofWord, P5.bTall, P5.bTl, Wd.bT, Fr.Start.frame]
      have he : e = Wd.e1 := funext fun i => (Nat.not_lt_zero _ i.2).elim
      rw [h1, he]
      simpa using hΦ
    · rw [if_neg hne]
      obtain ⟨nf, fib, -, -, hR⟩ := hDw w e hw
      exact hR F hFc Φ hΦ
  · intro w hw e
    dsimp only
    by_cases hne : w = []
    · refine ⟨0, fun j => j.elim0, 0, 0, D0, fun j => j.elim0, ?_, by norm_num <;> positivity,
        by norm_num <;> positivity, ?_⟩
      · convert hD0 using 2
      · intro F g _
        rw [if_pos hne, hD0F]
    · obtain ⟨nf, fib, h1, h2, -⟩ := hDw w e hw
      refine ⟨nf, fib, _, _, Dw w e, h1, h2, ?_, ?_, ?_⟩
      · push_cast
        nlinarith [show (0:ℝ) ≤ (w.length:ℝ) * (2 * (P.r:ℝ) + P.k + 1) by positivity]
      · push_cast
        nlinarith [show (0:ℝ) ≤ (w.length:ℝ) * (2 * (P.r:ℝ) + P.k + 1) by positivity]
      · intro F g _
        rw [if_neg hne]

end Formalism.FourierDecayAlt.P
