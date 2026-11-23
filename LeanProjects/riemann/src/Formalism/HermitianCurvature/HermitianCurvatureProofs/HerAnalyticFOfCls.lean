import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumPairLevStarMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InvMemOfKappa
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PairOperatorCommute

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

section Gen

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S]
variable {𝒜 : StarSubalgebra ℂ A}

theorem Ts_mem (σ : Site A) (hp : σ.p ∈ 𝒜) (hc : σ.c ∈ 𝒜) (hci : σ.ci ∈ 𝒜) (Y : ℂ) (i j : Fin 2) :
    Ts σ Y i j ∈ 𝒜 := by
  unfold Ts Formalism.YangianSpanCharacter.T.Tm
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.mk_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  · exact add_mem (algebraMap_mem 𝒜 Y) hp
  · exact neg_mem hc
  · exact hci
  · exact zero_mem 𝒜

theorem bT_mem (σ : Site A) (hp : σ.p ∈ 𝒜) (hc : σ.c ∈ 𝒜) (hci : σ.ci ∈ 𝒜) (w : List (Letter ℂ S)) :
    bT σ w ∈ entSub 𝒜 := by
  induction w with
  | nil => exact (entSub 𝒜).one_mem
  | cons l w ih =>
    rw [bT]
    refine (entSub 𝒜).mul_mem (ins_mem _ fun i j => ?_) ih
    show io ((if l.plus then Ts σ l.pt else (Ts σ l.pt).map star) i j) ∈ entSub 𝒜
    apply io_mem
    split_ifs
    · exact Ts_mem σ hp hc hci l.pt i j
    · exact (star_mem (Ts_mem σ hp hc hci l.pt i j) : star _ ∈ 𝒜)

end Gen

section Lev

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem intOn_of_last {μ : Measure (Mt k r)} {U : Submodule ℂ (RadSp k r z z' π π')}
    (hI : IntLevOn μ (Fin.last r) U) : IntOn μ U := by
  intro c hc Φ hΦ Ψ hΨ
  obtain ⟨h1, -⟩ := hI c hc Φ hΦ Ψ hΨ
  have h2 := h1 (Classical.arbitrary _)
  rwa [glue_last_level] at h2

end Lev

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem herAnalyticF_of_cls (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0)
    (U : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (hKU : ∀ i, K i ≤ U i)
    (hI : ∀ i, IntLevOn μ i (U i))
    (hQ : ∀ i, ∀ Y : ℂ, star Y = Y → ∀ a b, st.QQ Y a b ∈ presAlg (U i))
    (hS : ∀ (i : Fin (P.r + 1)) (l : Fin P.r), i.val ≤ l.val →
      L.p l ∈ presAlg (U i) ∧ L.c l ∈ presAlg (U i) ∧ L.ci l ∈ presAlg (U i))
    (hfn : ∀ j, ∀ Φ ∈ U (Fin.last P.r), X.fn j Φ ∈ U (Fin.last P.r))
    (hT : ∀ Y : ℂ, star Y = Y → ∀ a b, X.QQ Y a b ∈ adjAlg μ (U (Fin.last P.r)) (intOn_of_last (hI _)))
    (hSA : ∀ (l : Fin P.r) (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r),
      L.p l ∈ adjLev μ l.castSucc (U l.castSucc) (hI _) c hc ∧ L.c l ∈ adjLev μ l.castSucc (U l.castSucc) (hI _) c hc ∧
        L.ci l ∈ adjLev μ l.castSucc (U l.castSucc) (hI _) c hc)
    (hPh : ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (l : Fin P.r) (x y : Ix S → RadSp P.k P.r z z' π π'),
      InK (K l.castSucc) x → InK (K l.castSucc) y → ∀ c ∈ OmX P.r,
      ∃ φ : ℂ → ℂ, Continuous φ ∧ (∀ t, t ≠ 0 → φ t = ph L st μ l w x y c t) ∧
        ∃ C : ℝ, ∀ t, ‖φ t‖ ≤ C * (1 + ‖t‖) ^ (-4 : ℤ)) :
    HerAnalyticF S P z z' π π' μ L st l0 K := by
  refine ⟨?_, ?_, ?_⟩
  · exact adjTop_of_tAdj P z z' π π' X μ L st K l0 hD (U (Fin.last P.r)) (intOn_of_last (hI _)) (hKU _) hfn hT
  · refine stepDens_of P z z' π π' μ L st K l0 (fun l => U l.castSucc) (fun l => hKU _) (fun l => hI _)
      (fun w hw l => siteStep_actual P z z' π π' X μ L st l0 w hD hw l)
      ?_ ?_ hPh
    · intro w _ l c hc a b
      obtain ⟨hp, hcc, hci⟩ := hSA l c hc
      exact bT_mem (site L l) hp hcc hci w a b
    · intro w hw l a b
      refine rrw_mem (QQi L st l.succ) (QQi_mem L st (presAlg (U l.castSucc)) l.succ (hQ _) ?_) w hw.1.2.1 a b
      intro l' hl'
      exact hS l.castSucc l' (by simp only [Fin.val_succ] at hl'; simp only [Fin.val_castSucc]; omega)
  · exact formInt_of_cls P z z' π π' μ L st K l0 U hKU hI hQ hS

end Top

end Formalism.FourierDecayAlt.P5.HerA
