import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmPActualCptOfStepForm

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

section Ent

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)}

theorem site_lc (X : ActualOps P.k P.r z z' π π') {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r}
    (hAL : IsActualLevel X L) (l : Fin P.r) :
    L.p l ∈ presAlg (lcSub P.k P.r z z' π π') ∧ L.c l ∈ presAlg (lcSub P.k P.r z z' π π') ∧
      L.ci l ∈ presAlg (lcSub P.k P.r z z' π π') := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hAL.1 l]; exact mkPair_mem_preservingAlgebra (op_lc X l 0) (neg_lc (op_lc X l 3))
  · rw [hAL.2.2.1 l]; exact mkPair_mem_preservingAlgebra (op_lc X l 1) (op_lc X l 4)
  · rw [hAL.2.2.2.1 l]; exact mkPair_mem_preservingAlgebra (op_lc X l 2) (op_lc X l 5)

theorem QQ_lc (X : ActualOps P.k P.r z z' π π') (Y : ℂ) (a b : Fin 2) :
    X.QQ Y a b ∈ presAlg (lcSub P.k P.r z z' π π') :=
  mkPair_mem_preservingAlgebra (t_lc X Y a b) (t_lc X (star Y) b a)

theorem RRi_lc (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0) (i : Fin (P.r + 1)) (w : List (Letter ℂ S))
    (hw : ∀ l ∈ w, star l.pt = l.pt) : RRi L st i w ∈ entSub (presAlg (lcSub P.k P.r z z' π π')) := by
  obtain ⟨-, -, hAL, hQQ, -⟩ := hD
  refine rrw_mem (QQi L st i) (QQi_mem L st _ i (fun Y _ a b => ?_) (fun l _ => site_lc X hAL l)) w hw
  rw [hQQ Y, Matrix.smul_apply]
  exact (presAlg (lcSub P.k P.r z z' π π')).smul_mem (QQ_lc X Y a b) _

end Ent

section G

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem int_lc (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {Φ Ψ : RadSp k r z z' π π'}
    (hΦ : Φ ∈ lcSub k r z z' π π') (hΨ : Ψ ∈ lcSub k r z z' π π') (c : Fin r → ℂ) :
    Integrable (fun g : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ := by
  by_cases hc : c ∈ OmX r
  · exact intOn_cpt μ hμ c hc Φ (lcSub_le_cptSub hΦ) Ψ (lcSub_le_cptSub hΨ)
  · have e : (fun g : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
        ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) = fun _ => 0 := by
      funext g
      rw [radSp_zero_off Φ (x := (c, Matrix.of g)) (fun h => hc h.1)]
      exact hsInner_zero_left _
    rw [e]; exact integrable_zero _ _ _

end G

section Form

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem formIntG_herKc (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (hD : IsData P z z' π π' X μ L st l0) (hz : D.z = z) (hz' : D.z' = z')
    (hπ : D.π = π) (hπ' : D.π' = π') (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w)
    (i : Fin (P.r + 1)) (c : Fin P.r → ℂ) (x y : Ix S → RadSp P.k P.r z z' π π')
    (hx : InK (herKc S P z z' π π' L st l0 D i) x) (hy : InK (herKc S P z z' π π' L st l0 D i) y)
    (c' : Cf P.r i) (a : Ix S) :
    Integrable (fun g : Mt P.k P.r =>
      B.hsInner ((act (RRi L st i w) x a : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
        ((y a : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ := by
  have hle := herKc_le_lc (S := S) (st := st) (l0 := l0) X hD.2.2.1
    (fun F Φ hF hΦ => jfCptLocAll Wp Wq P z z' π π' D F Φ hD.1 hz hz' hπ hπ' hF hΦ) i
  have hRR := RRi_lc X μ L st l0 hD i w hw.1.2.1
  have hu : act (RRi L st i w) x a ∈ lcSub P.k P.r z z' π π' :=
    (lcSub P.k P.r z z' π π').sum_mem fun b _ => (hRR a b).1 _ (hle (hx b))
  exact int_lc μ hD.2.1 hu (hle (hy a)) _

def FormIntOuterCpt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (i : Fin (P.r + 1)) (c : Fin P.r → ℂ), c ∈ OmX P.r →
    ∀ x y : Ix S → RadSp P.k P.r z z' π π', InK (herKc S P z z' π π' L st l0 D i) x →
      InK (herKc S P z z' π π' L st l0 D i) y →
      Integrable (fun c' : Cf P.r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        ∑ a, pairAt μ (act (RRi L st i w) x a) (y a) (glue i c c'))

def StepDensCptAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    StepDens (S := S) P z z' π π' μ L st (herKc S P z z' π π' L st l0 D) l0

theorem stepFormCptAll_of (hSD : StepDensCptAll) (hFO : FormIntOuterCpt) : StepFormCptAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ'
  refine ⟨hSD Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ', fun w hw i c hc x y hx hy => ⟨?_, ?_⟩⟩
  · exact fun c' a => formIntG_herKc P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' w hw i c x y hx hy c' a
  · exact hFO Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' w hw i c hc x y hx hy

theorem thmPActualCpt_of_outer (hSD : StepDensCptAll) (hFO : FormIntOuterCpt) : ThmPActualCpt :=
  thmPActualCpt_of_stepForm (stepFormCptAll_of hSD hFO)

end Form

end Formalism.FourierDecayAlt.P5.HerC
