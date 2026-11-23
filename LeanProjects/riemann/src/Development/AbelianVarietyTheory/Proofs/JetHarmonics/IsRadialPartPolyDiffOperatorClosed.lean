import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.JdPolyOKPolynomialOperators
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PolyOpExistsComposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftClosedUnderOperations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftCapelliOperators

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory

noncomputable section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

end

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma polyOp_mono' {n n' κ κ' : ℕ} {Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq} (h : _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n κ Θ)
    (hn : n ≤ n') (hκ : κ ≤ κ') : _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n' κ' Θ := by
  unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at h ⊢
  intro T hT
  obtain ⟨hlen, Q, ⟨q, hq, hQ⟩, hc, hca⟩ := h T hT
  exact ⟨hlen.trans hn, Q, ⟨q, hq.trans hκ, hQ⟩, hc, hca⟩

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma polyOp_nil (n κ : ℕ) : _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n κ ([] : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) := by
  unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp
  simp

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma opApply_nil (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) :
    _root_.Formalism.FourierDecayAlt.B.opApply ([] : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) F g = 0 := by
  simp [_root_.Formalism.FourierDecayAlt.B.opApply]

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma polyOp_of_polyOp_cons {n κ : ℕ} {T : _root_.Formalism.FourierDecayAlt.B.DTerm k r Wp Wq} {Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq}
    (h : _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n κ (T :: Θ)) : _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n κ Θ := by
  unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at h ⊢
  exact fun T' hT' => h T' (by simp [hT'])

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma totalDegree_lin_le_one {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (i : _root_.PI.UnitaryGroupMassFormula.UsCompose.Vr N) :
    (_root_.PI.UnitaryGroupMassFormula.UsCompose.lin X i).totalDegree ≤ 1 := by
  rcases i with x | x <;>
  · simp only [_root_.PI.UnitaryGroupMassFormula.UsCompose.lin]
    refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun c _ => ?_)
    exact (totalDegree_mul _ _).trans (by simp [totalDegree_C, totalDegree_X])

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma totalDegree_pderiv_add_one_le_of_ne_zero {σ : Type*} (q : MvPolynomial σ ℂ) (i : σ)
    (h : pderiv i q ≠ 0) : (pderiv i q).totalDegree + 1 ≤ q.totalDegree := by
  have hne : (pderiv i q).support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (by simpa [MvPolynomial.support_eq_empty] using h)
  obtain ⟨m, hm, hdeg⟩ := Finset.exists_mem_eq_sup _ hne (fun s : σ →₀ ℕ => s.sum fun _ e => e)
  rw [totalDegree, hdeg]
  have hm' := (mem_support_iff.mp hm)
  rw [coeff_pderiv] at hm'
  have hs : m + Finsupp.single i 1 ∈ q.support := by
    rw [mem_support_iff]
    intro h0
    exact hm' (by simp [h0])
  have := le_totalDegree hs
  rwa [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl] at this

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma totalDegree_dP_le {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ)
    (q : MvPolynomial (_root_.PI.UnitaryGroupMassFormula.UsCompose.Vr N) ℂ) : (_root_.PI.UnitaryGroupMassFormula.UsCompose.dP X q).totalDegree ≤ q.totalDegree := by
  unfold _root_.PI.UnitaryGroupMassFormula.UsCompose.dP
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
  by_cases h : pderiv i q = 0
  · simp [h]
  · exact (totalDegree_mul _ _).trans
      ((Nat.add_le_add_left (totalDegree_lin_le_one X i) _).trans (totalDegree_pderiv_add_one_le_of_ne_zero q i h))

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma exists_isPolyDeg_hasDerivAt_comp_crv {X : _root_.Formalism.FourierDecayAlt.B.Mat k r} {κ : ℕ} {Q : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ}
    (hQ : _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κ Q) : ∃ Q' : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ, _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κ Q' ∧
      ∀ g, HasDerivAt (fun t => Q (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t)) (Q' g) 0 := by
  obtain ⟨q, hq, hQq⟩ := hQ
  refine ⟨fun g => MvPolynomial.eval (_root_.PI.UnitaryGroupMassFormula.UsCompose.vars g) (_root_.PI.UnitaryGroupMassFormula.UsCompose.dP X q),
    ⟨_root_.PI.UnitaryGroupMassFormula.UsCompose.dP X q, (totalDegree_dP_le X q).trans hq, fun g => rfl⟩, fun g => ?_⟩
  have e : (fun t => Q (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t)) =
      fun t => MvPolynomial.eval (_root_.PI.UnitaryGroupMassFormula.UsCompose.vars (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t)) q := by
    funext t
    rw [hQq]
    rfl
  rw [e]
  exact _root_.PI.UnitaryGroupMassFormula.UsCompose.hasDerivAt_poly X g q

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma ckOn_rightWordDeriv_of_forall_inLie {F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp}
    (hF : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F) : ∀ w : List (_root_.Formalism.FourierDecayAlt.B.Mat k r), (∀ X ∈ w, _root_.Formalism.FourierDecayAlt.B.inLie k r X) →
      _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) (_root_.Formalism.FourierDecayAlt.B.Rw w F)
  | [], _ => by simpa [_root_.Formalism.FourierDecayAlt.B.Rw] using hF
  | X :: w, hw => by
    have h := ckOn_rightWordDeriv_of_forall_inLie hF w (fun Y hY => hw Y (by simp [hY]))
    have := _root_.Formalism.FourierDecayAlt.P.B5.ckOn_RdV (m := ⊤) (hw X (by simp)) (by simpa using h)
    simpa [_root_.Formalism.FourierDecayAlt.B.Rw] using this

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma opApply_cons' (T : _root_.Formalism.FourierDecayAlt.B.DTerm k r Wp Wq) (Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq)
    (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) :
    _root_.Formalism.FourierDecayAlt.B.opApply (T :: Θ) F g = (T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word F g) + _root_.Formalism.FourierDecayAlt.B.opApply Θ F g := by
  simp [_root_.Formalism.FourierDecayAlt.B.opApply]

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma polyOp_deriv_lemma_10 {X : _root_.Formalism.FourierDecayAlt.B.Mat k r} (hX : _root_.Formalism.FourierDecayAlt.B.inLie k r X) {κ : ℕ} :
    ∀ (Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) (n : ℕ), _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n κ Θ → ∃ Θ' : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq,
      _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp (n + 1) κ Θ' ∧ ∀ F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp, _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F →
        ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r,
          HasDerivAt (fun t => _root_.Formalism.FourierDecayAlt.B.opApply Θ F (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t)) (_root_.Formalism.FourierDecayAlt.B.opApply Θ' F g) 0
  | [], n, _ => ⟨[], polyOp_nil _ _, fun F _ g _ => by
      simpa [opApply_nil] using hasDerivAt_const (0 : ℝ) (0 : Wq →L[ℂ] Wp)⟩
  | T :: Θ, n, h => by
    have hT := h
    unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at hT
    obtain ⟨hlen, Q, hQ, hc, -⟩ := hT T (by simp)
    obtain ⟨Θr, hJr, hDr⟩ := polyOp_deriv_lemma_10 hX Θ n (polyOp_of_polyOp_cons h)
    obtain ⟨Q', hQ', hdQ⟩ := exists_isPolyDeg_hasDerivAt_comp_crv (X := X) hQ
    have hw : ∀ Y ∈ X :: T.word, _root_.Formalism.FourierDecayAlt.B.inLie k r Y := by
      intro Y hY
      rcases List.mem_cons.mp hY with rfl | hY
      exacts [hX, T.word_lie Y hY]
    refine ⟨_root_.GlobalTheory.HatNF.PolyComp.scalTerm Q' T.word T.word_lie ::
      _root_.GlobalTheory.HatNF.PolyComp.scalTerm Q (X :: T.word) hw :: Θr, ?_, ?_⟩
    · unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at hJr ⊢
      intro T' hT'
      rcases List.mem_cons.mp hT' with rfl | hT'
      · exact ⟨hlen.trans (Nat.le_succ n), Q', hQ', fun _ => rfl, fun _ => rfl⟩
      rcases List.mem_cons.mp hT' with rfl | hT'
      · exact ⟨by simp [_root_.GlobalTheory.HatNF.PolyComp.scalTerm, hlen], Q, hQ, fun _ => rfl, fun _ => rfl⟩
      · exact hJr T' hT'
    · intro F hF g hg
      have hG := ckOn_rightWordDeriv_of_forall_inLie hF T.word T.word_lie
      have hD : HasDerivAt (fun t => _root_.Formalism.FourierDecayAlt.B.Rw T.word F (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t))
          (_root_.Formalism.FourierDecayAlt.B.Rw (X :: T.word) F g) 0 := by
        have := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_diff (x := (false, X)) hX (_root_.Formalism.FourierDecayAlt.P.B6.smooth_on_mono le_top hG) hg hg
        rw [← _root_.PI.UnitaryGroupMassFormula.UsCompose.RdV_eq_Dx] at this
        exact this
      have hfun : (fun t => _root_.Formalism.FourierDecayAlt.B.opApply (T :: Θ) F (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t)) = fun t =>
          Q (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t) • _root_.Formalism.FourierDecayAlt.B.Rw T.word F (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t) +
            _root_.Formalism.FourierDecayAlt.B.opApply Θ F (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv (false, X) g t) := by
        funext t
        rw [opApply_cons', hc]
        simp
      rw [hfun]
      have := ((hdQ g).smul hD).add (hDr F hF g hg)
      refine this.congr_deriv ?_
      rw [opApply_cons', opApply_cons']
      simp only [_root_.GlobalTheory.HatNF.PolyComp.scalTerm, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.crv_zero]
      abel

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma polyOp_word_lemma_6 {κ : ℕ} : ∀ (u : List (_root_.Formalism.FourierDecayAlt.B.Mat k r)), (∀ X ∈ u, _root_.Formalism.FourierDecayAlt.B.inLie k r X) →
    ∀ (Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) (n : ℕ), _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n κ Θ → ∃ Θ' : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq,
      _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp (n + u.length) κ Θ' ∧ ∀ F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp,
        _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F → ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r,
          _root_.Formalism.FourierDecayAlt.B.Rw u (_root_.Formalism.FourierDecayAlt.B.opApply Θ F) g = _root_.Formalism.FourierDecayAlt.B.opApply Θ' F g
  | [], _, Θ, n, h => ⟨Θ, h, fun F _ g _ => rfl⟩
  | X :: u, hu, Θ, n, h => by
    have hX : _root_.Formalism.FourierDecayAlt.B.inLie k r X := hu X (by simp)
    obtain ⟨Θ1, hJ1, hE1⟩ := polyOp_word_lemma_6 u (fun Y hY => hu Y (by simp [hY])) Θ n h
    obtain ⟨Θ2, hJ2, hD2⟩ := polyOp_deriv_lemma_10 hX Θ1 (n + u.length) hJ1
    refine ⟨Θ2, ?_, fun F hF g hg => ?_⟩
    · have e : n + (X :: u).length = n + u.length + 1 := by simp [add_assoc]
      rw [e]
      exact hJ2
    · have step : _root_.Formalism.FourierDecayAlt.B.Rw (X :: u) (_root_.Formalism.FourierDecayAlt.B.opApply Θ F) g =
          _root_.Formalism.REAL.RdV X (_root_.Formalism.FourierDecayAlt.B.Rw u (_root_.Formalism.FourierDecayAlt.B.opApply Θ F)) g := rfl
      rw [step, _root_.Formalism.FourierDecayAlt.P.PositiveOrbitOpen.rdV_local isOpen_univ (fun x _ hx => hE1 F hF x hx) hX g (Set.mem_univ g) hg,
        _root_.PI.UnitaryGroupMassFormula.UsCompose.RdV_eq_Dx, _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dx_eq]
      exact (hD2 F hF g hg).deriv

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma exists_polyOp_opApply_eq_smul {κa : ℕ} {Pf : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ} (hP : _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κa Pf) :
    ∀ (Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) (n κ : ℕ), _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n κ Θ → ∃ Θ' : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq,
      _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp n (κa + κ) Θ' ∧ ∀ (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) g,
        _root_.Formalism.FourierDecayAlt.B.opApply Θ' F g = Pf g • _root_.Formalism.FourierDecayAlt.B.opApply Θ F g
  | [], n, κ, _ => ⟨[], polyOp_nil _ _, fun F g => by simp [opApply_nil]⟩
  | T :: Θ, n, κ, h => by
    have hT := h
    unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at hT
    obtain ⟨hlen, Q, hQ, hc, -⟩ := hT T (by simp)
    obtain ⟨Θr, hJr, hEr⟩ := exists_polyOp_opApply_eq_smul hP Θ n κ (polyOp_of_polyOp_cons h)
    refine ⟨_root_.GlobalTheory.HatNF.PolyComp.scalTerm (fun g => Pf g * Q g) T.word T.word_lie :: Θr, ?_,
      fun F g => ?_⟩
    · unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at hJr ⊢
      intro T' hT'
      rcases List.mem_cons.mp hT' with rfl | hT'
      · obtain ⟨p, hp, hPp⟩ := hP
        obtain ⟨q, hq, hQq⟩ := hQ
        exact ⟨hlen, _, ⟨p * q, (totalDegree_mul p q).trans (add_le_add hp hq),
          fun g => by simp [hPp, hQq]⟩, fun _ => rfl, fun _ => rfl⟩
      · exact hJr T' hT'
    · rw [opApply_cons', opApply_cons', hEr F g, hc]
      simp [_root_.GlobalTheory.HatNF.PolyComp.scalTerm, smul_add, mul_smul]

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma opApply_append' (Θ₁ Θ₂ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq)
    (F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (g : _root_.Formalism.FourierDecayAlt.B.Mat k r) :
    _root_.Formalism.FourierDecayAlt.B.opApply (Θ₁ ++ Θ₂) F g = _root_.Formalism.FourierDecayAlt.B.opApply Θ₁ F g + _root_.Formalism.FourierDecayAlt.B.opApply Θ₂ F g := by
  simp [_root_.Formalism.FourierDecayAlt.B.opApply]

open MvPolynomial in
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] {k r : ℕ} in
private lemma polyOp_comp_lemma_2 {o₂ κ₁ κ₂ : ℕ} {Θb : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq} (hb : _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp o₂ κ₂ Θb) :
    ∀ (Θa : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq) (o₁ : ℕ), _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp o₁ κ₁ Θa → ∃ Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp k r Wp Wq,
      _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp (o₁ + o₂) (κ₁ + κ₂) Θ ∧ ∀ F : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp,
        _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) F → ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r,
          _root_.Formalism.FourierDecayAlt.B.opApply Θ F g = _root_.Formalism.FourierDecayAlt.B.opApply Θa (_root_.Formalism.FourierDecayAlt.B.opApply Θb F) g
  | [], o₁, _ => ⟨[], polyOp_nil _ _, fun F _ g _ => by simp [opApply_nil]⟩
  | T :: Θa, o₁, h => by
    have hT := h
    unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at hT
    obtain ⟨hlen, Pf, hP, hc, -⟩ := hT T (by simp)
    obtain ⟨Θr, hJr, hEr⟩ := polyOp_comp_lemma_2 hb Θa o₁ (polyOp_of_polyOp_cons h)
    obtain ⟨Θ1, hJ1, hE1⟩ := polyOp_word_lemma_6 T.word T.word_lie Θb o₂ hb
    obtain ⟨Θ2, hJ2, hE2⟩ := exists_polyOp_opApply_eq_smul hP Θ1 (o₂ + T.word.length) κ₂ hJ1
    refine ⟨Θ2 ++ Θr, ?_, fun F hF g hg => ?_⟩
    · have hJ2' := polyOp_mono' hJ2 (show o₂ + T.word.length ≤ o₁ + o₂ by omega) le_rfl
      unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at hJ2' hJr ⊢
      intro T' hT'
      rcases List.mem_append.mp hT' with hT' | hT'
      exacts [hJ2' T' hT', hJr T' hT']
    · rw [opApply_append', opApply_cons', hE2 F g, ← hE1 F hF g hg, hEr F hF g hg, hc]
      simp

open MeasureTheory in

theorem _root_.GlobalTheory.HatNF.polyLift_closed : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par)
    (Bs : _root_.Formalism.FourierDecayAlt.B.RealPlaceData P.k P.r Wp Wq), _root_.GlobalTheory.HatNF.PolyLift P Bs 0 0 1 ∧
      (∀ o o' κ κ' a, o ≤ o' → κ ≤ κ' → _root_.GlobalTheory.HatNF.PolyLift P Bs o κ a →
        _root_.GlobalTheory.HatNF.PolyLift P Bs o' κ' a) ∧
      ∀ o₁ κ₁ o₂ κ₂ a b, _root_.GlobalTheory.HatNF.PolyLift P Bs o₁ κ₁ a →
        _root_.GlobalTheory.HatNF.PolyLift P Bs o₂ κ₂ b →
        _root_.GlobalTheory.HatNF.PolyLift P Bs (o₁ + o₂) (κ₁ + κ₂) (a * b) := by
  intro Wp Wq _ _ _ _ _ _ P Bs
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨[_root_.GlobalTheory.HatNF.PolyComp.scalTerm (fun _ => 1) [] (by simp)], ?_, ?_⟩
    · intro Tm hTm
      simp only [List.mem_singleton] at hTm
      subst hTm
      refine ⟨by simp [_root_.GlobalTheory.HatNF.PolyComp.scalTerm], fun _ => 1, ?_, fun _ => rfl, fun _ => rfl⟩
      exact ⟨MvPolynomial.C 1, by simp, fun g => by simp⟩
    · intro F _ Φ hΦ
      have hF : _root_.Formalism.FourierDecayAlt.B.opApply [_root_.GlobalTheory.HatNF.PolyComp.scalTerm (Wp := Wp) (Wq := Wq) (fun _ => 1) []
          (by simp)] F = F := by
        funext g
        simp [_root_.Formalism.FourierDecayAlt.B.opApply, _root_.Formalism.FourierDecayAlt.B.Rw, _root_.GlobalTheory.HatNF.PolyComp.scalTerm]
      rw [hF]
      exact hΦ
  · rintro o o' κ κ' a ho hκ ⟨Θ, hΘ, hR⟩
    exact ⟨Θ, polyOp_mono' hΘ ho hκ, hR⟩
  · rintro o₁ κ₁ o₂ κ₂ a b ⟨Θa, hJa, hRa⟩ ⟨Θb, hJb, hRb⟩
    obtain ⟨Θ, hJ, hE⟩ := polyOp_comp_lemma_2 hJb Θa o₁ hJa
    refine ⟨Θ, hJ, ?_⟩
    unfold _root_.Formalism.FourierDecayAlt.TL.RadIs at hRa hRb ⊢
    intro F hF Φ hΦ
    have hsmooth : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) F := by
      unfold _root_.Formalism.FourierDecayAlt.KB.CptCoef at hF
      exact hF.1
    have hsm : _root_.Formalism.FourierDecayAlt.B.SmoothCoef (_root_.Formalism.FourierDecayAlt.C6.domL Bs ∅) Θb :=
      (_root_.GlobalTheory.HatNF.polyOp_ok P.k P.r Wp Wq o₂ κ₂ Θb hJb).1 _
    have h2 := hRa _ (_root_.Formalism.FourierDecayAlt.P.TLB.cpt_op hF hsm) _ (hRb F hF Φ hΦ)
    unfold _root_.Formalism.FourierDecayAlt.Top.IsRadOf at h2 ⊢
    intro x hx
    rw [show (a * b).1 Φ = a.1 (b.1 Φ) from rfl, h2 x hx]
    unfold _root_.Formalism.FourierDecayAlt.Q.resG
    rw [_root_.Formalism.FourierDecayAlt.P.JCx2.sq_jf_congr Bs (fun g hg => (hE F hsmooth g hg).symm) (_root_.Formalism.FourierDecayAlt.P.TLB.wCell_gv Bs hx)]

end GlobalTheory.HatNF
