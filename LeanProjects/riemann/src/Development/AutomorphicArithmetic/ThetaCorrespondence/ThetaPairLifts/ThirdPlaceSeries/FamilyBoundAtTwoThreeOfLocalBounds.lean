import Development.AutomorphicArithmetic.ResidueCharacters.FamilyBoundAtTwoThreeOfLocalBounds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRowOn
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace UpperTheory.N
theorem mid_of_rowOn_alt (Q : D7 → ℕ → Prop)
    (hQ : ∀ D l, l.Prime → Q D l → D.host.condN.factorization l = D.host.QS.factorization l)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (h : _root_.UpperTheory.N.RowOnAlt Q A B) {eps : ℝ} (Fm : FamP eps) :
    ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x)
      (HW : HWOf (Fm.D x i).loc) (F : FonOf (Fm.D x i).loc (Fm.D x i).locA HW)
      (_ : CmpOf (Fm.D x i).loc (Fm.D x i).locA HW F) (X : KillingConditions.HubData (Fm.D x i)) (C₂ : ℝ),
      _root_.GlobalTheory.NLink.SetupAlt (Fm.L x i) (Fm.ex x hx i).nch HW X C₂ → ∀ k, TwistedPlaces.TwLoc (Fm.D x i) k → Q (Fm.D x i) ((Fm.D x i).nd.l k) →
        ∀ π ∈ (Fm.D x i).nd.Zgood k, Bd X.ρ k π (midF (Fm.L x i) C) := by
  obtain ⟨x0, h0⟩ := h Fm
  obtain ⟨C0, x1, hC0, hpar⟩ := GlobalTheory.T.admissible_parameters_family_const Fm
  refine ⟨18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1, max 3 (max x0 x1), ?_,
    fun x hxx hx i HW F Cm X C₂ hS k hTw hq π hπ => ?_⟩
  · have : 0 ≤ C0 := by linarith
    positivity
  have h3 : 3 ≤ x := (le_max_left _ _).trans hxx
  have hb := h0 x (((le_max_left _ _).trans (le_max_right _ _)).trans hxx) hx i HW F Cm X C₂ hS k hTw hq π hπ
  obtain ⟨-, -, -, hn, ht, -⟩ := hpar x (((le_max_right _ _).trans (le_max_right _ _)).trans hxx) hx i
  have hlog : 1 ≤ Real.log (Fm.L x i).sc.x := by
    rw [Fm.L_x x i hx, Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hl : ((Fm.D x i).nd.l k).Prime := ((Fm.D x i).nd.lPrime k).out
  have hc : costC (Fm.L x i) A B ((Fm.D x i).nd.l k) ≤
      midF (Fm.L x i) (18 * A * C0 + 2 * B * (3 * C0 + 9) + 5 * C0 + 1) :=
    Num.cost_le' (Fm.L x i) (Fm.params x hx i) hA hB hC0 hlog hn ht hl (hQ _ _ hl hq) le_rfl
  unfold Bd at hb ⊢
  linarith
theorem boundAtTwoThree_of_local_bounds_at_two_three (h3qd : ∀ D : D7, 3 ≠ D.host.q ∧ 3 ≠ D.host.d)
    (h2 : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ _root_.UpperTheory.N.SecondBoundCondition A B) (h3 : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ _root_.UpperTheory.N.ThirdBoundCondition A B)
    {eps : ℝ} (Fm : FamP eps) : _root_.GlobalTheory.NLink.BoundAtTwoThreeFamilyFonAlt Fm := by
  obtain ⟨A, B, hA, hB, h2⟩ := h2
  obtain ⟨A', B', hA', hB', h3⟩ := h3
  obtain ⟨C, x0, hC, h2⟩ := _root_.UpperTheory.N.mid_of_rowOn_alt (fun _ l => l = 2) (fun D l _ (e : l = 2) =>
    Num.factorization_condN D (by rw [e]; exact UpperTheory.Small.two_mem D.host)) A B hA hB (fun Fm => h2 Fm) Fm
  obtain ⟨C', x1, hC', h3⟩ := _root_.UpperTheory.N.mid_of_rowOn_alt (fun D l => l = 3 ∧ l ∉ D.host.small) (fun D l _ (e : l = 3 ∧ l ∉ D.host.small) =>
    Num.factorization_condN' D (by rw [e.1]; exact (h3qd D).1) (by rw [e.1]; exact (h3qd D).2)) A' B' hA' hB' (fun Fm => h3 Fm) Fm
  refine ⟨max C C', max x0 x1, fun x hxx hx i HW F Cm X C₂ hS k hTw hl π hπ => ?_⟩
  have h0 : 0 ≤ max C C' := hC.trans (le_max_left _ _)
  rcases hl with hl | hl
  · have h := h2 x ((le_max_left _ _).trans hxx) hx i HW F Cm X C₂ hS k hTw hl π hπ
    have h' := midF_mono (Fm.L x i) (le_max_left C C') h0
    unfold Bd at h ⊢; linarith
  · have h := h3 x ((le_max_right _ _).trans hxx) hx i HW F Cm X C₂ hS k hTw hl π hπ
    have h' := midF_mono (Fm.L x i) (le_max_right C C') h0
    unfold Bd at h ⊢; linarith
end UpperTheory.N
end
