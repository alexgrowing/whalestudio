import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupFormalChartEvNatMultipleEqConvPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeFiniteProjectiveReflexive
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EvP

theorem isAdicComplete_ring_of_module {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (p : ℕ) [h : IsAdicComplete (Ideal.span {(p : O)}) A] :
    IsAdicComplete (Ideal.span {(p : A)}) A := by
  have key : ∀ (n : ℕ) (x : A), x ∈ (Ideal.span {(p : A)} ^ n • ⊤ : Submodule A A) ↔
      x ∈ (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O A) := by
    intro n x
    rw [GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists, GlobalTheory.mem_span_singleton_pow_smul_top_iff_exists]
    simp [Algebra.smul_def]
  exact
    { haus' := fun x hx => IsHausdorff.haus h.toIsHausdorff x fun n =>
        SModEq.sub_mem.2 ((key n _).1 (SModEq.sub_mem.1 (hx n)))
      prec' := fun f hf => by
        obtain ⟨L, hL⟩ := IsPrecomplete.prec h.toIsPrecomplete (f := f) fun {m n} hmn =>
          SModEq.sub_mem.2 ((key _ _).1 (SModEq.sub_mem.1 (hf hmn)))
        exact ⟨L, fun n => SModEq.sub_mem.2 ((key _ _).2 (SModEq.sub_mem.1 (hL n)))⟩ }

theorem constantCoeff_nmul {O : Type} [CommRing O] {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O) (hμ : ∀ j, constantCoeff (μ j) = 0) :
    ∀ (k : ℕ) (j : Fin d), constantCoeff (nmul μ k j) = 0 := by
  intro k
  induction k with
  | zero => intro j; rfl
  | succ k ihk =>
    intro j
    have hsucc : nmul μ (k + 1) j =
        subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) O)) (μ j) := by
      simp only [nmul, Function.iterate_succ_apply']
      rfl
    rw [hsucc]
    refine constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ?_) ?_ (hμ j) <;>
    · rintro (l | l)
      · simpa using ihk l
      · simp

theorem ev_subst_nmul_p : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (n : ℕ) (s : MvPowerSeries (Fin d) O), c.ev (n + 1) (subst (nmul c.μ p) s) = G.mulP n (c.ev n s) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c n s
  haveI : IsAdicComplete (Ideal.span {(p : O)}) (G.A (n + 1)) :=
    GlobalTheory.isAdicComplete_of_finite_projective _ _
  haveI : IsAdicComplete (Ideal.span {(p : G.A (n + 1))}) (G.A (n + 1)) :=
    isAdicComplete_ring_of_module (O := O) p
  have hT := (GlobalTheory.CEval.continuous_eval p O (G.A (n + 1)) (Fin d) (c.x (n + 1)) (c.nil (n + 1))).2
    (c.ev (n + 1)) (c.isEval (n + 1))
  let E' : MvPowerSeries (Fin d) O →ₐ[O] G.A (n + 1) :=
    (G.mulP n : G.A n →ₐ[O] G.A (n + 1)).comp (c.ev n)
  have hu : ∀ j, constantCoeff (nmul c.μ p j) = 0 :=
    constantCoeff_nmul c.μ (fun j => c.isLaw.const j) p
  have hE' : IsEval p (fun j => c.ev (n + 1) (nmul c.μ p j)) E' := by
    constructor
    · intro j
      show G.mulP n (c.ev n (X j)) = c.ev (n + 1) (nmul c.μ p j)
      rw [(c.isEval n).1 j, GlobalTheory.T.pDivGroupFormalChart_ev_natMultiple_eq_convPower p C v O hv G d c (n + 1) p j, ← c.res n j, mulP_res]
    · intro m
      obtain ⟨N, hN⟩ := (c.isEval n).2 m
      refine ⟨N, fun f hf => ?_⟩
      have := map_dvd (G.mulP n : G.A n →ₐ[O] G.A (n + 1)) (hN f hf)
      rwa [map_pow, map_natCast] at this
  exact hT.1 (Fin d) (nmul c.μ p) E' hu hE' s

end GlobalTheory.EvP
