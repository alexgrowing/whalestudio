import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNaturaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeFiniteProjectiveReflexive
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

open TensorProduct WithConv Coalgebra

namespace GlobalTheory.NMul

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

end GlobalTheory.NMul

namespace GlobalTheory.NMul

theorem ev_nmul : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (n k : ℕ) (i : Fin d),
      c.ev n (nmul c.μ k i) = PDiv.mulBy O (G.A n) k (c.x n i) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c n k
  haveI : IsAdicComplete (Ideal.span {(p : O)}) (G.A n) :=
    GlobalTheory.isAdicComplete_of_finite_projective _ _
  haveI : IsAdicComplete (Ideal.span {(p : G.A n)}) (G.A n) := isAdicComplete_ring_of_module (O := O) p
  have hT := (GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O (G.A n) (Fin d) (c.x n) (c.nil n)).2 (c.ev n) (c.isEval n)
  have hsucc : ∀ (k : ℕ) (j : Fin d), nmul c.μ (k + 1) j =
      subst (Sum.elim (nmul c.μ k) fun i => (X i : MvPowerSeries (Fin d) O)) (c.μ j) := by
    intro k j
    simp only [nmul, Function.iterate_succ_apply']
    rfl
  have hmul : ∀ (j : ℕ) (a : G.A n),
      PDiv.mulBy O (G.A n) j a = (toConv (AlgHom.id O (G.A n)) ^ j).ofConv a := fun j a =>
    DFunLike.congr_fun (PDiv.comp_mulBy_pts (AlgHom.id O (G.A n)) j) a
  induction k with
  | zero =>
    intro i
    have h0 : nmul c.μ 0 i = 0 := rfl
    rw [h0, map_zero, hmul]
    simp [c.aug n i]
  | succ k ih =>
    intro i
    have hu : ∀ s, constantCoeff
        (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) s) = 0 := by
      have hc : ∀ (k : ℕ) (j : Fin d), constantCoeff (nmul c.μ k j) = 0 := by
        intro k
        induction k with
        | zero => intro j; rfl
        | succ k ihk =>
          intro j
          rw [hsucc]
          refine constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero ?_) ?_
            (c.isLaw.const j) <;>
          · rintro (l | l)
            · simpa using ihk l
            · simp
      rintro (l | l)
      · simpa using hc k l
      · simp
    let ψ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] G.A n :=
      (Algebra.TensorProduct.lift (PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
        (AlgHom.id O (G.A n)) fun _ _ => Commute.all _ _).comp (c.ev₂ n)
    have hψ : IsEval p (fun s => c.ev n
        (Sum.elim (nmul c.μ k) (fun i => (X i : MvPowerSeries (Fin d) O)) s)) ψ := by
      constructor
      · rintro (l | l)
        · simp only [ψ, AlgHom.comp_apply, (c.isEval₂ n).1 (Sum.inl l), Sum.elim_inl,
            Algebra.TensorProduct.lift_tmul, map_one, mul_one, ih]
          rfl
        · simp only [ψ, AlgHom.comp_apply, (c.isEval₂ n).1 (Sum.inr l), Sum.elim_inr,
            Algebra.TensorProduct.lift_tmul, map_one, one_mul, (c.isEval n).1 l]
          rfl
      · intro m
        obtain ⟨N, hN⟩ := (c.isEval₂ n).2 m
        refine ⟨N, fun f hf => ?_⟩
        obtain ⟨y, hy⟩ := hN f hf
        refine ⟨(Algebra.TensorProduct.lift (PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n)
          (AlgHom.id O (G.A n)) fun _ _ => Commute.all _ _) y, ?_⟩
        simp only [ψ, AlgHom.comp_apply, hy, map_mul, map_pow, map_natCast]
    rw [hsucc, hT.1 _ _ ψ hu hψ (c.μ i)]
    simp only [ψ, AlgHom.comp_apply, c.comul n i]
    rw [hmul (k + 1), pow_succ, AlgHom.convMul_apply]
    have e : (toConv (AlgHom.id O (G.A n)) ^ k).ofConv =
        (PDiv.mulBy O (G.A n) k : G.A n →ₐ[O] G.A n) := by
      ext a; exact (hmul k a).symm
    simp only [e]

end GlobalTheory.NMul
