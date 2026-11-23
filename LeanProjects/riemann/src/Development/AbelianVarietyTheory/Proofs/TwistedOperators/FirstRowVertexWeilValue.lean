import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowMapVUpdateZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionSchrodingerModelFiniteIdempotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EdgeFactorNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowArgumentConjugateMoveLeftMulInvComponentStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedTensorEigenvalueLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FirstRowTermLaw

theorem law_gen {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T} (ht : t ∈ U) {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ}
    (hτ : S.IsExpansion t Φ β τ) (k : FinPt G (.grid 0 D.R.m)) (lam : locPl G t → ℂ)
    (hlam : ∀ w : locPl G t, (locGrid G t w).pathAct .one (GlobalTheory.SplitFlip.oppositePath D.R.m)
      (Pi.mulSingle (0, D.R.m) (kapAt S t w k)) (Tflip W S.B t Φ w) = lam w • Tflip W S.B t Φ w)
    (s : ℂ) (hs : s * ∏ w, lam w = ∏ w : locPl G t, (locGrid G t w).edgeFactor .one (Pi.mulSingle (0, D.R.m) (kapAt S t w k)) (.ex 0 D.R.m))
    (xs : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)))
    (ys : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :
    s * (τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))) i)) =
      τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (ys i) := by
  obtain ⟨e, he, hsupp, hexp⟩ := hτ
  have hm : D.R.m ≠ 0 := by have := D.R.two_le_m; omega
  by_cases hh : (∀ j, IsHalf e (xs j)) ∧ ∀ i, IsHalf e (ys i)
  · have hh' : ∀ i, IsHalf e (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))) i) := by
      intro i
      by_cases h : i = (GlobalTheory.FirstRowVertex.firstIx D)
      · subst h; rw [Function.update_self]; exact (GlobalTheory.SchrMove.isHalf_actO_iff _ _ _).2 (hh.2 _)
      · rw [Function.update_of_ne h]; exact hh.2 i
    rw [hexp xs _ hh.1 hh', hexp xs ys hh.1 hh.2]
    have hloc : ∀ w : locPl G t, (locGrid G t w).edgeFactor .one (Pi.mulSingle (0, D.R.m) (kapAt S t w k)) (.ex 0 D.R.m) *
        (S.term t Φ β w).datum (S.colAt t w xs) (S.rowAt t w (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))))) =
        lam w * (S.term t Φ β w).datum (S.colAt t w xs) (S.rowAt t w ys) := by
      intro w
      rw [GlobalTheory.T.firstRowArgument_conjugateMove_left_mul_inv_component S ht w w.2 k ys]
      exact GlobalTheory.FirstRowTermLaw.datum_law (Γ := locGrid G t w) one_le_sLen hm _ _ _ _ _ _ _ _ (hlam w) _ _
    have hprod := Finset.prod_congr rfl fun w (_ : w ∈ Finset.univ) => hloc w
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib] at hprod
    exact key_cancel _ _ _ _ _ (Finset.prod_ne_zero_iff.2 fun w _ => edgeFactor_ne_zero _ _ _) hs hprod
  · have hz : ∀ d ∈ τ.support, (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (ys i) = 0 ∧
        (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))) i) = 0 := by
      intro d hd
      have hX : ∀ j, (d.1 j).fn (xs j) ≠ 0 → IsHalf e (xs j) := fun j h => ((hsupp d hd).1 j).2.1 ▸ (d.1 j).sb.1 _ h
      have hY : ∀ i y, (d.2 i).fn y ≠ 0 → IsHalf e y := fun i y h => ((hsupp d hd).2 i).2.1 ▸ (d.2 i).sb.1 _ h
      by_cases hx : ∀ j, IsHalf e (xs j)
      · obtain ⟨i, hi⟩ : ∃ i, ¬ IsHalf e (ys i) := by
          by_contra hc; push_neg at hc; exact hh ⟨hx, hc⟩
        have h1 : (d.2 i).fn (ys i) = 0 := by by_contra h; exact hi (hY i _ h)
        have h2 : (d.2 i).fn (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))) i) = 0 := by
          by_contra h
          have h' := hY i _ h
          by_cases hi0 : i = (GlobalTheory.FirstRowVertex.firstIx D)
          · subst hi0; rw [Function.update_self] at h'; exact hi ((GlobalTheory.SchrMove.isHalf_actO_iff _ _ _).1 h')
          · rw [Function.update_of_ne hi0] at h'; exact hi h'
        exact ⟨by rw [show (∏ i, (d.2 i).fn (ys i)) = 0 from Finset.prod_eq_zero (Finset.mem_univ i) h1, mul_zero],
          by rw [show (∏ i, (d.2 i).fn (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))) i)) = 0 from
            Finset.prod_eq_zero (Finset.mem_univ i) h2, mul_zero]⟩
      · push_neg at hx
        obtain ⟨j, hj⟩ := hx
        have h1 : (d.1 j).fn (xs j) = 0 := by by_contra h; exact hj (hX j h)
        rw [show (∏ j, (d.1 j).fn (xs j)) = 0 from Finset.prod_eq_zero (Finset.mem_univ j) h1]
        simp only [zero_mul, and_self]
    simp only [Finsupp.sum]
    rw [Finset.sum_eq_zero fun d hd => by rw [mul_assoc, (hz d hd).2, mul_zero],
      Finset.sum_eq_zero fun d hd => by rw [mul_assoc, (hz d hd).1, mul_zero], mul_zero]

end GlobalTheory.FirstRowTermLaw

namespace GlobalTheory.FirstRowTermLaw

set_option maxHeartbeats 1000000 in

theorem main : GlobalTheory.FunPr.Hypotheses₂ → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) (c : ℂ),
      ch.W.om (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1) (ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) = c • ch.S.Z.vac (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) →
    ∀ (xs : ∀ j : Fin D.R.m, WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)))
      (ys : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))),
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) * c *
        (τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) *
          ∏ i, Function.update (fun i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D)
            (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn (actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ y)) i (ys i)) =
      τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (ys i) := by
  intro hP hS
  obtain ⟨a₁, h₁⟩ := GlobalTheory.T.first_vertex_weil_scalar hP hS
  refine ⟨a₁, fun ε CF hC => ?_⟩
  obtain ⟨x₁, hc₁⟩ := h₁ ε CF hC
  refine ⟨x₁, ?_⟩
  intro D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc t a β hβ τ hτ k hkl hk c hc xs ys
  obtain ⟨lam, hlam, hscal⟩ := hc₁ D large₂ e hx Γ Pl0 T A Ks R F s ch hi hsc t a k hkl hk c hc
  have hL : (τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) *
      ∏ i, Function.update (fun i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D) (fun y => (d.2 (GlobalTheory.FirstRowVertex.firstIx D)).fn ((actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) y)) i (ys i)) =
      τ.sum fun d a' => a' * (∏ j, (d.1 j).fn (xs j)) * ∏ i, (d.2 i).fn (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) ((actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) (ys (GlobalTheory.FirstRowVertex.firstIx D))) i) :=
    sum_update_comp τ (fun d j => (d.1 j).fn) (fun d i => (d.2 i).fn) (GlobalTheory.FirstRowVertex.firstIx D) (actO (ch.G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).1⁻¹ (ch.G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((ch.S.N.u (.grid 0 D.R.m))⁻¹ * k * ch.S.N.u (.grid 0 D.R.m)).1 1).2⁻¹) xs ys
  rw [hL]
  exact law_gen ch.S.toGridChoice (Set.mem_univ t) hτ k lam hlam _ hscal xs ys

end GlobalTheory.FirstRowTermLaw

end
