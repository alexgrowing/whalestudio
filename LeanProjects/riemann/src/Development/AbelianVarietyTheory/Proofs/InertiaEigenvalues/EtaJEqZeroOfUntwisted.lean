import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalFormLengthEqDefiniteFamilyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLocalCongruenceLengthEqRationalLengthStatement
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

namespace GlobalTheory

theorem etaJ_eq_zero_of_untwisted (D : D7) (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (hw : D.what₂.muAt w = D.what₂.mu0) : D.what₂.etaJ j w = 0 := by
  rw [D.etaJ_tie j w h1 h2]
  refine Finset.sum_eq_zero fun i hi => ?_
  exact absurd (by rw [((D.nd.locs_mem j w i).1 hi).2]; exact hw) (D.nd.w_tw i)

theorem etaJ_join : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → m ≤ D.R.m → ∀ (S0 : IndefData (A.side P ψ Zs)) (M : MtFam D) (Tn : NormalizedLocalCompatibility D M), TupTie D A S0 tup → (∀ y, y ∈ S0.Tw ↔ S0.μ y ≠ A.μ0) → (∀ (i : Fin m), ∀ y ∈ S0.Tw, FormsTie D.what₂.embLL ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lH D A P ψ i (S0.μ y)) (lE D A P ψ i (S0.μ y)) (D.what₂.eMt (tup (S0.μ y)) ((i : ℕ) + 1)) ∧ OLatTie D.what₂.embLL (D.what₂.MtLat (tup (S0.μ y)) ((i : ℕ) + 1)) ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lNab D A P ψ i (S0.μ y)) ∧ Idx.Z0 D (tup (S0.μ y)) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)) (eMt i (S0.μ y) ((lZ0 D A P ψ Zs i (S0.μ y)).mulVec (Pi.single k 1))))) → HeckeStdTw Tn.B → (∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → LatStable Tn.B j w) → (∀ i, SpecPr D i) → ∀ (i : Fin m) w, D.what₂.etaJ ((i : ℕ) + 1) w = @ite _ (D.plEq w ∈ S0.Tw) (Classical.propDecidable _) (A.fam.etaJ P ψ Zs i (S0.μ (D.plEq w)) (D.plEq w)) 0 := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk hm S0 M Tn hTup hTw hMt hH hLat hSpec i w
  have hj1 : 1 ≤ (i : ℕ) + 1 := Nat.le_add_left _ _
  have hj2 : (i : ℕ) + 1 ≤ D.R.m := Nat.lt_of_lt_of_le i.2 hm
  by_cases h : D.plEq w ∈ S0.Tw
  · rw [if_pos h]
    have hne : D.what₂.muAt w ≠ D.what₂.mu0 := by
      rw [hTup.muAt w, ← hTup.mu0]
      exact fun e => (hTw _).1 h (hTup.inj e)
    have htw : D.what₂.muTw w = tup (S0.μ (D.plEq w)) :=
      ((D.what₂.muAt_or w).resolve_left hne).symm.trans (hTup.muAt w)
    obtain ⟨hM1, hM2, hM3⟩ := hMt i _ h
    obtain ⟨hZ, hE⟩ := GlobalTheory.T.rationalFormLength_eq_definiteFamily D G Pl0 T m A P ψ Zs tup eMt s hOk i (S0.μ (D.plEq w)) hM1 hM2 hM3
    rw [GlobalTheory.T.sum_localCongruenceLength_eq_rationalLength D M Tn ((i : ℕ) + 1) w hj1 hj2 hne hH (hLat _ w hj1 hj2 hne) (htw ▸ hZ)
      (fun i' _ => hSpec i'), htw]
    exact hE w
  · rw [if_neg h]
    refine etaJ_eq_zero_of_untwisted D _ w hj1 hj2 ?_
    rw [hTup.muAt w, ← hTup.mu0]
    congr 1
    by_contra hn
    exact h ((hTw _).2 hn)

end GlobalTheory
