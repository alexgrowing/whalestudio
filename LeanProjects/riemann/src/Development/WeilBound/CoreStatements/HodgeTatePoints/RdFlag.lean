import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.WeilBound.CoreStatements.HodgeTatePoints.RdChain

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rd

theorem prod_ext {n : ℕ} (s : Fin n → NNReal) :
    ∏ i ∈ Finset.range n, (fun i => if h : i < n then s ⟨i, h⟩ else 1) i = ∏ i, s i := by
  rw [Finset.prod_range]
  simp

theorem prod_ext_min {n : ℕ} (s : Fin n → NNReal) (j : ℕ) :
    ∏ i ∈ Finset.range (min j n), (fun i => if h : i < n then s ⟨i, h⟩ else 1) i =
      ∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), s i := by
  have key : Finset.range (min j n) = (Finset.range n).filter (fun i => i < j) := by
    ext i
    simp only [Finset.mem_range, Finset.mem_filter, lt_min_iff]
    tauto
  rw [key, Finset.prod_filter, Finset.prod_filter,
    ← Fin.prod_univ_eq_prod_range (fun i => if i < j then (if h : i < n then s ⟨i, h⟩ else 1) else 1) n]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp

theorem flag_om_of (hex : type_of% @GlobalTheory.T.teichmuller_character_exists) (hsq : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_restriction)
    (hsplit : type_of% @GlobalTheory.T.stable_hopf_order_fundamental_ideal) (hos : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_characters) : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal) (r : NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) r → ∏ i, s i ≤ r := by
  intro p _ C _ _ _ v R _ _ hR hp F _ _ _ _ f hcard N _ _ _ _ AA hst n b χ s r hs hr
  have key := chain_le hex hsq hsplit hos p C v R hR hp F f hcard χ n N AA hst (flagSub b)
    (fun i => if h : i < n then b ⟨i, h⟩ else 0) (isChain_flag b)
    (fun i => if h : i < n then s ⟨i, h⟩ else 1) r
    (by
      intro i hi
      have e1 : (if h : i < n then b ⟨i, h⟩ else 0) = b ⟨i, hi⟩ := dif_pos hi
      have e2 : (if h : i < n then s ⟨i, h⟩ else 1) = s ⟨i, hi⟩ := dif_pos hi
      show HasLen v R (OmType (stepOrder AA.carrier (flagSub b i)
        (if h : i < n then b ⟨i, h⟩ else 0)) χ) (if h : i < n then s ⟨i, h⟩ else 1)
      rw [e1, e2]
      exact hs ⟨i, hi⟩) hr
  rwa [prod_ext] at key

theorem gr_partial_of (hex : type_of% @GlobalTheory.T.teichmuller_character_exists) (hsq : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_restriction)
    (hstep : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_translation) (hsplit : type_of% @GlobalTheory.T.stable_hopf_order_fundamental_ideal)
    (hos : type_of% @GlobalTheory.T.stable_hopf_order_subgroup_characters) : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∀ (χ : MulChar F R) (s : Fin n → NNReal), (∀ i : Fin n, HasLen v R (OmType (stepOrder AA.carrier (flagSub b i) (b i)) χ) (s i)) → HasLen v R (OmType AA.carrier χ) (∏ i, s i) → ∀ j : ℕ, HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : flagSub b j → N))) χ) (∏ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < j), s i) := by
  intro p _ C _ _ _ v R _ _ hR hp F _ _ _ _ f hcard N _ _ _ _ AA hst n b χ s hs hr j
  have key := chain_partial hex hsq hsplit hos p C v R hR hp F f hcard hstep χ n N AA hst (flagSub b)
    (fun i => if h : i < n then b ⟨i, h⟩ else 0) (isChain_flag b)
    (fun i => if h : i < n then s ⟨i, h⟩ else 1)
    (by
      intro i hi
      have e1 : (if h : i < n then b ⟨i, h⟩ else 0) = b ⟨i, hi⟩ := dif_pos hi
      have e2 : (if h : i < n then s ⟨i, h⟩ else 1) = s ⟨i, hi⟩ := dif_pos hi
      show HasLen v R (OmType (stepOrder AA.carrier (flagSub b i)
        (if h : i < n then b ⟨i, h⟩ else 0)) χ) (if h : i < n then s ⟨i, h⟩ else 1)
      rw [e1, e2]
      exact hs ⟨i, hi⟩)
    (by rwa [prod_ext]) j
  rwa [prod_ext_min] at key

end PositivityTheory.HtPt.Rd
