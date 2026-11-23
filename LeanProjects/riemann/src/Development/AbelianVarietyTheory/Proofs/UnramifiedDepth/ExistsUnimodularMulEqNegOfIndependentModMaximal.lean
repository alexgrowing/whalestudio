import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLinearIndependentSumElimOfFinrankEq
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory

theorem exists_isUnit_det_mul_eq_neg_of_linearIndependent_residue {R : Type} [CommRing R]
    [IsLocalRing R] (n n0 : ℕ) (Φ : Fin n → Fin n0 → R)
    (h : LinearIndependent (IsLocalRing.ResidueField R)
      (fun (c : Fin n0) (b : Fin n) => IsLocalRing.residue R (Φ b c))) :
    n0 ≤ n ∧ ∃ Y : Matrix (Fin n) (Fin n) R, IsUnit Y.det ∧
      ∀ (b : Fin n) (c : Fin n0), ∑ b', Y b b' * Φ b' c = if b.val = c.val then -1 else 0 := by
  have hle : n0 ≤ n := by simpa using h.fintype_card_le_finrank
  refine ⟨hle, ?_⟩
  obtain ⟨n', rfl⟩ := Nat.exists_eq_add_of_le hle
  obtain ⟨w, hw⟩ := exists_linearIndependent_sumElim_of_finrank_eq (n' := n') (by simp) _ h
  choose s hs using IsLocalRing.residue_surjective (R := R)
  let M : Matrix (Fin (n0 + n')) (Fin (n0 + n')) R := Matrix.of fun i j =>
    Sum.elim (Φ i) (fun j' => s (w j' i)) (finSumFinEquiv.symm j)
  have hcol : (M.map (IsLocalRing.residue R)).col =
      Sum.elim (fun (c : Fin n0) (b : Fin (n0 + n')) => IsLocalRing.residue R (Φ b c)) w ∘
        finSumFinEquiv.symm := by
    funext j i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    rcases j with j | j
    · simp [M, Matrix.col]
    · simp [M, Matrix.col, hs]
  have hu : IsUnit (M.map (IsLocalRing.residue R)) := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit, hcol]
    exact hw.comp _ finSumFinEquiv.symm.injective
  have hdet : IsUnit M.det := by
    rw [Matrix.isUnit_iff_isUnit_det] at hu
    have : (M.map (IsLocalRing.residue R)).det = IsLocalRing.residue R M.det :=
      (RingHom.map_det (IsLocalRing.residue R) M).symm
    rw [this] at hu
    exact (isUnit_map_iff (IsLocalRing.residue R) _).mp hu
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hdet
  refine ⟨-M⁻¹, ?_, ?_⟩
  · rw [← Matrix.isUnit_iff_isUnit_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_nonsing_inv_det M hdet)).neg
  · intro b c
    have hij : ∑ b', M⁻¹ b b' * Φ b' c = (M⁻¹ * M) b (Fin.castAdd n' c) := by
      simp [M, Matrix.mul_apply]
    simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]
    rw [hij, hinv, Matrix.one_apply]
    by_cases hbc : b.val = c.val
    · rw [if_pos hbc, if_pos (Fin.ext hbc)]
    · rw [if_neg hbc, if_neg (fun e => hbc (by rw [e]; rfl)), neg_zero]

theorem exists_unimodular_mul_eq_neg_of_indepMod : ∀ (C : Type) [Field C] (V : VF C) (n n0 : ℕ) (Φ : Fin n → Fin n0 → C), (∀ b c, V.Ge 0 (Φ b c)) → IndepMod V (fun c b => Φ b c) → n0 ≤ n ∧ ∃ Y : Matrix (Fin n) (Fin n) C, (∀ b b', V.Ge 0 (Y b b')) ∧ V.v Y.det = 0 ∧ ∀ (b : Fin n) (c : Fin n0), b.val < n0 → ∑ b', Y b b' * Φ b' c = if b.val = c.val then -1 else 0 := by
  intro C _ V n n0 Φ hΦ hind
  let O : ValuationSubring C := (AddValuation.toValuation V.v).valuationSubring
  have hmem : ∀ x : C, x ∈ O ↔ 0 ≤ V.v x := fun _ => Iff.rfl
  have hge : ∀ x : C, V.Ge 0 x ↔ 0 ≤ V.v x := fun _ => Iff.rfl
  have hunit : ∀ x : O, IsUnit x ↔ V.v (x : C) = 0 := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hx.exists_right_inv
      have h1 : V.v (x : C) + V.v (y : C) = 0 := by
        rw [← V.v.map_mul, ← V.v.map_one]
        exact congrArg (fun z : O => V.v (z : C)) hy
      have h2 := (hmem _).1 x.2
      have h3 := (hmem _).1 y.2
      exact le_antisymm (by
        calc V.v (x : C) = V.v (x : C) + 0 := (add_zero _).symm
          _ ≤ V.v (x : C) + V.v (y : C) := by gcongr
          _ = 0 := h1) h2
    · intro hx
      have hx0 : (x : C) ≠ 0 := by
        intro h0
        rw [h0, V.v.map_zero] at hx
        exact WithTop.top_ne_zero hx
      have h1 : V.v (x : C)⁻¹ = 0 := by
        have := V.v.map_mul (x : C) (x : C)⁻¹
        rw [mul_inv_cancel₀ hx0, V.v.map_one, hx, zero_add] at this
        exact this.symm
      exact IsUnit.of_mul_eq_one (⟨(x : C)⁻¹, (hmem _).2 h1.ge⟩ : O)
        (Subtype.ext (mul_inv_cancel₀ hx0))
  have hres : ∀ x : O, IsLocalRing.residue O x = 0 ↔ V.MM (x : C) := by
    intro x
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunit]
    exact ⟨fun h => lt_of_le_of_ne ((hmem _).1 x.2) (Ne.symm h), fun h => ne_of_gt h⟩
  let Ψ : Fin n → Fin n0 → O := fun b c => ⟨Φ b c, (hmem _).2 ((hge _).1 (hΦ b c))⟩
  have hli : LinearIndependent (IsLocalRing.ResidueField O)
      (fun (c : Fin n0) (b : Fin n) => IsLocalRing.residue O (Ψ b c)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg ν
    choose s hs using IsLocalRing.residue_surjective (R := O)
    rw [← hs (g ν), hres]
    refine hind (fun ν => (s (g ν) : C)) (fun ν => (hge _).2 ((hmem _).1 (s (g ν)).2)) (fun x => ?_) ν
    have h1 : IsLocalRing.residue O (∑ ν, s (g ν) * Ψ x ν) = 0 := by
      have := congrFun hg x
      simpa [hs, Finset.sum_apply] using this
    rw [hres] at h1
    simpa [Ψ] using h1
  obtain ⟨hle, Y, hY, hYΦ⟩ := exists_isUnit_det_mul_eq_neg_of_linearIndependent_residue n n0 Ψ hli
  refine ⟨hle, Y.map O.subtype, fun b b' => (hge _).2 ((hmem _).1 (Y b b').2), ?_, fun b c _ => ?_⟩
  · have : (Y.map O.subtype).det = O.subtype Y.det := (RingHom.map_det O.subtype Y).symm
    rw [this]
    exact (hunit _).1 hY
  · have := congrArg O.subtype (hYΦ b c)
    rw [map_sum] at this
    simp only [map_mul, apply_ite O.subtype, map_neg, map_one, map_zero] at this
    exact this

end GlobalTheory
