import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnipVal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InCellIffDetNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianSplitUnitaryLowerBlockInvertibleStatement

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem finite_det_line_zero {F E : Type} [Field F] [Field E] [Algebra F E] {ν : Type} [Fintype ν] [DecidableEq ν]
    (A B : Matrix ν ν E) (r₀ : F) (h : (A + algebraMap F E r₀ • B).det ≠ 0) :
    {r : F | (A + algebraMap F E r • B).det = 0}.Finite := by
  set M : Matrix ν ν (Polynomial E) := A.map Polynomial.C + (Polynomial.X : Polynomial E) • B.map Polynomial.C with hM
  have hev : ∀ x : E, M.det.eval x = (A + x • B).det := by
    intro x
    have h1 := RingHom.map_det (Polynomial.evalRingHom x) M
    rw [Polynomial.coe_evalRingHom] at h1
    rw [h1]
    congr 1
    ext i j
    simp [hM]
    ring
  have hp : M.det ≠ 0 := by
    intro h0
    apply h
    rw [← hev, h0, Polynomial.eval_zero]
  have hfin := Polynomial.finite_setOfPred_isRoot hp
  refine (hfin.preimage (f := algebraMap F E) (algebraMap F E).injective.injOn).subset ?_
  intro r hr
  change M.det.eval _ = 0
  rw [hev]
  exact hr

theorem exists_herm_transversal (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E)
    (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (s : Finset (UG c (stdJ ν E))) :
    ∃ t : Matrix ν ν E, (t.map c)ᵀ = t ∧ ∀ g ∈ s, ((mat c g).toBlocks₂₁ + (mat c g).toBlocks₂₂ * t).det ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by ext i j; simp, by simp⟩
  | insert g s _ ih =>
    obtain ⟨t₀, ht₀, h₀⟩ := ih
    obtain ⟨t₁, ht₁, h₁⟩ := GlobalTheory.T.exists_hermitian_splitUnitary_lowerBlock_invertible F E c δ hE ν g
    have key : ∀ k ∈ insert g s, {r : F | (((mat c k).toBlocks₂₁ + (mat c k).toBlocks₂₂ * t₀) +
        algebraMap F E r • ((mat c k).toBlocks₂₂ * (t₁ - t₀))).det = 0}.Finite := by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · refine finite_det_line_zero _ _ 1 ?_
        rw [map_one, one_smul, add_assoc, ← Matrix.mul_add, add_sub_cancel]
        exact h₁
      · refine finite_det_line_zero _ _ 0 ?_
        rw [map_zero, zero_smul, add_zero]
        exact h₀ k hk
    have hfin := Set.Finite.biUnion (insert g s).finite_toSet key
    obtain ⟨r, hr⟩ := hfin.exists_notMem
    refine ⟨t₀ + algebraMap F E r • (t₁ - t₀), ?_, ?_⟩
    · ext i j
      have e₀ : c (t₀ j i) = t₀ i j := congrFun (congrFun ht₀ i) j
      have e₁ : c (t₁ j i) = t₁ i j := congrFun (congrFun ht₁ i) j
      simp [e₀, e₁]
    · intro k hk h0
      apply hr
      refine Set.mem_biUnion (Finset.mem_coe.mpr hk) ?_
      rw [Matrix.mul_add, Matrix.mul_smul, ← add_assoc] at h0
      exact h0

theorem exists_translate_inCell : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E]
    (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (s : Finset (UG c (stdJ ν E))),
    ∃ u : UG c (stdJ ν E), ∀ g ∈ s, InCell c (g * u) := by
  intro F _ _ E _ _ c δ hE ν _ _ s
  obtain ⟨t, ht, h⟩ := exists_herm_transversal F E c δ hE ν s
  let u : UG c (stdJ ν E) :=
    ⟨⟨fromBlocks 1 0 t 1, fromBlocks 1 0 (-t) 1, by simp [fromBlocks_multiply], by simp [fromBlocks_multiply]⟩, by
      rw [mem_UG_iff]
      have h0 : (0 : Matrix ν ν E).map c = 0 := Matrix.map_zero _ (map_zero c)
      have h1 : (1 : Matrix ν ν E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
      simp [stdJ, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, h0, h1, ht]⟩
  refine ⟨u, fun g hg => (GlobalTheory.T.inCell_iff_det_lower_left_block_ne_zero F E c δ hE ν _).mpr ?_⟩
  have e : mat c (g * u) = mat c g * fromBlocks 1 0 t 1 := rfl
  rw [e, ← fromBlocks_toBlocks (mat c g), fromBlocks_multiply, toBlocks_fromBlocks₂₁, Matrix.mul_one]
  exact h g hg

end GlobalTheory.KSp
