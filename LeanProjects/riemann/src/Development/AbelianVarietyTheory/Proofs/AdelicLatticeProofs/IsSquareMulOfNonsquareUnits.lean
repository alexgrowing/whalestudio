import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSquareOfValuedSubOneLt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
open NumberField IsDedekindDomain GlobalTheory.QNorm IsLocalRing
open scoped WithZero

namespace GlobalTheory.QNorm

open NumberField IsDedekindDomain IsLocalRing in
open scoped WithZero in

theorem _root_.GlobalTheory.QNorm.isSquare_of_isSquare_residue_odd (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (h2 : Valued.v (2 : v.adicCompletion F) = 1)
    (z : v.adicCompletionIntegers F) (hz : Valued.v (z : v.adicCompletion F) = 1)
    (h : IsSquare (residue (v.adicCompletionIntegers F) z)) :
    IsSquare (z : v.adicCompletion F) := by
  obtain ⟨r, hr⟩ := h
  obtain ⟨w, rfl⟩ := residue_surjective r
  have hmem : z - w * w ∈ maximalIdeal (v.adicCompletionIntegers F) := by
    rw [← residue_eq_zero_iff, map_sub, map_mul, hr, sub_self]
  have hlt : Valued.v ((z : v.adicCompletion F) - w * w) < 1 := by
    have hnu : ¬ IsUnit (z - w * w) := hmem
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hnu
    have hle := ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 (z - w * w).2)
    push_cast at hnu hle
    exact lt_of_le_of_ne hle hnu
  have hw : Valued.v (w : v.adicCompletion F) = 1 := by
    by_contra hne
    have hwle := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).1 w.2
    have hw1 : Valued.v (w : v.adicCompletion F) < 1 := lt_of_le_of_ne hwle hne
    have : Valued.v (z : v.adicCompletion F) < 1 := by
      have hsplit : (z : v.adicCompletion F) = ((z : v.adicCompletion F) - w * w) + w * w := by ring
      rw [hsplit]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hlt ?_)
      rw [map_mul]
      calc Valued.v (w : v.adicCompletion F) * Valued.v (w : v.adicCompletion F)
          ≤ 1 * Valued.v (w : v.adicCompletion F) := by gcongr
        _ < 1 := by rw [one_mul]; exact hw1
    rw [hz] at this
    exact lt_irrefl _ this
  have hw0 : (w : v.adicCompletion F) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hw; exact zero_ne_one hw
  have h4 : Valued.v (4 : v.adicCompletion F) = 1 := by
    rw [show (4 : v.adicCompletion F) = 2 * 2 by norm_num, map_mul, h2, one_mul]
  have hsq : IsSquare ((z : v.adicCompletion F) / (w * w)) := by
    apply _root_.GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt
    rw [h4, show (z : v.adicCompletion F) / (w * w) - 1 = ((z : v.adicCompletion F) - w * w) / (w * w) by
      field_simp, map_div₀, map_mul, hw, mul_one, div_one]
    exact hlt
  obtain ⟨s, hs⟩ := hsq
  refine ⟨s * w, ?_⟩
  have : (z : v.adicCompletion F) = (z : v.adicCompletion F) / (w * w) * (w * w) := by
    field_simp
  rw [this, hs]
  ring

open NumberField IsDedekindDomain IsLocalRing in
open scoped WithZero in

theorem _root_.GlobalTheory.QNorm.isSquare_mul_of_nonsquare_units : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), Valued.v (2 : v.adicCompletion F) = 1 → ∀ x y : v.adicCompletion F, Valued.v x = 1 → Valued.v y = 1 → ¬ IsSquare x → ¬ IsSquare y → IsSquare (x * y) := by
  intro F _ _ v h2 x y hx hy hnx hny
  classical
  haveI : Fintype (ResidueField (v.adicCompletionIntegers F)) :=
    @Fintype.ofFinite _ (_root_.GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v)
  let x' : v.adicCompletionIntegers F :=
    ⟨x, (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 hx.le⟩
  let y' : v.adicCompletionIntegers F :=
    ⟨y, (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).2 hy.le⟩
  have hrx : ¬ IsSquare (residue (v.adicCompletionIntegers F) x') :=
    fun h => hnx (_root_.GlobalTheory.QNorm.isSquare_of_isSquare_residue_odd F v h2 x' hx h)
  have hry : ¬ IsSquare (residue (v.adicCompletionIntegers F) y') :=
    fun h => hny (_root_.GlobalTheory.QNorm.isSquare_of_isSquare_residue_odd F v h2 y' hy h)
  have hx0 : residue (v.adicCompletionIntegers F) x' ≠ 0 := fun h => hrx (h ▸ ⟨0, by simp⟩)
  have hy0 : residue (v.adicCompletionIntegers F) y' ≠ 0 := fun h => hry (h ▸ ⟨0, by simp⟩)
  have hres : IsSquare (residue (v.adicCompletionIntegers F) (x' * y')) := by
    rw [map_mul, ← quadraticChar_one_iff_isSquare (mul_ne_zero hx0 hy0), map_mul,
      quadraticChar_neg_one_iff_not_isSquare.2 hrx, quadraticChar_neg_one_iff_not_isSquare.2 hry]
    norm_num
  have hxy : Valued.v (((x' * y' : v.adicCompletionIntegers F)) : v.adicCompletion F) = 1 := by
    push_cast
    rw [map_mul]
    simp [x', y', hx, hy]
  simpa [x', y'] using _root_.GlobalTheory.QNorm.isSquare_of_isSquare_residue_odd F v h2 (x' * y') hxy hres

end GlobalTheory.QNorm
