import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.CharacterEqOfRepIso
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.ConjugateCharacterFormula
open CategoryTheory Polynomial Formalism.IrreducibleCountingLemmas.TYPES Formalism.BasicNotions Formalism.L2.DIV

noncomputable section

namespace GlobalTheory.SeriesIdem

theorem zIdem_pair_ne_zero {G : Type} [Group G] [Fintype G] (τ W : FDRep ℂ G) [Simple τ] [Simple W]
    (h : ∑ x, (zIdem τ).coeff x * W.character x ≠ 0) : Nonempty (W ≅ τ) := by
  classical
  have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  haveI := invertibleOfNonzero hcard
  have ho := FDRep.char_orthonormal W τ
  by_contra hn
  rw [if_neg hn] at ho
  apply h
  have hs : ∑ g, W.character g * τ.character g⁻¹ = 0 := by
    rcases mul_eq_zero.mp ho with h0 | h0
    · exact absurd h0 (inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))
    · exact h0
  calc ∑ x, (zIdem τ).coeff x * W.character x
      = (Module.finrank ℂ τ : ℂ) / Fintype.card G * ∑ g, W.character g * τ.character g⁻¹ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [zIdem_coeff]
        simp only [FDRep.character]
        ring
    _ = 0 := by rw [hs, mul_zero]

end GlobalTheory.SeriesIdem

open GlobalTheory.SeriesIdem in
theorem GlobalTheory.SeriesIdem.exists_simple_of_eSerO_pair : ∀ (g : ℕ) [Fact g.Prime] (C : LabelConv (ZMod g)) (O : LabelMap (ZMod g) C) (r : ℕ) (f : (ZMod g)[X]) (ψ : GL (Fin r) (ZMod g) → ℂ), Formalism.L2.NT.IsIrrChar ψ → ∑ x, (Formalism.L2.NT.eSerO O r f).coeff x * ψ x = ψ 1 → ∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ HasLabelO O τ f ∧ ∀ x, τ.character x = ψ x := by
  intro g _ C O r f ψ hψ hsum
  classical
  obtain ⟨W, hWs, rfl⟩ := (PI.SerBridgeGLW.irrCharIff_of PI.SerBridgeGLW.conjugate_character_formula _ ψ).1 hψ
  haveI := hWs
  by_contra hno
  push_neg at hno
  have hnt : Nontrivial W := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    have h0 : ∀ x, W.character x = 0 := fun x => by
      rw [FDRep.character, Subsingleton.elim (W.ρ x) 0, map_zero]
    have hn1 := (FDRep.simple_iff_char_is_norm_one W).mp hWs
    simp only [h0, zero_mul, Finset.sum_const_zero] at hn1
    exact absurd hn1.symm (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have h1 : W.character 1 ≠ 0 := by
    rw [FDRep.char_one]
    exact_mod_cast Module.finrank_pos.ne'
  apply h1
  rw [← hsum]

  have hz : ∀ z : MonoidAlgebra ℂ (GL (Fin r) (ZMod g)),
      (∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f) →
      ∑ x, z.coeff x * W.character x = 0 := by
    rintro z ⟨τ, hτs, rfl, hτl⟩
    haveI := hτs
    by_contra hne
    obtain ⟨i⟩ := zIdem_pair_ne_zero τ W hne
    obtain ⟨x, hx⟩ := hno τ hτs hτl
    exact hx (by rw [FDRep.char_iso i])
  unfold Formalism.L2.NT.eSerO
  set F : MonoidAlgebra ℂ (GL (Fin r) (ZMod g)) → MonoidAlgebra ℂ (GL (Fin r) (ZMod g)) := fun z =>
    ∑ᶠ (_ : ∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f), z with hF
  by_cases hfin : (Function.support F).Finite
  · rw [finsum_eq_sum F hfin]
    have hsplit : ∑ x, (∑ z ∈ hfin.toFinset, F z).coeff x * W.character x =
        ∑ z ∈ hfin.toFinset, ∑ x, (F z).coeff x * W.character x := by
      simp only [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finset.sum_mul]
      exact Finset.sum_comm
    rw [hsplit]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hP : ∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f
    · simp only [hF, finsum_eq_if, if_pos hP]
      exact hz z hP
    · simp only [hF, finsum_eq_if, if_neg hP]
      simp
  · rw [finsum_of_infinite_support hfin]
    simp
