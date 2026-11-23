import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitLocalPlaceDataAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomTrivOutsideLoc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CompletedLatticeIntegralityFacts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DivisorsAtInvDualLabelAndStabilizerMul
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceHeckeSatake
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

namespace GlobalTheory.NormaliserGLint

open Matrix

theorem exists_unif (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : v.adicCompletion F, Formalism.UG.IsUnifV F v ϖ := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  refine ⟨(π : v.adicCompletion F), ?_⟩
  unfold Formalism.UG.IsUnifV
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', hπ]
  rfl

theorem mul_entries_mem {L : Type} [Field L] (O : Subring L) {n : ℕ} {A B : Matrix (Fin n) (Fin n) L}
    (hA : ∀ i j, A i j ∈ O) (hB : ∀ i j, B i j ∈ O) : ∀ i j, (A * B) i j ∈ O := by
  intro i j
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => O.mul_mem (hA i k) (hB k j)

theorem mulVec_entries_mem {L : Type} [Field L] (O : Subring L) {n : ℕ} {A : Matrix (Fin n) (Fin n) L}
    {z : Fin n → L} (hA : ∀ i j, A i j ∈ O) (hz : ∀ i, z i ∈ O) : ∀ i, (A *ᵥ z) i ∈ O := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun k _ => O.mul_mem (hA i k) (hz k)

theorem le_of_zpow_eq {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
    {ϖ : v.adicCompletion F} (hϖ : Formalism.UG.IsUnifV F v ϖ) {p q : ℤ} {w : v.adicCompletion F}
    (hw : w ∈ Formalism.UG.Ov F v) (h : ϖ ^ q = ϖ ^ p * w) : p ≤ q := by
  have hv := congrArg Valued.v h
  rw [map_mul, map_zpow₀, map_zpow₀, hϖ] at hv
  have hw' : Valued.v w ≤ 1 := hw
  have key : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ q ≤
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ^ p := by
    rw [hv]; exact mul_le_of_le_one_right' hw'
  rw [← WithZero.coe_zpow, ← WithZero.coe_zpow, WithZero.coe_le_coe, ← ofAdd_zsmul, ← ofAdd_zsmul,
    Multiplicative.ofAdd_le] at key
  simp at key
  omega

end GlobalTheory.NormaliserGLint

namespace GlobalTheory.NormaliserGLint

open Matrix

theorem conj_eq_glint_mul_mul :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ)
    (N : GL (Fin n) (v.adicCompletion F)),
    (∀ g ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v), ∀ z : Fin n → v.adicCompletion F, (∀ i, z i ∈ Formalism.UG.Ov F v) →
      ∃ z' : Fin n → v.adicCompletion F, (∀ i, z' i ∈ Formalism.UG.Ov F v) ∧
        (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec
            ((N : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec z) =
          (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec z') →
    ∀ X : Matrix (Fin n) (Fin n) (v.adicCompletion F), ∃ k₁ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v),
      ∃ k₂ ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.Ov F v),
        ((N⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * X *
            (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
          (k₁ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * X * (k₂ : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  intro F _ _ v n N hN X
  obtain ⟨ϖ, hϖ⟩ := exists_unif F v
  have hϖO : ϖ ∈ Formalism.UG.Ov F v := by
    change Valued.v ϖ ≤ 1
    rw [hϖ]
    exact (by decide : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤ 1)
  have h0 : ϖ ≠ 0 := by rintro rfl; simp [Formalism.UG.IsUnifV] at hϖ
  obtain ⟨m, -, a, ha, b, hb, hNab⟩ := Formalism.UG.Final.CartanDecomp F v n ϖ hϖO hϖ N
  set O := Formalism.UG.Ov F v with hO
  have hbe := Formalism.UG.P.cartan_entries_of_mem O b hb
  have hbi := Formalism.UG.P.cartan_entries_of_mem O _ (inv_mem hb)
  have hae := Formalism.UG.P.cartan_entries_of_mem O a ha
  have hai := Formalism.UG.P.cartan_entries_of_mem O _ (inv_mem ha)
  have ha1 : ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
      (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have ha2 : (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
      ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hb2 : (b : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
      ((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have ha1x : ∀ Y : Matrix (Fin n) (Fin n) (v.adicCompletion F),
      ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
        ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Y) = Y := by
    intro Y; rw [← Matrix.mul_assoc, ha1, Matrix.one_mul]
  have ha2x : ∀ Y : Matrix (Fin n) (Fin n) (v.adicCompletion F),
      (a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
        (((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * Y) = Y := by
    intro Y; rw [← Matrix.mul_assoc, ha2, Matrix.one_mul]
  have key : ∀ i j : Fin n, i ≠ j → m i ≤ m j := by
    intro i j hij
    set E : Matrix (Fin n) (Fin n) (v.adicCompletion F) := Matrix.single i j 1 with hE
    have hsq : E * E = 0 := by rw [hE]; simp [Matrix.single_mul_single_of_ne, hij.symm]
    have hEmem : ∀ r s, E r s ∈ O := by
      intro r s
      simp only [hE, Matrix.single_apply]
      split_ifs
      · exact O.one_mem
      · exact O.zero_mem
    have h1mem : ∀ r s, (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) r s ∈ O := by
      intro r s
      rw [Matrix.one_apply]
      split_ifs
      · exact O.one_mem
      · exact O.zero_mem
    have hAB : ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * (1 + E) *
        ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))) *
        ((a : Matrix (Fin n) (Fin n) (v.adicCompletion F)) * (1 - E) *
        ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))) = 1 := by
      have hpm : (1 + E) * (1 - E) = 1 := by
        rw [add_mul, one_mul, mul_sub, mul_one, hsq]; abel
      simp only [Matrix.mul_assoc, ha1x]
      rw [← Matrix.mul_assoc (1 + E), hpm, Matrix.one_mul, ha2]
    obtain ⟨g, hg, hgA⟩ := Formalism.UG.P.cartan_exists_glint O _ _ hAB
      (mul_entries_mem O (mul_entries_mem O hae fun r s => O.add_mem (h1mem r s) (hEmem r s)) hai)
      (mul_entries_mem O (mul_entries_mem O hae fun r s => O.sub_mem (h1mem r s) (hEmem r s)) hai)
    have hz : ∀ k, (((b⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ
        Pi.single j 1) k ∈ O := mulVec_entries_mem O hbi fun k => by
      rw [Pi.single_apply]; split_ifs
      · exact O.one_mem
      · exact O.zero_mem
    obtain ⟨z', hz', hEq⟩ := hN g hg _ hz
    rw [hgA, hNab] at hEq
    have hL := congrArg (fun w => ((a⁻¹ : GL (Fin n) (v.adicCompletion F)) :
      Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ w) hEq
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, ha1x, hb2, Matrix.mul_one] at hL
    have hi := congrFun hL i
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at hi
    rw [← Matrix.mulVec_mulVec] at hi
    simp only [Formalism.UG.diagPow, Matrix.mul_diagonal, Matrix.mulVec_diagonal, Matrix.add_apply,
      Matrix.one_apply_ne hij, hE, Matrix.single_apply_same, zero_add, one_mul] at hi
    exact le_of_zpow_eq hϖ (mulVec_entries_mem O hbe hz' i) hi
  obtain ⟨c, hc, hD⟩ : ∃ c : v.adicCompletion F, c ≠ 0 ∧
      Formalism.UG.diagPow F v ϖ m = c • (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    rcases n with _ | k
    · exact ⟨1, one_ne_zero, by ext i; exact i.elim0⟩
    · refine ⟨ϖ ^ (m 0), zpow_ne_zero _ h0, ?_⟩
      ext i j
      simp only [Formalism.UG.diagPow, Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs with h
      · subst h
        have hm : m i = m 0 := by
          rcases eq_or_ne i 0 with rfl | hi
          · rfl
          · exact le_antisymm (key i 0 hi) (key 0 i hi.symm)
        rw [hm, mul_one]
      · rw [mul_zero]
  refine ⟨(a * b)⁻¹, inv_mem (mul_mem ha hb), a * b, mul_mem ha hb, ?_⟩
  have hNc : (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      c • ((a * b : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    rw [hNab, hD, Units.val_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  have hNi : ((N⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      c⁻¹ • (((a * b)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
    have h1 : ((N⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
        (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h2 : (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
        (c⁻¹ • (((a * b)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F))) = 1 := by
      rw [hNc, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul, ← Units.val_mul,
        mul_inv_cancel, Units.val_one]
    calc _ = ((N⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
          ((N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *
            (c⁻¹ • (((a * b)⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) := by
          rw [h2, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [hNi, hNc]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, mul_inv_cancel₀ hc, one_smul]

end GlobalTheory.NormaliserGLint
