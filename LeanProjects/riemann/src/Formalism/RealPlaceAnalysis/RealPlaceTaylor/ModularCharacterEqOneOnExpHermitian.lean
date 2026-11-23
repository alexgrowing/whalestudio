import Formalism.RealPlaceAnalysis.InstMeasurableSpaceUJ
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexificationHolds
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InvolutionInvariants

open MeasureTheory Matrix Topology
open scoped NNReal ENNReal

noncomputable section

namespace Formalism.REAL

def indefiniteUnitaryMk {n : ℕ} (ε : Fin n → Bool) (m : Matrix (Fin n) (Fin n) ℂ) (h : inUJ ε m) : UJ ε :=
  ⟨⟨m, Jm ε * mᴴ * Jm ε, (indefinite_unitary_inv_closed n ε m h).1, (indefinite_unitary_inv_closed n ε m h).2⟩, h⟩

lemma indefiniteUnitaryMk_val {n : ℕ} (ε : Fin n → Bool) (m : Matrix (Fin n) (Fin n) ℂ) (h : inUJ ε m) :
    (((indefiniteUnitaryMk ε m h : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = m := rfl

lemma indefinite_unitary_ext {n : ℕ} {ε : Fin n → Bool} {g h : UJ ε}
    (e : ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) =
      ((h : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)) : g = h :=
  Subtype.ext (Units.ext e)

abbrev modularCharacterAlt {n : ℕ} (ε : Fin n → Bool) (g : UJ ε) : ℝ≥0 := Measure.modularCharacterFun g

lemma map_mul_right_haar_modular_alt {n : ℕ} (ε : Fin n → Bool) (g : UJ ε) :
    Measure.map (fun x => x * g) (muG ε) = modularCharacterAlt ε g • muG ε := by
  rw [modularCharacterAlt, Measure.modularCharacterFun_eq_haarScalarFactor (muG ε) g]
  exact Measure.isMulLeftInvariant_eq_smul _ _

lemma modularCharacter_mul {n : ℕ} (ε : Fin n → Bool) (g h : UJ ε) :
    modularCharacterAlt ε (g * h) = modularCharacterAlt ε g * modularCharacterAlt ε h :=
  Measure.modularCharacterFun_map_mul g h

lemma modularCharacter_one {n : ℕ} (ε : Fin n → Bool) : modularCharacterAlt ε 1 = 1 :=
  Measure.modularCharacterFun_map_one

lemma continuous_frobenius_on_group {n : ℕ} (ε : Fin n → Bool) : Continuous (hsG (ε := ε)) :=
  continuous_hs_real_place_taylor.comp (continuous_coeMatrix ε)

lemma frobenius_ball_compact_pos_finite {n : ℕ} (ε : Fin n → Bool) :
    IsCompact {g : UJ ε | hsG g ≤ (n : ℝ) + 1} ∧ 0 < muG ε {g : UJ ε | hsG g ≤ (n : ℝ) + 1} ∧
      muG ε {g : UJ ε | hsG g ≤ (n : ℝ) + 1} < ⊤ := by
  have hc : IsCompact {g : UJ ε | hsG g ≤ (n : ℝ) + 1} := by
    have h := (isClosedEmbeddingMatrix n ε).1.isCompact_preimage ((hermitian_small_ball n ε).1 ((n : ℝ) + 1))
    convert h using 1
    ext g
    exact ⟨fun hg => ⟨g.2, hg⟩, fun hg => hg.2⟩
  refine ⟨hc, ?_, hc.measure_lt_top⟩
  have hU : IsOpen {g : UJ ε | hsG g < (n : ℝ) + 1} :=
    isOpen_lt (continuous_frobenius_on_group ε) continuous_const
  have h1 : (1 : UJ ε) ∈ {g : UJ ε | hsG g < (n : ℝ) + 1} := by
    show hs (1 : Matrix (Fin n) (Fin n) ℂ) < (n : ℝ) + 1
    rw [f1auxiliary_hs_one]; linarith
  exact (hU.measure_pos (muG ε) ⟨1, h1⟩).trans_le
    (measure_mono fun g (hg : hsG g < (n : ℝ) + 1) => hg.le)

lemma modularCharacter_eq_one_on_compact {n : ℕ} (ε : Fin n → Bool) (g : UJ ε)
    (hk : ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε) :
    modularCharacterAlt ε g = 1 := by
  obtain ⟨hc, hpos, hfin⟩ := frobenius_ball_compact_pos_finite ε
  set B := {g : UJ ε | hsG g ≤ (n : ℝ) + 1} with hB
  have hBm : MeasurableSet B := hc.isClosed.measurableSet
  have hpre : (fun x => x * g) ⁻¹' B = B := by
    ext x
    simp only [hB, Set.mem_preimage, Set.mem_ofPred_eq, hsG, Subgroup.coe_mul, Units.val_mul]
    rw [((hermitian_small_ball n ε).2 _ _ hk).1]
  have h1 := map_mul_right_haar_modular_alt ε g
  have h2 : (Measure.map (fun x => x * g) (muG ε)) B = muG ε B := by
    rw [Measure.map_apply (measurable_mul_const g) hBm, hpre]
  rw [h1, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
  have h3 : ((modularCharacterAlt ε g : ℝ≥0∞)) * muG ε B = 1 * muG ε B := by rw [h2, one_mul]
  rw [ENNReal.mul_left_inj hpos.ne' hfin.ne] at h3
  exact_mod_cast h3

lemma signature_mem_indefinite_unitary {n : ℕ} (ε : Fin n → Bool) : inUJ ε (Jm ε) :=
  (maximal_compact_facts n ε).1 _ (maximal_compact_facts n ε).2.2.1

lemma modularCharacter_eq_one_on_exp_hermitian {n : ℕ} (ε : Fin n → Bool) (p : UJ ε) (X : Matrix (Fin n) (Fin n) ℂ) (hX : inP ε X)
    (hp : ((p : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = NormedSpace.exp X) :
    modularCharacterAlt ε p = 1 := by
  set j := indefiniteUnitaryMk ε (Jm ε) (signature_mem_indefinite_unitary ε) with hj
  have hDj : modularCharacterAlt ε j = 1 := modularCharacter_eq_one_on_compact ε j (maximal_compact_facts n ε).2.2.1
  have hherm : (NormedSpace.exp X)ᴴ = NormedSpace.exp X :=
    exp_conjTranspose_of_hermitian (((parabolic_character_holds n ε X).1.mp hX).1)
  have hconj : j * p * j = p⁻¹ := by
    apply indefinite_unitary_ext
    have hinv := coeMatrix_inv_eq ε p
    simp only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_inv]
    rw [hinv, hj, indefiniteUnitaryMk_val]
    show Jm ε * _ * Jm ε = Jm ε * (coeMatrixAlt ε p)ᴴ * Jm ε
    rw [show coeMatrixAlt ε p = NormedSpace.exp X from hp, hp, hherm]
  have h1 : modularCharacterAlt ε p⁻¹ = modularCharacterAlt ε p := by
    rw [← hconj, modularCharacter_mul, modularCharacter_mul, hDj, one_mul, mul_one]
  have h2 : modularCharacterAlt ε p * modularCharacterAlt ε p = 1 := by
    rw [← modularCharacter_one ε, ← mul_inv_cancel p, modularCharacter_mul, h1]
  have h3 : ((modularCharacterAlt ε p : ℝ≥0) : ℝ) * (modularCharacterAlt ε p : ℝ) = 1 := by exact_mod_cast h2
  have h4 : (0 : ℝ) ≤ (modularCharacterAlt ε p : ℝ) := (modularCharacterAlt ε p).2
  have h5 : ((modularCharacterAlt ε p : ℝ≥0) : ℝ) = 1 := by nlinarith
  exact_mod_cast h5

lemma modularCharacter_eq_one_alt {n : ℕ} (ε : Fin n → Bool) (g : UJ ε) : modularCharacterAlt ε g = 1 := by
  have hgU : inUJ ε ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) := g.2
  obtain ⟨k, X, hk, hX, hg⟩ := (polar_decomposition_holds n ε).1 _ hgU
  have hkU : inUJ ε k := (maximal_compact_facts n ε).1 k hk
  have hEU : inUJ ε (NormedSpace.exp X) := by
    have h := exp_indefinite_unitary_holds n ε X hX.1 1
    rwa [Complex.ofReal_one, one_smul] at h
  have hdec : g = indefiniteUnitaryMk ε k hkU * indefiniteUnitaryMk ε _ hEU := by
    apply indefinite_unitary_ext
    rw [Subgroup.coe_mul, Units.val_mul, indefiniteUnitaryMk_val, indefiniteUnitaryMk_val]
    exact hg
  have hk' : (((indefiniteUnitaryMk ε k hkU : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ)
      ∈ Kset ε := hk
  rw [hdec, modularCharacter_mul, modularCharacter_eq_one_on_compact ε _ hk', modularCharacter_eq_one_on_exp_hermitian ε _ X hX (indefiniteUnitaryMk_val ε _ hEU), one_mul]

theorem indefinite_unitary_unimodular : Unimodular := by
  intro n ε g
  rw [map_mul_right_haar_modular_alt, modularCharacter_eq_one_alt, one_smul]

theorem invInvariant_of (h : Unimodular) : InvInvariant :=
  _root_.UpperTheory.Reformulated.B.InvolutionInvariants.invInvariant_of h

end Formalism.REAL
