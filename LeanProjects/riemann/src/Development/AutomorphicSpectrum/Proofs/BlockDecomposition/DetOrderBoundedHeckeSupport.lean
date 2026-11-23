import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIntZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatWeightDecreases

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS

theorem det_mem_Ov {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ}
    {M : Matrix (Fin n) (Fin n) (w.adicCompletion E)} (hM : IsInt w M) : M.det ∈ Ov E w := by
  have hN : M = (Ov E w).subtype.mapMatrix (Matrix.of fun i j => (⟨M i j, hM i j⟩ : Ov E w)) := by
    ext i j; rfl
  rw [hN, ← RingHom.map_det]
  exact SetLike.coe_mem _

private theorem v_eq_ofAdd_lemma {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}
    (x : w.adicCompletion E) (hx : x ≠ 0) :
    Valued.v x = ((Multiplicative.ofAdd (-ordL x) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
  have h : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
  rw [ordL, dif_neg h, neg_neg, ofAdd_toAdd, WithZero.coe_unzero]

theorem ordL_det_range : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ϖ : w.adicCompletion E), IsUnifV E w ϖ → ∀ g : GL (Fin n) (w.adicCompletion E), IsInt w g.val → IsInt w (ϖ • (g⁻¹).val) → ∃ i ≤ n, ordL g.val.det = (i : ℤ) := by
  intro E _ _ w n ϖ hϖ g hg hgi
  have hd : g.val.det ∈ Ov E w := det_mem_Ov hg
  have hdi : (ϖ • (g⁻¹).val).det ∈ Ov E w := det_mem_Ov hgi
  have hmul : g.val.det * (g⁻¹).val.det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  have hd0 : g.val.det ≠ 0 := left_ne_zero_of_mul_eq_one hmul
  have hdi0 : (g⁻¹).val.det ≠ 0 := right_ne_zero_of_mul_eq_one hmul
  rw [Matrix.det_smul, Fintype.card_fin] at hdi
  simp only [Ov, ValuationSubring.mem_toSubring, HeightOneSpectrum.mem_adicCompletionIntegers] at hd hdi
  rw [map_mul, map_pow, show Valued.v ϖ =
      ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) from hϖ,
    v_eq_ofAdd_lemma _ hdi0, ← WithZero.coe_pow, ← WithZero.coe_mul, ← ofAdd_nsmul, ← ofAdd_add,
    ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le,
    nsmul_eq_mul, mul_neg, mul_one] at hdi
  rw [v_eq_ofAdd_lemma _ hd0, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero,
    Multiplicative.ofAdd_le] at hd
  have hm := congrArg Valued.v hmul
  rw [map_mul, map_one, v_eq_ofAdd_lemma _ hd0, v_eq_ofAdd_lemma _ hdi0, ← WithZero.coe_mul, ← ofAdd_add,
    ← WithZero.coe_one, WithZero.coe_inj, ofAdd_eq_one] at hm
  refine ⟨(ordL g.val.det).toNat, ?_, ?_⟩
  · omega
  · omega

end GlobalTheory.CompanionTheory.CtS
