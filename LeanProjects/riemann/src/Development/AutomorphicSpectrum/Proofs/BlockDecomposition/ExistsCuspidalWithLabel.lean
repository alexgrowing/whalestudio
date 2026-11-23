import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.CharacterEqOfRepIso
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.ConjugateCharacterFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalOfUnipotentSumsVanishStatement
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MatrixTraceIffIsCharacterOverSubfieldComplexStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterCuspidalRootSumRegularStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.GeneralLinearFunctionExtendZeroEndPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExponentRegularOfNatDegreeMinpolyGeneratorPowStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumUnipotentRadicalEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyOfIrreduciStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePowStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FrobeniusTorusMinpolyDegreeRootPowerSumStatement

open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory

namespace GlobalTheory.CompanionTheory.TyFin.CuspLabel

theorem root_pow_eq_one {K : Type} [Field K] [Fintype K] {P : K[X]} (hmon : P.Monic) (hirr : Irreducible P)
    (hX : P ≠ X) {x : AlgebraicClosure K} (hx : aeval x P = 0) :
    x ^ (Fintype.card K ^ P.natDegree - 1) = 1 := by
  have hmin : P = minpoly K x := minpoly.eq_of_irreducible_of_monic hirr hx hmon
  have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hfr : Module.finrank K (IntermediateField.adjoin K {x}) = P.natDegree := by
    rw [hmin, IntermediateField.adjoin.finrank hint]
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hX (hmin.trans (minpoly.zero K _))
  haveI : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin K {x}) := Module.finite_of_finite K
  letI := Fintype.ofFinite (IntermediateField.adjoin K {x})
  have hcard : Fintype.card (IntermediateField.adjoin K {x}) = Fintype.card K ^ P.natDegree := by
    rw [← hfr]; exact Module.card_eq_pow_finrank
  have hy : IntermediateField.AdjoinSimple.gen K x ≠ 0 := by
    intro h
    exact hx0 (by simpa using congrArg (algebraMap (IntermediateField.adjoin K {x}) (AlgebraicClosure K)) h)
  have h := FiniteField.pow_card_sub_one_eq_one _ hy
  rw [hcard] at h
  simpa using congrArg (algebraMap (IntermediateField.adjoin K {x}) (AlgebraicClosure K)) h

theorem rootSum_minpoly {K : Type} [Field K] [Fintype K] (θ : AlgebraicClosure K →* ℂ) {d : ℕ} (hd : 0 < d)
    {w : AlgebraicClosure K} (hw : w ^ (Fintype.card K ^ d - 1) = 1) (hdeg : (minpoly K w).natDegree = d)
    (j : ℕ) : GlobalTheory.CuspGL.rootSum θ j (minpoly K w) =
      ∑ i ∈ Finset.range d, θ (w ^ Fintype.card K ^ i) ^ j := by
  have h := (GlobalTheory.T.frobeniusTorus_minpoly_degree_rootPowerSum K θ d hd w (by
    show w ^ (Nat.card K ^ d - 1) = 1
    rw [Nat.card_eq_fintype_card]; exact hw)).2.2 j
  rw [hdeg, Nat.div_self hd, pow_one, Nat.card_eq_fintype_card] at h
  exact h

theorem exists_cuspidal_label : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (C : LabelConv K) (d : ℕ), 1 ≤ d → ∀ P : K[X], P.Monic → Irreducible P → P ≠ X → P.natDegree = d →
    ∃ τ : FDRep ℂ (GL (Fin d) K), Simple τ ∧ IsCuspidal K τ ∧ HasCuspLabel C τ P := by
  intro K _ _ _ C d hd P hmon hirr hX hdeg
  have hcard : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hqd : 1 < Fintype.card K ^ d := Nat.one_lt_pow (by omega) hq
  obtain ⟨x₀, hx₀⟩ := IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure K) P
    (by
      intro h
      have h0 : P.natDegree = 0 := natDegree_eq_of_degree_eq_some (by simpa using h)
      omega)
  have hroot : ∀ w : AlgebraicClosure K, aeval w P = 0 → w ^ (Fintype.card K ^ d - 1) = 1 := fun w hw => by
    rw [← hdeg]; exact root_pow_eq_one hmon hirr hX hw
  have hminP : ∀ w : AlgebraicClosure K, aeval w P = 0 → minpoly K w = P := fun w hw =>
    (minpoly.eq_of_irreducible_of_monic hirr hw hmon).symm
  have hprim : IsPrimitiveRoot (C.gen d) (Fintype.card K ^ d - 1) := by
    rw [← C.gen_order d hd]; exact IsPrimitiveRoot.orderOf _
  haveI : NeZero (Fintype.card K ^ d - 1) := ⟨by omega⟩
  obtain ⟨k, -, hkx⟩ := hprim.eq_pow_of_pow_eq_one (hroot x₀ hx₀)
  have hreg := GlobalTheory.T.exponent_regular_of_natDegree_minpoly_generator_pow K d k (C.gen d) hd (by rw [hcard]; exact C.gen_order d hd)
    (by rw [hkx, hminP x₀ hx₀, hdeg])
  obtain ⟨hch, hip⟩ := GlobalTheory.T.isCharacter_cuspidal_rootSum_regular K C.ι C.ι_inj d k hd hreg
  have hadd := (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow K C.ι k).1
  obtain ⟨n, ρ, hρ⟩ := (GlobalTheory.T.matrixTrace_iff_isCharacterOverSubfield_complex _ _).2 hch
  have hchar : ∀ g : GL (Fin d) K, (PI.SerBridgeGLW.repOfGL ρ).character g = (-1) ^ (d - 1) *
      GlobalTheory.CuspGL.psi (GlobalTheory.CuspGL.rootSum C.ι k) (Fin d → K)
        (Matrix.toLin' (g : Matrix (Fin d) (Fin d) K)) := fun g => by
    rw [PI.SerBridgeGLW.repOfGL_character, ← hρ]
  refine ⟨PI.SerBridgeGLW.repOfGL ρ, ?_, ?_, hmon, hirr, hX, by simpa using hdeg, ?_⟩
  · rw [FDRep.simple_iff_char_is_norm_one]
    rw [(GlobalTheory.T.generalLinearFunctionExtendZeroEnd_properties K d (fun _ => 0)).2.2.1, finsum_eq_sum_of_fintype, GlobalTheory.CuspGL.glCard] at hip
    rw [← hip]
    refine Finset.sum_congr rfl fun x _ => ?_
    have h1 : ((-1 : ℂ) ^ (d - 1)) * ((-1 : ℂ) ^ (d - 1)) = 1 := by
      rw [← mul_pow]; simp
    rw [← PI.SerBridgeGLW.conjugate_character_formula _ (PI.SerBridgeGLW.repOfGL ρ) x, hchar, star_mul', star_pow,
      star_neg, star_one, mul_mul_mul_comm, h1, one_mul]
  · refine GlobalTheory.T.cuspidal_of_unipotent_sums_vanish K d _ fun a ha had => ?_
    have h := GlobalTheory.T.finsum_unipotent_radical_eq_zero_of_isPrimitive K d _ (GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse K (Fin d → K) _ hadd) a ha had
    rw [finsum_mem_def, finsum_eq_sum_of_fintype] at h
    have h2 := congrArg (fun z : ℂ => (-1 : ℂ) ^ (d - 1) * z) h
    simp only [mul_zero, Finset.mul_sum] at h2
    refine Eq.trans ?_ h2
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : ∀ i j : Fin d, (u : Matrix (Fin d) (Fin d) K) i j = (if i = j then 1 else 0) ∨
        ((i : ℕ) < a ∧ a ≤ (j : ℕ))
    · rw [if_pos hu, Set.indicator_of_mem (by exact hu), hchar]
    · rw [if_neg hu, Set.indicator_of_notMem (by exact hu), mul_zero]
  · intro x hx γ hγ z hz m hm
    simp only [Fintype.card_fin] at hm ⊢
    have hQ : minpoly K z = Matrix.charpoly (γ : Matrix (Fin d) (Fin d) K) :=
      (minpoly.eq_of_irreducible_of_monic hγ hz (Matrix.charpoly_monic _)).symm
    have hQd : (minpoly K z).natDegree = d := by
      rw [hQ, Matrix.charpoly_natDegree_eq_dim]; simp
    have hz1 : z ^ (Fintype.card K ^ d - 1) = 1 := by
      rw [← hm, ← pow_mul, mul_comm, pow_mul, ← C.gen_order d hd, pow_orderOf_eq_one, one_pow]
    have hval := GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_of_irreducible K (Fin d → K) _ hadd
      (Matrix.toLin' (γ : Matrix (Fin d) (Fin d) K)) (by rw [Matrix.charpoly_toLin']; exact hγ)
    rw [Matrix.charpoly_toLin'] at hval
    show (PI.SerBridgeGLW.repOfGL ρ).character γ = _
    rw [hchar, hval, ← hQ, rootSum_minpoly C.ι hd hz1 hQd k]
    congr 1
    have hxd : (minpoly K x).natDegree = d := by rw [hminP x hx, hdeg]
    have hx₀d : (minpoly K x₀).natDegree = d := by rw [hminP x₀ hx₀, hdeg]
    calc ∑ i ∈ Finset.range d, C.ι (z ^ Fintype.card K ^ i) ^ k
        = ∑ i ∈ Finset.range d, C.ι (x₀ ^ Fintype.card K ^ i) ^ m := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← map_pow, ← map_pow, ← hm, ← hkx]
          congr 1
          simp only [← pow_mul]
          congr 1
          ring
      _ = GlobalTheory.CuspGL.rootSum C.ι m (minpoly K x₀) := (rootSum_minpoly C.ι hd (hroot x₀ hx₀) hx₀d m).symm
      _ = GlobalTheory.CuspGL.rootSum C.ι m (minpoly K x) := by rw [hminP x₀ hx₀, hminP x hx]
      _ = ∑ i ∈ Finset.range d, C.ι (x ^ Fintype.card K ^ i) ^ m := rootSum_minpoly C.ι hd (hroot x hx) hxd m
      _ = ∑ i ∈ Finset.range d, C.ι x ^ (m * Fintype.card K ^ i) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [map_pow, ← pow_mul, mul_comm (Fintype.card K ^ i) m]

end GlobalTheory.CompanionTheory.TyFin.CuspLabel
