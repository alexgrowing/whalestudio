import Mathlib
import Formalism.LocalToGlobal.Divisibility.QLocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsUnrM
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsNrm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddHaarCompletionIntegralMatricesVolOne
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
open MeasureTheory Matrix NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DoubleCosetMeasures Formalism.L2.Host Formalism.L2.DIV Formalism.L2.DIV.QLoc GlobalTheory.Mem.HD

namespace GlobalTheory.ParahoricTopo

theorem isClopen_OP {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) :
    IsClopen ((OP P : Subring (P.adicCompletion L)) : Set (P.adicCompletion L)) :=
  Valued.isClopen_valuationSubring (P.adicCompletion L)

theorem isClopen_mulSet {L : Type} [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L))
    (ϖ : P.adicCompletion L) (hϖ : ϖ ≠ 0) :
    IsClopen {y : P.adicCompletion L | ∃ o ∈ OP P, y = ϖ * o} := by
  have e : {y : P.adicCompletion L | ∃ o ∈ OP P, y = ϖ * o} =
      (fun y => ϖ⁻¹ * y) ⁻¹' ((OP P : Subring (P.adicCompletion L)) : Set (P.adicCompletion L)) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe]
    constructor
    · rintro ⟨o, ho, rfl⟩
      rwa [← mul_assoc, inv_mul_cancel₀ hϖ, one_mul]
    · intro h
      exact ⟨_, h, by rw [← mul_assoc, mul_inv_cancel₀ hϖ, one_mul]⟩
  rw [e]
  exact (isClopen_OP P).preimage (continuous_const.mul continuous_id)

theorem isOpen_isCompact_parJ : ∀ (L : Type) [Field L] [NumberField L] (P : HeightOneSpectrum (𝓞 L)) (r c : ℕ), IsOpen (parJ (OP P) (piP P : P.adicCompletion L) r c) ∧ IsCompact (parJ (OP P) (piP P : P.adicCompletion L) r c) := by
  intro L _ _ P r c
  letI := GlobalTheory.LocalData.complRel P
  haveI := GlobalTheory.LocalData.isLocalField P
  haveI : (Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (P.adicCompletion L))
    (Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ)))
  have hK : GlobalTheory.SplitWeil.KO (P.adicCompletion L) (Fin (r + c)) = GLint (OP P) (r + c) := by
    ext g
    rw [GlobalTheory.SplitFlip.mem_KO_iff]
    simp only [he.le_one_iff_le_one, Valuation.mem_integer_iff]
    exact Iff.rfl
  have hS := isClopen_mulSet P (piP P : P.adicCompletion L) (Units.ne_zero _)
  set B : Set (GL (Fin (r + c)) (P.adicCompletion L)) :=
    {k | bDA (k : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) ∈
      IIset (t := c) (a := r) (OP P) (piP P : P.adicCompletion L)} with hB
  have hBe : B = ⋂ i : Fin c, ⋂ j : Fin r,
      (fun k : GL (Fin (r + c)) (P.adicCompletion L) =>
        (k : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) (Fin.natAdd r i) (Fin.castAdd c j)) ⁻¹'
        {y : P.adicCompletion L | ∃ o ∈ OP P, y = (piP P : P.adicCompletion L) * o} := by
    ext k
    simp only [hB, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, IIset, bDA, Matrix.submatrix_apply]
  have hcont : ∀ (i : Fin (r + c)) (j : Fin (r + c)), Continuous fun k : GL (Fin (r + c)) (P.adicCompletion L) =>
      (k : Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L)) i j := fun i j =>
    (Units.continuous_val (M := Matrix (Fin (r + c)) (Fin (r + c)) (P.adicCompletion L))).matrix_elem i j
  have hBc : IsClopen B := by
    rw [hBe]
    exact isClopen_iInter_of_finite fun i => isClopen_iInter_of_finite fun j => hS.preimage (hcont _ _)
  have hP : parJ (OP P) (piP P : P.adicCompletion L) r c =
      (GlobalTheory.SplitWeil.KO (P.adicCompletion L) (Fin (r + c)) : Set _) ∩ B := by
    rw [hK]; rfl
  rw [hP]
  exact ⟨GlobalTheory.SplitFlip.isOpen_KO.inter hBc.isOpen, GlobalTheory.SplitFlip.isCompact_KO.inter_right hBc.isClosed⟩

end GlobalTheory.ParahoricTopo
