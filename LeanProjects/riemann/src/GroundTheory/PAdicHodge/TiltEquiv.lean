import Mathlib
import GroundTheory.PAdicHodge.UntiltPerfectoid
import GroundTheory.PAdicHodge.UntiltApprox
import GroundTheory.PAdicHodge.UntiltGalois
import GroundTheory.PAdicHodge.UntiltGaloisCorr
import GroundTheory.PAdicHodge.CompletedAlgClosure
import GroundTheory.PAdicHodge.PerfectoidCharP
import GroundTheory.PAdicHodge.PerfectoidCriterion
import GroundTheory.PAdicHodge.TiltAlgClosed
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

theorem exists_isGalois_le {F L : Type*} [Field F] [Field L] [Algebra F L] [IsAlgClosed L]
    [PerfectField F] (N : IntermediateField F L) [FiniteDimensional F N] :
    ∃ N' : IntermediateField F L, N ≤ N' ∧ FiniteDimensional F N' ∧ IsGalois F N' := by
  classical
  set B := Module.finBasis F N
  set f : Polynomial F := ∏ i, minpoly F (B i : L)
  have hint : ∀ i, IsIntegral F (B i : L) := fun i =>
    (IsIntegral.of_finite F (B i)).map (IntermediateField.val N)
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => minpoly.ne_zero (hint i)
  set N' := IntermediateField.adjoin F (f.rootSet L)
  have hsplit : (f.map (algebraMap F L)).Splits := IsAlgClosed.splits _
  have : Polynomial.IsSplittingField F N' f :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplit
  have hfin : FiniteDimensional F N' := Polynomial.IsSplittingField.finiteDimensional N' f
  have : Normal F N' := Normal.of_isSplittingField f
  have : IsGalois F N' := IsGalois.mk
  refine ⟨N', ?_, hfin, this⟩
  have hB : ∀ i, (B i : L) ∈ N' := fun i => by
    apply IntermediateField.subset_adjoin
    rw [Polynomial.mem_rootSet]
    refine ⟨hf0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_finsetProd]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (minpoly.aeval F (B i : L))
  intro x hx
  have := congrArg (fun u : N => (u : L)) (B.sum_repr ⟨x, hx⟩)
  simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at this
  rw [← this]
  exact N'.sum_mem fun i _ => N'.smul_mem (hB i)

section InC

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C] [IsAlgClosed C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p

variable (K C p) in
include K in

theorem isPerfectoidField_of_isAlgClosed_of_normedAlgebra [CompleteSpace C] :
    IsPerfectoidField C p :=
  IsPerfectoidField.of_isAlgClosed p (by
    rw [← map_natCast (algebraMap K C), norm_algebraMap']
    exact IsPerfectoidField.norm_natCast_lt_one)

variable [IsPerfectoidField C p]

theorem exists_eq_untiltField (L : IntermediateField K C) [FiniteDimensional K L] :
    ∃ M : IntermediateField K♭ C♭, FiniteDimensional K♭ M ∧ untiltField K C p M = L := by
  obtain ⟨N, hN, hLN⟩ := exists_le_untiltField (p := p) L
  have : PerfectField K♭ := PerfectRing.toPerfectField K♭ p
  obtain ⟨N', hNN', hN', hgal⟩ := exists_isGalois_le N
  obtain ⟨M, -, hM, hML⟩ :=
    exists_untiltField_eq_of_le N' L (hLN.trans (untiltField_mono hNN'))
  exact ⟨M, hM, hML⟩

instance isPerfectoidField_of_finiteDimensional (L : IntermediateField K C) [FiniteDimensional K L] :
    IsPerfectoidField L p := by
  obtain ⟨M, hM, hML⟩ := exists_eq_untiltField (p := p) L
  exact IsPerfectoidField.of_ringEquiv p (IntermediateField.equivOfEq hML).toRingEquiv
    fun _ => rfl

theorem untiltField_tiltIntermediateField (L : IntermediateField K C) [FiniteDimensional K L] :
    ∃ _ : FiniteDimensional K♭ (tiltIntermediateField p L),
      untiltField K C p (tiltIntermediateField p L) = L := by
  obtain ⟨M, hM, rfl⟩ := exists_eq_untiltField (p := p) L
  have h : tiltIntermediateField p (untiltField K C p M) = M :=
    tiltIntermediateField_untiltField M
  rw [h]
  exact ⟨hM, rfl⟩

theorem finrank_tiltIntermediateField (L : IntermediateField K C) [FiniteDimensional K L] :
    Module.finrank K♭ (tiltIntermediateField p L) = Module.finrank K L := by
  obtain ⟨M, hM, rfl⟩ := exists_eq_untiltField (p := p) L
  have h : tiltIntermediateField p (untiltField K C p M) = M :=
    tiltIntermediateField_untiltField M
  rw [h, finrank_untiltField]

theorem existsUnique_tiltIntermediateField_eq (M : IntermediateField K♭ C♭)
    [FiniteDimensional K♭ M] :
    ∃! L : IntermediateField K C, ∃ _ : FiniteDimensional K L, tiltIntermediateField p L = M := by
  refine ⟨untiltField K C p M, ⟨inferInstance, tiltIntermediateField_untiltField M⟩, ?_⟩
  rintro L ⟨hL, hLM⟩
  obtain ⟨M', hM', rfl⟩ := exists_eq_untiltField (p := p) L
  have h : tiltIntermediateField p (untiltField K C p M') = M' :=
    tiltIntermediateField_untiltField M'
  rw [h] at hLM
  rw [hLM]

end InC

section Abstract

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem IsPerfectoidField.of_finiteDimensional (p : ℕ) [Fact p.Prime] [IsPerfectoidField K p]
    (L : Type*) [NontriviallyNormedField L] [IsUltrametricDist L] [NormedAlgebra K L]
    [FiniteDimensional K L] : IsPerfectoidField L p := by
  rcases IsPerfectoidField.charZero_or_charP (K := K) p with h0 | hp
  · have := IsPerfectoidField.completeSpace (K := K) p
    have : IsPerfectoidField (CompletedAlgClosure K) p :=
      isPerfectoidField_of_isAlgClosed_of_normedAlgebra K (CompletedAlgClosure K) p
    set j := CompletedAlgClosure.embedding K L
    let e : L ≃ₐ[K] j.fieldRange := AlgEquiv.ofInjectiveField j
    have : FiniteDimensional K j.fieldRange := LinearEquiv.finiteDimensional e.toLinearEquiv
    refine IsPerfectoidField.of_ringEquiv p e.symm.toRingEquiv fun y => ?_
    have h1 : ((e (e.symm y) : j.fieldRange) : CompletedAlgClosure K) = j (e.symm y) := rfl
    rw [AlgEquiv.apply_symm_apply] at h1
    change ‖e.symm y‖ = ‖(y : CompletedAlgClosure K)‖
    rw [h1, CompletedAlgClosure.norm_embedding]
  · exact IsPerfectoidField.of_finiteDimensional_of_charP (K := K) p L

end Abstract

end GroundTheory.PAdicHodge
