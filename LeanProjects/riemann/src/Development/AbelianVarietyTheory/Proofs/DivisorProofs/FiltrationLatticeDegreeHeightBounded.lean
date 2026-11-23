import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibLieLatticeFull
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.HadStA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemistableLatticeRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltrationDegreeRecursionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedDegreeHeightBound
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieRead

set_option autoImplicit false

theorem GlobalTheory.LieRead.steps_read_heights : Hypotheses2 → HypothesesH → OnObj fun D O _ _ H _ => ∃ C : ℝ, ∀ y : Pt O.s, y ∈ H.int → ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K) (ι : K →+* Qb) (h : HermFam K (Fin F.P₀.g → K)), FibTie O y F ι → F.IsHerm h → ∀ τ, ∀ k ≤ O.S.Dw.mult τ, latRank K (stepLat O F τ k) = k ∧ |deg h (stepLat O F τ k) + stepHt O O.met.hm y τ k| ≤ C := by
  intro hP hH D O hc hf A T H hR
  obtain ⟨C, hC⟩ := GlobalTheory.T.graded_degree_height_bound hP hH D O hc hf A T H hR
  refine ⟨max C 0 * ∑ τ : D.host.E →+* ℂ, (O.S.Dw.mult τ : ℝ), ?_⟩
  intro y hy K _ _ F ι h hT hh τ k hk
  obtain ⟨_, _, _, -, -, -, -, hg, -⟩ := id hT
  have hfull : Full F.lieLat := SemiFib.full_lieLat K F
  refine ⟨GlobalTheory.T.semistable_lattice_rank D O K F hg hfull τ k hk, ?_⟩
  have hdeg : ∀ k ≤ O.S.Dw.mult τ, deg h (stepLat O F τ k) = ∑ i ∈ Finset.range k, stepGrDeg O F h τ i := by
    intro k hk
    induction k with
    | zero => simp [stepLat_zero, HadamardFrameExtension.deg_bot]
    | succ k ih => rw [GlobalTheory.T.filtration_degree_recursion D O K F h hg hfull τ k (by omega), ih (by omega), Finset.sum_range_succ]
  have hb : ∀ i ∈ Finset.range k, |stepGrDeg O F h τ i - (adlOf (O.Φ.C _) (O.met.hm _) (Finsupp.single (ArIn.ind ∅, none, .inl (τ, i)) 1)).ht (basePt O.Φ y)| ≤ max C 0 :=
    fun i hi => (hC y hy K F ι h hT hh τ i (by simp at hi; omega)).trans (le_max_left _ _)
  rw [hdeg k hk, stepHt, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ i ∈ Finset.range k, |stepGrDeg O F h τ i - (adlOf (O.Φ.C _) (O.met.hm _) (Finsupp.single (ArIn.ind ∅, none, .inl (τ, i)) 1)).ht (basePt O.Φ y)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ Finset.range k, max C 0 := Finset.sum_le_sum hb
    _ = max C 0 * k := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
    _ ≤ max C 0 * ∑ τ : D.host.E →+* ℂ, (O.S.Dw.mult τ : ℝ) := by
      refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
      calc (k : ℝ) ≤ O.S.Dw.mult τ := by exact_mod_cast hk
        _ ≤ _ := Finset.single_le_sum (f := fun τ => (O.S.Dw.mult τ : ℝ)) (fun _ _ => by positivity) (Finset.mem_univ τ)
