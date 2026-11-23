import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SumRhoEqTrace
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarMeasureScalingStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.ThW

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem muF_latN : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι F) (N : ℕ), 0 < N → (muF B lf (latN F ι N : Set (ι → A F))).toReal = kap F ^ Fintype.card ι * (Real.sqrt |((Algebra.norm ℚ B.det : ℚ) : ℝ)|)⁻¹ * (((N : ℝ) ^ Module.finrank ℚ F)⁻¹) ^ Fintype.card ι := by
  intro F _ _ _ _ lf hH h1 ι _ _ B N hN
  obtain ⟨hlc, hsc, ht2, -, hopen, -, -, -, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI := hlc
  haveI := hsc
  haveI := ht2
  haveI : SigmaFinite lf := inferInstance
  have hscale := (GlobalTheory.T.adelic_haar_measure_scaling F lf hH h1).1
  have hNF : ((N : F)) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hnorm : ((Algebra.norm ℚ (N : F) : ℚ) : ℝ) = (N : ℝ) ^ Module.finrank ℚ F := by
    have : (N : F) = algebraMap ℚ F (N : ℚ) := by simp
    rw [this, Algebra.norm_algebraMap]
    push_cast
    rfl
  set S : Set (A F) := (fun x => algebraMap F (A F) (N : F) * x) '' Oh F with hSdef
  have hlf : lf S = ENNReal.ofReal (((N : ℝ) ^ Module.finrank ℚ F)⁻¹) := by
    rw [hSdef, hscale (N : F) hNF (Oh F) hopen.measurableSet, h1, mul_one, hnorm,
      abs_of_nonneg (by positivity)]
  have hset : (latN F ι N : Set (ι → A F)) = Set.pi Set.univ (fun _ => S) := by
    ext x
    simp only [SetLike.mem_coe, Set.mem_pi, Set.mem_univ, true_imp_iff, hSdef, Set.mem_image,
      map_natCast]
    constructor
    · intro h i
      obtain ⟨y, hy, e⟩ := h i
      exact ⟨y, hy, e.symm⟩
    · intro h i
      obtain ⟨y, hy, e⟩ := h i
      exact ⟨y, hy, e.symm⟩
  have hk : 0 ≤ kap F := inv_nonneg.mpr (Real.sqrt_nonneg _)
  rw [hset, muF, Measure.smul_apply, Measure.pi_pi, smul_eq_mul, Finset.prod_const,
    Finset.card_univ, hlf, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal]
  positivity

end GlobalTheory.CompanionTheory.SW.ThW
