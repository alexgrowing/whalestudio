import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.EisensteinMeromorphy.HgtMulRight
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.IsCompactStandardMaximalCompact
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.HeightFunctionContinuousPos
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EisensteinSeriesConvergenceBound

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.SiegelWeilFormula
namespace PositivityTheory.SiegelWeilFormula.Khead
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem majorant_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (hS : d.Strong) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) :
    ∃ t : ℝ, ∀ z : ℂ, t < z.re → ∀ C : Set d.G, IsCompact C →
      ∃ u : GlobalTheory.Eis.Cosets (par2 σ d.Y) (rat2 σ d.Y) → ℝ, Summable u ∧
        ∀ g ∈ C, ∀ q, ‖GlobalTheory.Eis.term (par2 σ d.Y) (rat2 σ d.Y) (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) g q‖ ≤ u q := by
  obtain ⟨r', s', hY⟩ := hS
  have hKc : IsCompact (d.K : Set d.G) := _root_.GlobalTheory.T.isCompact_standard_maximal_compact F E σ d.B d.n d.Y r' s' d.ok.good d.ok.hn hY d.b d.K d.a
    d.ok.frame d.ok.stdK d.ok.hgt
  obtain ⟨hac, hpos⟩ := _root_.GlobalTheory.T.height_function_continuous_pos F E σ d.B d.n d.Y r' s' d.ok.good d.ok.hn hY d.b d.K d.a d.ok.frame d.ok.stdK d.ok.hgt
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.flat_section_growth_bound d.K d.a hKc d.ok.hgt hpos d.χ s₁ f hf
  obtain ⟨σ₀, hσ⟩ := _root_.GlobalTheory.T.eisenstein_series_convergence_bound F E σ d.B d.n d.Y r' s' d.ok.good d.ok.hn hY d.b d.K d.a d.ok.frame d.ok.stdK d.ok.hgt
  refine ⟨σ₀ - (d.n : ℝ) / 2, fun z hz C hC => ?_⟩
  set σ' : ℝ := z.re + (d.n : ℝ) / 2 with hσ'
  have h1 : σ₀ < σ' := by linarith
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup d.G := Subgroup.instIsTopologicalGroupSubtypeMem _
  have hKC : IsCompact ((d.K : Set d.G) * C) := hKc.mul hC
  obtain ⟨M, hM⟩ := hKC.exists_bound_of_continuousOn hac.continuousOn
  obtain ⟨M', hM'⟩ := hKC.exists_bound_of_continuousOn (hac.inv₀ fun y => (hpos y).ne').continuousOn
  have hr : ∀ x, ∀ c ∈ C, d.a (x * c) ^ σ' ≤ (|M| ^ σ' + (|M'|⁻¹) ^ σ') * d.a x ^ σ' := by
    intro x c hc
    obtain ⟨k, hk, e⟩ := hgt_mul_right d.ok.hgt x c
    have hkc : k * c ∈ (d.K : Set d.G) * C := Set.mul_mem_mul hk hc
    have r0 := hpos (k * c)
    have rM : d.a (k * c) ≤ |M| := (Real.le_norm_self _).trans ((hM _ hkc).trans (le_abs_self M))
    have hm := hM' _ hkc
    rw [Pi.inv_apply, norm_inv, Real.norm_of_nonneg r0.le] at hm
    have hM'pos : 0 < |M'| := lt_of_lt_of_le (inv_pos.2 r0) (hm.trans (le_abs_self _))
    have rm : |M'|⁻¹ ≤ d.a (k * c) := (inv_le_comm₀ hM'pos r0).2 (hm.trans (le_abs_self _))
    have hb : d.a (k * c) ^ σ' ≤ |M| ^ σ' + (|M'|⁻¹) ^ σ' := by
      rcases le_total 0 σ' with hs | hs
      · exact (Real.rpow_le_rpow r0.le rM hs).trans
          (le_add_of_nonneg_right (Real.rpow_nonneg (inv_nonneg.2 (abs_nonneg _)) _))
      · exact (Real.rpow_le_rpow_of_nonpos (inv_pos.2 hM'pos) rm hs).trans
          (le_add_of_nonneg_left (Real.rpow_nonneg (abs_nonneg _) _))
    rw [e, Real.mul_rpow (hpos x).le r0.le, mul_comm]
    exact mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg (hpos x).le _)
  obtain ⟨_, _, hsum⟩ := hσ σ' h1
  refine ⟨fun q => |C0| * (|M| ^ σ' + (|M'|⁻¹) ^ σ') * d.a ((Quotient.out q).1 * 1) ^ σ', (hsum 1).1.mul_left _,
    fun g hg q => ?_⟩
  have hΦ : (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) = flat d.a f s₁ z := funext fun y => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.Ht, flat]
    rw [Real.coe_toNNReal _ (hpos y).le]
  rw [hΦ]
  show ‖flat d.a f s₁ z ((Quotient.out q).1 * g)‖ ≤ _
  simp only [mul_one]
  calc _ ≤ C0 * d.a ((Quotient.out q).1 * g) ^ σ' := hC0 z _
    _ ≤ |C0| * d.a ((Quotient.out q).1 * g) ^ σ' := mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (hpos _).le _)
    _ ≤ |C0| * ((|M| ^ σ' + (|M'|⁻¹) ^ σ') * d.a (Quotient.out q).1 ^ σ') :=
        mul_le_mul_of_nonneg_left (hr _ g hg) (abs_nonneg _)
    _ = _ := by ring
end PositivityTheory.SiegelWeilFormula.Khead
end
end
