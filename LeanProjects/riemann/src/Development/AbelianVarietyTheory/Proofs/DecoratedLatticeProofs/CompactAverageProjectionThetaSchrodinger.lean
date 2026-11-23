import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MeanPair
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.RegularisingElement
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinResidue
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.FirstTermIdentitySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableOneP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactAverageSchwartzProjectionMemAdelicSchwartStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerFunctionUnitaryLeviRadicalActions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledThetaEqSumSchrodingerFunctionPeriodisatio
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledPairSchrodingerFunctionContinuousIntegrab
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledPairThetaFunctionEqZeroOfSchrodingerEqZer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalSh
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSummableBoundSchwartzMajorantRationalTransStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RegSchProj

open GlobalTheory.Unf

variable {D : D7}

theorem realSize_mul_le (θ : InfFam D) {m n k : ℕ} (Y : Mx D m n) (a : Mx D n k) :
    realSize θ (Y ⬝ a) ≤ (k * realSize θ Y) * realSize θ a := by
  calc realSize θ (Y ⬝ a) = ∑ τ, ∑ i, ∑ j, ‖∑ l, compAt θ τ Y i l * compAt θ τ a l j‖ := by
        simp only [realSize, MajMeas.compAt_mul, Matrix.mul_apply]
    _ ≤ ∑ τ, ∑ i, ∑ _j : Fin k, ∑ l, ‖compAt θ τ Y i l‖ * realSize θ a := by
        gcongr with τ _ i _ j _
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (MajMeas.norm_compAt_le_realSize θ a τ l j) (norm_nonneg _)
    _ = _ := by
        generalize realSize θ a = r
        simp only [realSize, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum,
          Finset.sum_mul, mul_assoc]

theorem maj_mt_le {θ : InfFam D} (hθ : IsInfFam θ) (T : HSp D) (n : ℕ) {K : Set (GA D T)} (hK : IsCompact K)
    {K₀ : Set (Mx D T.rank n)} (hK₀ : IsCompact K₀) :
    ∃ K' : Set (Mx D T.rank n), IsCompact K' ∧ ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ k ∈ K, ∀ u : Mx D T.rank n,
      maj θ K₀ N (mt T k⁻¹ ⬝ u) ≤ C * maj θ K' N u := by
  obtain ⟨h1, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  have hmt : Continuous (mt T) := GlobalTheory.MixModel.continuous_mt T
  obtain ⟨c, hc⟩ := (hK.image ((MajMeas.continuous_realSize hθ).comp hmt)).bddAbove
  let P : GA D T × Mx D T.rank n → Mx D T.rank n := fun p => mt T p.1 ⬝ p.2
  have hP : Continuous P := (hmt.comp continuous_fst).matrix_mul continuous_snd
  refine ⟨P '' (K ×ˢ K₀), (hK.prod hK₀).image hP, fun N => ⟨(1 + n * |c|) ^ N, by positivity, fun k hk u => ?_⟩⟩
  have hyx : (mt T k : Mx D T.rank T.rank) * mt T k⁻¹ = 1 := by
    show mt T (k * k⁻¹) = 1
    rw [mul_inv_cancel]; rfl
  have hu : (mt T k ⬝ (mt T k⁻¹ ⬝ u) : Mx D T.rank n) = u := by
    rw [← Matrix.mul_assoc, hyx, Matrix.one_mul]
  by_cases hb : InBox K₀ (mt T k⁻¹ ⬝ u)
  · have hb' : InBox (P '' (K ×ˢ K₀)) u := by
      obtain ⟨k0, hk0, hkx⟩ := hb
      refine ⟨P (k, k0), ⟨(k, k0), ⟨hk, hk0⟩, rfl⟩, ?_⟩
      have e : u - P (k, k0) = (mt T k ⬝ ((mt T k⁻¹ ⬝ u : Mx D T.rank n) - k0) : Mx D T.rank n) := by
        rw [Matrix.mul_sub, hu]
      rw [e, Matrix.map_mul, hkx, Matrix.mul_zero]
    simp only [maj, if_pos hb, if_pos hb']
    have hs := realSize_mul_le θ (mt T k) (mt T k⁻¹ ⬝ u : Mx D T.rank n)
    rw [hu] at hs
    have hck : realSize θ (mt T k) ≤ |c| := (hc ⟨k, hk, rfl⟩).trans (le_abs_self c)
    have h0 := realSize_nonneg θ (mt T k⁻¹ ⬝ u : Mx D T.rank n)
    have h0' := realSize_nonneg θ u
    generalize realSize θ (mt T k⁻¹ ⬝ u : Mx D T.rank n) = r at hs h0 ⊢
    have hs' : realSize θ u ≤ (n * |c|) * r := hs.trans (by gcongr)
    have hn : (0 : ℝ) ≤ n * |c| := by positivity
    have hle : 1 + realSize θ u ≤ (1 + n * |c|) * (1 + r) := by nlinarith
    have hA : 0 < (1 + r) ^ N := by positivity
    have hB : 0 < (1 + realSize θ u) ^ N := by positivity
    rw [inv_eq_one_div, ← div_eq_mul_inv, div_le_div_iff₀ hA hB, one_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hle N
  · have e : maj θ K₀ N (mt T k⁻¹ ⬝ u) = 0 := by simp only [maj, if_neg hb]
    rw [e]
    exact mul_nonneg (by positivity) (maj_nonneg θ _ N u)

theorem exists_summable_bound {θ : InfFam D} (hθ : IsInfFam θ) (T : HSp D) (n : ℕ) {K : Set (GA D T)} (hK : IsCompact K)
    {Φ : Mx D T.rank n → ℂ} (hΦ : Φ ∈ schwartzA θ T.rank n) (x : Mx D T.rank n) :
    ∃ b : Matrix (Fin T.rank) (Fin n) D.host.E → ℝ, Summable b ∧
      ∀ k ∈ K, ∀ ξ, ‖Φ (mt T k⁻¹ ⬝ (x + rat ξ : Mx D T.rank n))‖ ≤ b ξ := by
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_summable_bound_schwartz_majorant_rational_translates D θ hθ T.rank n
  obtain ⟨-, K₀, hK₀, hC⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ T.rank n Φ
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ T.rank n Φ hΦ)
  obtain ⟨C, hC⟩ := hC N
  obtain ⟨K', hK', hM⟩ := maj_mt_le hθ T n hK hK₀
  obtain ⟨C', hC', hM⟩ := hM N
  obtain ⟨b, hb, hb'⟩ := hN K' {x} hK' isCompact_singleton
  refine ⟨fun ξ => |C| * (C' * b ξ), (hb.mul_left C').mul_left |C|, fun k hk ξ => (hC _).trans ?_⟩
  exact mul_le_mul (le_abs_self C) ((hM k hk _).trans (mul_le_mul_of_nonneg_left (hb' x rfl ξ) hC'))
    (maj_nonneg _ _ _ _) (abs_nonneg C)

theorem hasSum_sch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D)
    {ν : Measure (WO A B)} {𝓨 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓨) {f : WO (dblSp A) B → ℂ}
    (hf : IsThetaFunO ψ (dblSp A) B f) (x y : Mx D B.rank A.rank) :
    HasSum (fun ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E =>
      ψ (symplO (dblSp A) B ((GlobalTheory.Core.Rk.SWLaw.dblDec A).extX B (x + rat ξ)) ((GlobalTheory.Core.Rk.SWLaw.dblDec A).extY B y)) * sch ψ A B ν 𝓨 f (x + rat ξ))
      (ψ (symplOH (dblSp A) B ((GlobalTheory.Core.Rk.SWLaw.dblDec A).extX B x) ((GlobalTheory.Core.Rk.SWLaw.dblDec A).extY B y)) *
        f ((GlobalTheory.Core.Rk.SWLaw.dblDec A).extX B x + (GlobalTheory.Core.Rk.SWLaw.dblDec A).extY B y)) := by
  have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf ((GlobalTheory.Core.Rk.SWLaw.dblDec A).extY B y)
  have hsum := (GlobalTheory.Core.Rk.SchPeriod.theta_eq_sum_sch D ψ hψ A B ν 𝓨 hν _ hg x).2
  simp only [GlobalTheory.Core.Rk.SchwInj.sch_heisO_extY hψ A B hν hf] at hsum
  exact hsum

theorem projK_theta_sch : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χ : (AE D)ˣ →* Circle) (om : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ om → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ K : Subgroup (GA D B), IsCompact (K : Set (GA D B)) → ∀ νK : Measure K, IsProbabilityMeasure νK → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → IsThetaFunO ψ (dblSp A) B (projK om νK φ) ∧ sch ψ A B ν 𝓨 (projK om νK φ) = projS νK (sch ψ A B ν 𝓨 φ) := by
  intro D ψ A B χ om hW ν 𝓨 hν K hK νK hνK φ hφ
  have hψ := hW.std
  obtain ⟨θ, hθ⟩ : ∃ θ : InfFam D, IsInfFam θ := GlobalTheory.DualPairCompare.exists_infFam D
  obtain ⟨h1, h2, -⟩ := GlobalTheory.SchSchwartzAll.schSchwartz D ψ hψ θ hθ A B ν 𝓨 hν
  obtain ⟨f', hf', hs⟩ := h2 _ (GlobalTheory.T.compactAverageSchwartzProjection_mem_adelicSchwartz D θ hθ B A.rank K hK νK hνK _ (h1 φ hφ))
  suffices h : projK om νK φ = f' by rw [h]; exact ⟨hf', hs⟩
  funext w
  obtain ⟨x, y, rfl⟩ := GlobalTheory.Core.Rk.SchwInj.exists_extX_add_extY A B w
  obtain ⟨b, hb, hb'⟩ := exists_summable_bound hθ B A.rank hK (h1 φ hφ) x
  obtain ⟨-, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  haveI : BorelSpace (GA D B) := ⟨rfl⟩
  haveI : IsTopologicalGroup (GA D B) := (Formalism.IndefR.Eqv.ga_facts D B).1
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin B.rank) (Fin A.rank) D.host.E) := inferInstanceAs (Countable (Fin _ → Fin _ → _))
  have hc := (GlobalTheory.Core.Rk.SchInt.sch_continuous_integrable D ψ hψ A B ν 𝓨 hν φ hφ).1
  have hmt : Continuous fun k : K => mt B (k : GA D B)⁻¹ :=
    (GlobalTheory.MixModel.continuous_mt B).comp continuous_subtype_val.inv
  have hn : ∀ a, ‖ψ a‖ = 1 := hψ.1.2.1
  have key := hasSum_integral_of_dominated_convergence (μ := νK)
    (F := fun (ξ : Matrix (Fin B.rank) (Fin A.rank) D.host.E) (k : K) =>
      ψ (symplO (dblSp A) B ((GlobalTheory.Core.Rk.SWLaw.dblDec A).extX B (x + rat ξ)) ((GlobalTheory.Core.Rk.SWLaw.dblDec A).extY B y)) *
        sch ψ A B ν 𝓨 φ (mt B (k : GA D B)⁻¹ ⬝ (x + rat ξ : Mx D B.rank A.rank)))
    (f := fun k : K => ψ (symplOH (dblSp A) B ((GlobalTheory.Core.Rk.SWLaw.dblDec A).extX B x) ((GlobalTheory.Core.Rk.SWLaw.dblDec A).extY B y)) *
        om (1, (k : GA D B)) φ ((GlobalTheory.Core.Rk.SWLaw.dblDec A).extX B x + (GlobalTheory.Core.Rk.SWLaw.dblDec A).extY B y))
    (fun ξ _ => b ξ)
    (fun ξ => (continuous_const.mul (hc.comp (hmt.matrix_mul continuous_const))).measurable.aestronglyMeasurable)
    (fun ξ => .of_forall fun k => by rw [norm_mul, hn, one_mul]; exact hb' k k.2 ξ)
    (.of_forall fun _ => hb) (integrable_const _)
    (.of_forall fun k => by
      have h := hasSum_sch hψ A B hν (hW.om_pres (1, (k : GA D B)) φ hφ) x y
      simp only [(GlobalTheory.Core.Rk.SchLaws.sch_laws D ψ A B χ om hW ν 𝓨 hν φ hφ).1] at h
      exact h)
  simp only [integral_const_mul] at key
  have h' := hasSum_sch hψ A B hν hf' x y
  rw [hs] at h'
  have e := key.unique h'
  exact mul_left_cancel₀ (norm_ne_zero_iff.1 (by rw [hn]; exact one_ne_zero)) e

end GlobalTheory.RegSchProj

end
