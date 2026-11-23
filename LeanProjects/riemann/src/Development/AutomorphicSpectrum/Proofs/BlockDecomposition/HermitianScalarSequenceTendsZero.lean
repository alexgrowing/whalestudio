import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfMulUnimodular
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Path

variable {F : Type} [Field F] [NumberField F]

def invInf (F : Type) [Field F] [NumberField F] (n : ℕ) : Ainf F :=
  fun w => ((n : w.Completion) + 1)⁻¹

omit [NumberField F] in
theorem norm_natCast_add_one (w : NumberField.InfinitePlace F) (n : ℕ) :
    ‖((n : w.Completion) + 1)‖ = (n : ℝ) + 1 := by
  have h := (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
    (map_zero _) ((n : w.Completion) + 1)
  rw [← h, map_add, map_natCast, map_one]
  have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [this, Complex.norm_natCast]
  push_cast; ring

theorem natCast_add_one_ne_zero (w : NumberField.InfinitePlace F) (n : ℕ) :
    ((n : w.Completion) + 1) ≠ 0 := by
  intro h
  have := norm_natCast_add_one w n
  rw [h, norm_zero] at this
  have h2 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem mul_invInf (n : ℕ) : ((n : Ainf F) + 1) * invInf F n = 1 := by
  have key : ((n : ∀ w : NumberField.InfinitePlace F, w.Completion) + 1) *
      (fun w : NumberField.InfinitePlace F => ((n : w.Completion) + 1)⁻¹) = 1 := by
    funext w
    simp only [Pi.mul_apply, Pi.add_apply, Pi.natCast_apply, Pi.one_apply]
    exact mul_inv_cancel₀ (natCast_add_one_ne_zero w n)
  exact key

theorem tendsto_invInf : Filter.Tendsto (invInf F) Filter.atTop (nhds 0) := by
  refine tendsto_pi_nhds.2 fun w => ?_
  have key : Filter.Tendsto (fun n : ℕ => ((n : w.Completion) + 1)⁻¹) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have e : ∀ n : ℕ, ‖((n : w.Completion) + 1)⁻¹‖ = 1 / ((n : ℝ) + 1) := fun n => by
      rw [norm_inv, norm_natCast_add_one, one_div]
    simp only [e]
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  exact key

def seqA (F : Type) [Field F] [NumberField F] (n : ℕ) : AF F := pairA F (invInf F n) 0

theorem tendsto_seqA : Filter.Tendsto (seqA F) Filter.atTop (nhds 0) := by
  have : Filter.Tendsto (fun n => (invInf F n, (0 : Af F))) Filter.atTop (nhds ((0 : Ainf F), (0 : Af F))) :=
    tendsto_invInf.prodMk_nhds tendsto_const_nhds
  exact this

def seqE (D : D7) (r n : ℕ) : Mx D r r :=
  Matrix.diagonal fun _ => seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)

theorem seqE_mem (D : D7) (r n : ℕ) : seqE D r n ∈ hermA D r := by
  show GlobalTheory.MixModel.adj (seqE D r n) = seqE D r n
  ext i j
  by_cases h : i = j
  · subst h
    simp [GlobalTheory.MixModel.adj, seqE, sigR]
  · simp [GlobalTheory.MixModel.adj, seqE, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

theorem tendsto_seqE (D : D7) (r : ℕ) : Filter.Tendsto (seqE D r) Filter.atTop (nhds 0) := by
  have hc : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  have h1 : Filter.Tendsto (fun n => seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) Filter.atTop (nhds (0 : AE D)) := by
    have h2 : Filter.Tendsto (fun n => seqA D.host.F n • (1 : AE D)) Filter.atTop (nhds ((0 : AF D.host.F) • (1 : AE D))) :=
      tendsto_seqA.smul_const _
    rw [zero_smul] at h2
    refine h2.congr fun n => ?_
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  show Filter.Tendsto (fun n => seqE D r n i j) Filter.atTop (nhds (0 : AE D))
  by_cases h : i = j
  · subst h
    refine h1.congr fun n => ?_
    exact (Matrix.diagonal_apply_eq (fun _ => seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) i).symm
  · refine (tendsto_const_nhds (x := (0 : AE D))).congr fun n => ?_
    exact (Matrix.diagonal_apply_ne (fun _ => seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) h).symm

theorem theta_seqE (D : D7) (θ : InfFam D) (ρ : D.what₂.Tau) (n : ℕ) :
    θ ρ (infPart D (seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E))) = (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) := by
  have e1 : infPart D (seqA D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) = invInf D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  rw [e1]
  have e2 : (((n : Ainf D.host.F) + 1) ⊗ₜ[D.host.F] (1 : D.host.E)) * (invInf D.host.F n ⊗ₜ[D.host.F] (1 : D.host.E)) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_invInf, mul_one]; rfl
  have e3 : (((n : Ainf D.host.F) + 1) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      ((n : Ainf D.host.F ⊗[D.host.F] D.host.E) + 1) := by
    rw [TensorProduct.add_tmul, ← Algebra.TensorProduct.one_def]
    congr 1
  have e4 := congrArg (θ ρ) e2
  rw [e3, map_mul, map_add, map_natCast, map_one] at e4
  have hn : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp
  linear_combination e4

theorem exists_herm_seq : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ r : ℕ, ∃ e : ℕ → Mx D r r, (∀ n, e n ∈ hermA D r) ∧ Filter.Tendsto e Filter.atTop (nhds 0) ∧ ∀ (n : ℕ) (ρ : D.what₂.Tau), compAt θ ρ (e n) = (((1 : ℝ) / ((n : ℝ) + 1) : ℝ) : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) := by
  intro D θ _ r
  refine ⟨seqE D r, seqE_mem D r, tendsto_seqE D r, fun n ρ => ?_⟩
  ext i j
  by_cases h : i = j
  · subst h
    simp only [compAt, seqE, Matrix.map_apply, Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq]
    rw [theta_seqE]; simp
  · simp [compAt, seqE, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame.Path
