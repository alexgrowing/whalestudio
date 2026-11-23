import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceInnerMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulas
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisCovar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.RdEc

variable {D : D7}

theorem translate_mem (θ : InfFam D) {m n : ℕ} (x : Mx D m n) {φ : Mx D m n → ℂ} (hφ : φ ∈ schwartzA θ m n) :
    (fun z => φ (z + x)) ∈ schwartzA θ m n := by
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := Af D.host.F)
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    refine Submodule.subset_span ⟨SchwartzMap.compSubConstCLM ℂ (-(fun τ i j => compAt θ τ x i j)) f,
      fun u => g (u + fun i j => finPart D (x i j)), ⟨?_, ?_⟩, ?_⟩
    · exact hg.1.comp_continuous (continuous_add_const _)
    · exact hg.2.comp_homeomorph (Homeomorph.addRight _)
    · funext z
      rw [SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
      beta_reduce
      congr 2
      · funext τ i j
        exact (congrArg (θ τ) ((infPart D).map_add (z i j) (x i j))).trans ((θ τ).map_add _ _)
      · funext i j
        exact (finPart D).map_add (z i j) (x i j)
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul c a _ ha => exact Submodule.smul_mem _ c ha

theorem quad_mem {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D)
    {n : ℕ} (b : Mx D n n) (hb : adj b = b) {φ : Mx D V.rank n → ℂ} (hφ : φ ∈ schwartzA θ V.rank n) :
    (fun z => ψ (halfTr (Matrix.trace (b * GlobalTheory.StdUnn.inner V z z))) * φ z) ∈ schwartzA θ V.rank n := by
  obtain ⟨ψ₀, h₀, lam, hlam, hψeq⟩ := GlobalTheory.ThetaAllChar.exists_std hψ
  have hsh : ψ = shift ψ₀ lam := by
    ext x
    rw [hψeq]
    rfl
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne D V.rank n
  obtain ⟨χ, h1, h2⟩ := GlobalTheory.RawLift.exists_hecke_resEta D V.rank
  obtain ⟨ω, hω⟩ := GlobalTheory.StdUnn.Inhab.weil_exists D n V ψ₀ h₀ lam hlam χ h1 h2 θ hθ μ 𝓕 hμ
  rw [← hsh] at hω
  obtain ⟨g, hg⟩ := (GlobalTheory.StdUnn.Model.exists_unip b).2 hb
  have := (ω g ⟨φ, hφ⟩).2
  rwa [show (ω g ⟨φ, hφ⟩).1 = _ from funext (hω.unip g b hg ⟨φ, hφ⟩)] at this

theorem heisSch : HeisSch := by
  intro D ψ hψ θ hθ V n v Φ hΦ
  have h1 := translate_mem θ (xPart v) hΦ
  have h2 := quad_mem hψ hθ V (-1) (by simp [adj_neg, adj_one]) h1
  have h3 := translate_mem θ (-yPart v) h2
  have h4 := quad_mem hψ hθ V 1 adj_one h3
  have h5 := translate_mem θ (yPart v) h4
  have h6 := Submodule.smul_mem _ (ψ (halfTr (Matrix.trace (GlobalTheory.StdUnn.inner V (xPart v) (yPart v))) -
    halfTr (Matrix.trace (GlobalTheory.StdUnn.inner V (yPart v) (yPart v))))) h5
  convert h6 using 1
  funext z
  simp only [EC.Heisenberg₂, Pi.smul_apply, smul_eq_mul, add_neg_cancel_right]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul,
    Unip.quad_shift V adj_one z (yPart v)]
  congr 2
  simp only [Matrix.mul_one, Matrix.one_mul, Matrix.neg_mul, Matrix.trace_neg, halfTr, map_neg, mul_neg]
  abel

end PositivityTheory.RdEc
