import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtensionAdeleRealComponentsCmType
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniqueAdelicMatrixRealComponentsFinitePart
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ExistsBaseRingOfConjugationFixedTensor
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.RealPar

variable {D : D7}

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

theorem finPart_cA_eq (z : AE D) :
    finPart D (cA D z) = Algebra.TensorProduct.map (AlgHom.id D.host.F (Af D.host.F)) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, sigR, finPart]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb, map_add]

open Classical in

theorem exists_real_point {θ : InfFam D} (hθ : IsInfFam θ) (τ₀ : D.what₂.Tau) (t : ℝ) :
    ∃ x : Ainf D.host.F, ∀ τ, θ τ (x ⊗ₜ[D.host.F] (1 : D.host.E)) = if τ = τ₀ then (t : ℂ) else 0 := by
  obtain ⟨w, ⟨hw, hf⟩, -⟩ := exists_unique_of_comp_finPart D θ hθ 1 1
    (fun τ => fun _ _ => if τ = τ₀ then (t : ℂ) else 0) 0
  set a : AE D := w 0 0 with ha
  have hcomp : ∀ τ, θ τ (infPart D a) = if τ = τ₀ then (t : ℂ) else 0 := fun τ => by
    have := congrFun (congrFun (hw τ) 0) 0
    simpa [compAt] using this
  have hfin : finPart D a = 0 := by
    have := congrFun (congrFun hf 0) 0
    rw [Matrix.map_apply, Matrix.map_apply, Matrix.zero_apply, map_zero] at this
    exact this
  have hRC := RealComp.real_components D θ hθ
  have hc : cA D a = a := by
    have h0 : cA D a - a = 0 := by
      apply hRC.2.2.2
      · intro τ
        rw [map_sub, map_sub, hRC.2.1 a τ, hcomp τ]
        split_ifs <;> simp
      · rw [map_sub, finPart_cA_eq, hfin]
        simp
    exact sub_eq_zero.mp h0
  obtain ⟨y, hy⟩ := GlobalTheory.DetRootRows.fixed_mem_range a hc
  refine ⟨fstA D.host.F y, fun τ => ?_⟩
  rw [← hcomp τ, ← hy]
  rfl

theorem realPar_unique : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ l l' : D.what₂.Tau → ℝ, HasRealPar ψ θ l → HasRealPar ψ θ l' → l = l' := by
  classical
  intro D ψ θ hθ l l' hl hl'
  funext τ₀
  by_contra hne
  have hd : l τ₀ - l' τ₀ ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨x, hx⟩ := exists_real_point hθ τ₀ (1 / (2 * (l τ₀ - l' τ₀)))
  have e := (hl x).symm.trans (hl' x)
  simp only [hx, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp e
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have h1 : ((l τ₀ : ℂ) - l' τ₀) * ((1 / (2 * (l τ₀ - l' τ₀)) : ℝ) : ℂ) = n := by
    apply mul_left_cancel₀ hpi
    linear_combination hn
  have h2 : ((l τ₀ : ℂ) - l' τ₀) * ((1 / (2 * (l τ₀ - l' τ₀)) : ℝ) : ℂ) = 1 / 2 := by
    have hd' : ((l τ₀ : ℂ) - l' τ₀) ≠ 0 := by exact_mod_cast hd
    push_cast
    field_simp
  rw [h2] at h1
  have h3 : ((n : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; exact h1.symm
  have h4 : (n : ℝ) = 1 / 2 := by exact_mod_cast h3
  have h5 : (2 : ℝ) * n = 1 := by rw [h4]; norm_num
  have h6 : (2 : ℤ) * n = 1 := by exact_mod_cast h5
  omega

end GlobalTheory.StdUnn.RealPar
