import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalFirst
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AddCharConductorInv

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.StdAddChar

theorem isStd_inv_and_trivial_and_nontrivial : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → IsStd χ⁻¹ ∧ (∀ x ∈ 𝒪[F], Circle.coeHom.compAddChar χ x = 1) ∧ ∃ x : F, (GLnLocal.uniformizer F : F) * x ∈ 𝒪[F] ∧ Circle.coeHom.compAddChar χ x ≠ 1 := by
  intro F _ _ _ _ _ _ χ hχ
  refine ⟨GlobalTheory.CompanionTheory.SphStd.isStd_inv hχ, GlobalTheory.CompanionTheory.SphOne.coe_eq_one_of_isStd hχ, ?_⟩
  have hnot := not_isTrivialOn_addCharConductor_sub_one hχ.1 hχ.2.1
  rw [hχ.2.2] at hnot
  unfold IsTrivialOn at hnot
  push_neg at hnot
  obtain ⟨x, hx, hx1⟩ := hnot
  have hϖ : (GLnLocal.uniformizer F : F) ∈ valBall F 1 :=
    mem_valBall_one_iff.2 (GLnLocal.valuation_uniformizer_lt_one F)
  refine ⟨x, ?_, ?_⟩
  · have h := mul_mem_valBall hϖ hx
    have h0 : (1 : ℤ) + (0 - 1) = 0 := by norm_num
    rw [h0] at h
    exact mem_valBall_zero_iff.1 h
  · intro h
    apply hx1
    have h' : ((χ x : Circle) : ℂ) = 1 := h
    exact Circle.ext (by simpa using h')

end GlobalTheory.CompanionTheory.StdAddChar
