import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFacts

open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SphOne

theorem coe_eq_one_of_isStd {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {ψ : AddChar F Circle} (hψ : IsStd ψ) :
    ∀ x ∈ 𝒪[F], (Circle.coeHom.compAddChar ψ) x = 1 := by
  intro x hx
  have h := isTrivialOn_addCharConductor hψ.1 hψ.2.1
  rw [hψ.2.2] at h
  have h1 : ψ x = 1 := h x (mem_valBall_zero_iff.2 hx)
  show ((ψ x : Circle) : ℂ) = 1
  rw [h1, Circle.coe_one]

end GlobalTheory.CompanionTheory.SphOne
