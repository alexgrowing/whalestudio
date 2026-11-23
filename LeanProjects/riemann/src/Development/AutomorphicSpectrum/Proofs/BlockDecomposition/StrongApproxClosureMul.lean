import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

theorem SAQ_mul_mem {F : Type} [Field F] [NumberField F] {d β : F} {s : Pl F}
    {x y : Q d β (AF F)} (hx : x ∈ SAQ d β s) (hy : y ∈ SAQ d β s) : x * y ∈ SAQ d β s := by
  obtain ⟨γ, hγ, h, hh, rfl⟩ := hx
  obtain ⟨γ', hγ', h', hh', rfl⟩ := hy
  have hq : qn (rat γ' : Q d β (AF F)) = 1 := by
    have := qn_qmap (Algebra.ofId F (AF F)) γ'
    rw [hγ', map_one] at this
    exact this
  have hs : star (rat γ' : Q d β (AF F)) * rat γ' = 1 := by
    rw [star_mul_eq, hq, map_one]
  have hs' : (rat γ' : Q d β (AF F)) * star (rat γ') = 1 := by
    rw [mul_star_eq, hq, map_one]
  refine ⟨γ * γ', ?_, star (rat γ') * h * rat γ' * h', ⟨?_, ?_⟩, ?_⟩
  · rw [show qn (γ * γ') = qn γ * qn γ' from qn_mul γ γ', hγ, hγ', one_mul]
  · rw [qn_mul, qn_mul, qn_mul, qn_star, hq, hh.1, hh'.1]
    simp
  · intro u hu
    have e1 := hh.2 u hu
    have e2 := hh'.2 u hu
    rw [map_mul, map_mul, map_mul, e1, e2, mul_one, mul_one, ← map_mul, hs, map_one]
  · rw [map_mul]
    have : (rat γ : Q d β (AF F)) * rat γ' * (star (rat γ') * h * rat γ' * h') =
        rat γ * (rat γ' * star (rat γ')) * h * rat γ' * h' := by
      simp only [mul_assoc]
    rw [this, hs', mul_one]
    simp only [mul_assoc]

theorem closure_SAQ_mul : ∀ {F : Type} [Field F] [NumberField F] (d β : F) (s : Pl F),
    ∀ x ∈ closure (SAQ d β s), ∀ y ∈ closure (SAQ d β s), x * y ∈ closure (SAQ d β s) := by
  intro F _ _ d β s x hx y hy
  exact map_mem_closure₂ continuous_mul hx hy fun a ha b hb => SAQ_mul_mem ha hb

end GlobalTheory.CompanionTheory.PlaneSA
