import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.wtDegConst_of :
    PtEx → WtDegConst := by
  intro _ Z S p _ _ w hw
  obtain ⟨ψ, hψ, hsum⟩ := hw (Sq.self p) (fun _ => 1) (IsLocallyConstant.const 1)
  have hψ' : IsLocallyConstant (fun s : S => ψ s) := hψ
  by_cases hS : Nonempty S
  · obtain ⟨s₀⟩ := hS
    refine ⟨ψ s₀, ?_⟩
    funext Ω _ _ x
    have h : ψ (pt x) = ∑ᶠ (z : gp Ω ⟶ Z) (_ : z ∈ fib p x), w Ω (z ≫ 𝟙 Z) * 1 := hsum Ω x
    simp only [Category.comp_id, mul_one] at h
    show (∑ᶠ (z : gp Ω ⟶ Z) (_ : z ∈ fib p x), w Ω z) = ψ s₀
    have hc : ψ (pt x) = ψ s₀ := hψ'.apply_eq_of_preconnectedSpace (pt x) s₀
    rw [← hc]
    exact h.symm
  · refine ⟨0, ?_⟩
    funext Ω _ _ x
    exact (hS ⟨pt x⟩).elim
