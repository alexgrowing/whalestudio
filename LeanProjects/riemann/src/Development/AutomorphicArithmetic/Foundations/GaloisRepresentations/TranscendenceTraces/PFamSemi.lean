import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.famSemi_of :
    FamSemi := by
  intro Z S p R₁ R₂ R₃ _ _ _ I J K
  refine ⟨fun τ ρ => ?_, fun ρ τ => ?_⟩
  · refine ⟨⟨fun s => ⟨fun A => (ρ.app A.U s).comp ((τ.deg s).app A), ?_⟩, ?_⟩, fun _ _ _ => rfl⟩
    · intro A B t a
      change Sec.res t.g (ρ.app B.U s ((τ.deg s).app B a)) = ρ.app A.U s ((τ.deg s).app A (Sec.res t.k a))
      rw [ρ.nat t.g s, (τ.deg s).nat t a]
    · intro A s t a
      change Sec.map (K.d s t) (ρ.app A.U s ((τ.deg s).app A a)) =
        ρ.app A.U t ((τ.deg t).app A (Sec.map (I.d s t) a))
      rw [ρ.comm A.U s t, τ.comm A s t a]
  · refine ⟨⟨fun s => ⟨fun A => ((τ.deg s).app A).comp (ρ.app A.V s), ?_⟩, ?_⟩, fun _ _ _ => rfl⟩
    · intro A B t a
      change Sec.res t.g ((τ.deg s).app B (ρ.app B.V s a)) = (τ.deg s).app A (ρ.app A.V s (Sec.res t.k a))
      rw [(τ.deg s).nat t, ρ.nat t.k s]
    · intro A s t a
      change Sec.map (K.d s t) ((τ.deg s).app A (ρ.app A.V s a)) =
        (τ.deg t).app A (ρ.app A.V t (Sec.map (I.d s t) a))
      rw [τ.comm A s t, ρ.comm A.V s t]
