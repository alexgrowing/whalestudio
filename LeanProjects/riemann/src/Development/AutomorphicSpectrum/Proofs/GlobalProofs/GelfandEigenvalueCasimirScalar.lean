import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CapelliLowestGelfandConj

noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.CompanionTheory.DerGlRel

private theorem commutator_eq_of_glRel {M : Type*} [AddCommGroup M] [Module ℂ M] {n : ℕ}
    (L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ M)
    (hL : Formalism.REAL.GlRel fun a b : Fin n => L (Matrix.single a b 1))
    (Z W : Matrix (Fin n) (Fin n) ℂ) :
    L Z * L W - L W * L Z = L (Z * W - W * Z) := by
  classical
  have hs : ∀ (i j : Fin n) (x : ℂ),
      (Matrix.single i j x : Matrix (Fin n) (Fin n) ℂ) = x • Matrix.single i j 1 := by
    intro i j x
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  have base : ∀ a b c d : Fin n,
      L (Matrix.single a b 1) * L (Matrix.single c d 1) -
          L (Matrix.single c d 1) * L (Matrix.single a b 1) =
        L (Matrix.single a b 1 * Matrix.single c d 1 -
          Matrix.single c d 1 * Matrix.single a b 1) := by
    intro a b c d
    have h := hL a b c d
    simp only at h
    rw [h, map_sub]
    congr 1
    · by_cases h' : b = c
      · subst h'
        rw [if_pos rfl, Matrix.single_mul_single_same, mul_one]
      · rw [if_neg h']
        simp [Matrix.single_mul_single_of_ne, h']
    · by_cases h' : d = a
      · subst h'
        rw [if_pos rfl, Matrix.single_mul_single_same, mul_one]
      · rw [if_neg h']
        simp [Matrix.single_mul_single_of_ne, h']
  have key1 : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n),
      L Z * L (Matrix.single c d 1) - L (Matrix.single c d 1) * L Z =
        L (Z * Matrix.single c d 1 - Matrix.single c d 1 * Z) := by
    intro Z c d
    refine Matrix.induction_on' Z ?_ ?_ ?_
    · simp
    · intro p q hp hq
      rw [show (p + q) * Matrix.single c d 1 - Matrix.single c d 1 * (p + q) =
          (p * Matrix.single c d 1 - Matrix.single c d 1 * p) +
            (q * Matrix.single c d 1 - Matrix.single c d 1 * q) by noncomm_ring]
      simp only [map_add]
      rw [← hp, ← hq]
      noncomm_ring
    · intro i j x
      rw [hs i j x]
      simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, map_smul, base]
  refine Matrix.induction_on' W ?_ ?_ ?_
  · simp
  · intro p q hp hq
    rw [show Z * (p + q) - (p + q) * Z = (Z * p - p * Z) + (Z * q - q * Z) by noncomm_ring]
    simp only [map_add]
    rw [← hp, ← hq]
    noncomm_ring
  · intro i j x
    rw [hs i j x]
    simp only [smul_mul_assoc, mul_smul_comm, ← smul_sub, map_smul, key1]

theorem glRel_derEnd_family : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    (M : Fin V.rank → Fin V.rank → Matrix (Fin V.rank) (Fin V.rank) ℂ), Formalism.REAL.GlRel M →
    Formalism.REAL.GlRel (fun i j => GlobalTheory.Mem.RealTranslate.derEnd hθ τ (M i j)) := by
  intro D θ hθ V τ M hM
  unfold Formalism.REAL.GlRel at hM ⊢
  dsimp only at hM ⊢
  intro a b c d
  have h1 := commutator_eq_of_glRel (GlobalTheory.Mem.RealTranslate.derEnd (V := V) hθ τ)
    (GlobalTheory.Mem.Lift.glRel_derEnd hθ V τ) (M a b) (M c d)
  rw [h1, hM a b c d, map_sub]
  split_ifs <;> simp

end GlobalTheory.CompanionTheory.DerGlRel

end
