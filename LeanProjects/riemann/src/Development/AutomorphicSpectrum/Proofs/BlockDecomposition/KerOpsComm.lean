import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SumNegOnePowFinrankEqZero
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

namespace GlobalTheory.CompanionTheory.GE.UV

variable {X : Scheme.{0}} {k : ℕ} (M : ℕ → X.Modules) (T : Fin (k + 1) → ∀ e, M e ⟶ M (e + 1))

def kerSeq (e : ℕ) : X.Modules := kernel (T (Fin.last k) e)

def cokSeq (e : ℕ) : X.Modules := cokernel (T (Fin.last k) e)

variable {M T}

def kerOps (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (i : Fin k) (e : ℕ) :
    kerSeq M T e ⟶ kerSeq M T (e + 1) :=
  kernel.map (T (Fin.last k) e) (T (Fin.last k) (e + 1)) (T i.castSucc e) (T i.castSucc (e + 1))
    (hc _ _ e)

def cokOps (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (i : Fin k) (e : ℕ) :
    cokSeq M T e ⟶ cokSeq M T (e + 1) :=
  cokernel.map (T (Fin.last k) e) (T (Fin.last k) (e + 1)) (T i.castSucc e) (T i.castSucc (e + 1))
    (hc _ _ e)

theorem kerOps_comm (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (i j : Fin k) (e : ℕ) :
    kerOps hc i e ≫ kerOps hc j (e + 1) = kerOps hc j e ≫ kerOps hc i (e + 1) := by
  dsimp only [kerOps, kerSeq]
  apply equalizer.hom_ext
  simp only [kernel.map, Category.assoc, kernel.lift_ι, kernel.lift_ι_assoc]
  rw [hc i.castSucc j.castSucc e]

theorem cokOps_comm (hc : ∀ i j e, T i e ≫ T j (e + 1) = T j e ≫ T i (e + 1)) (i j : Fin k) (e : ℕ) :
    cokOps hc i e ≫ cokOps hc j (e + 1) = cokOps hc j e ≫ cokOps hc i (e + 1) := by
  dsimp only [cokOps, cokSeq]
  apply coequalizer.hom_ext
  simp only [cokernel.map, Category.assoc, cokernel.π_desc, cokernel.π_desc_assoc]
  simp only [← Category.assoc, hc i.castSucc j.castSucc (e + 1)]

end GlobalTheory.CompanionTheory.GE.UV
