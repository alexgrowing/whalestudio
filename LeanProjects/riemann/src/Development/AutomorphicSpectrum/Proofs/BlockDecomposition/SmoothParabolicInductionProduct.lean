import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EGPgTrueEqLastIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.BZRes

theorem isSmooth_sQ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {r t N : ℕ} (h : r + t = N)
    (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W)
    (h₁ : IsSmooth π₁) (h₂ : IsSmooth π₂) : IsSmooth (sQ h π₁ π₂) := by
  unfold GlobalTheory.CompanionTheory.BZRes.sQ
  refine GlobalTheory.SmGL.isSmooth_comp ?_ _
    (GlobalTheory.SmGL.ProdIrr.continuous_leviProj _)
  refine GlobalTheory.SmGL.isSmooth_twist ?_
    (GlobalTheory.SmGL.isSmoothChar_deltaHalf k)
  refine GlobalTheory.SmGL.isSmooth_piTensor ?_
  intro x
  cases x
  · exact h₁
  · exact h₂

end GlobalTheory.CompanionTheory.BZRes
end
