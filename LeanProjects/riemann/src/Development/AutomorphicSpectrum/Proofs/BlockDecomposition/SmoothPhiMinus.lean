import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsSmoothTwAct
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.VectorStabilizer

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.BZMir.Fun

namespace GlobalTheory.CompanionTheory.BZMirSmooth

section General

variable {G M V : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V]

noncomputable def vecStab {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ M X) (x : X) : Subgroup M :=
  _root_.UpperTheory.Reformulated.B.VectorStabilizer.vecStab ρ x

theorem isSmooth_twAct [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M]
    (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n)
    (hc : Continuous s) (hρ : IsSmooth ρ) : IsSmooth (twAct ρ N θ s hs) :=
  _root_.UpperTheory.Reformulated.B.Gwa2.isSmooth_twAct ρ N θ s hs hc hρ

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_glEmbHom (n : ℕ) : Continuous (glEmbHom k n) := by
  refine continuous_matrix fun i j => ?_
  show Continuous fun A : Matrix (Fin n) (Fin n) k => glEmbMat k n A i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simpa [glEmbMat] using continuous_const
    | cast j => simpa [glEmbMat] using continuous_const
  | cast i =>
    induction j using Fin.lastCases with
    | last => simpa [glEmbMat] using continuous_const
    | cast j =>
      simpa [glEmbMat] using (continuous_id.matrix_elem i j)

theorem continuous_glEmb (n : ℕ) : Continuous (glEmb k n) :=
  Continuous.units_map _ (continuous_glEmbHom n)

theorem continuous_levi (n : ℕ) : Continuous (levi k n) :=
  (continuous_glEmb n).subtype_mk _

theorem smPhiMinus (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    SmPhiMinus k := by
  intro ψ n V _ _ τ hτ
  exact isSmooth_twAct τ (MirUin k (n + 1)) (mirChar k ψ n) ((levi k (n + 1)).comp (Mir k n).subtype) (levi_stab ψ n)
    ((continuous_levi (n + 1)).comp continuous_subtype_val) hτ

end GlobalTheory.CompanionTheory.BZMirSmooth

end
