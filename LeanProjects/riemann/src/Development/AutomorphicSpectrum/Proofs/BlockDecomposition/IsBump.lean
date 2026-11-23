import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG Topology
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

section Abs
variable {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]

def IsBump (H : Subgroup G) (ρ : Representation ℂ H W) (K : Subgroup G) (c : G) (v : W) (B : cIndSpace H ρ) : Prop :=
  (∀ (a : H), ∀ x ∈ K, B.1.1.1 ((a : G) * c * x) = ρ a v) ∧
    ∀ g, (¬ ∃ a : H, ∃ x ∈ K, g = (a : G) * c * x) → B.1.1.1 g = 0

end Abs

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def sO (i t : ℕ) : Mir k (i + (t + 1)) →* Mir k ((i + 1) + t + 1) :=
  (sEmb k ((i + 1) + t)).comp (castM k (by omega : i + (t + 1) = (i + 1) + t)).toMonoidHom

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end
