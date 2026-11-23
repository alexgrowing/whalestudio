import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelIntG
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaLatticeImageRationalHomLattice

noncomputable section

open NumberField

namespace GlobalTheory.VacRead

def cE (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E) {x | ∃ c ∈ cc, x = ((c : D.host.K) : D.host.E)}

def bInv (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E) {y | ∃ α ∈ cE D cc, ∃ γ ∈ cE D D.host.ccK,
    y = r * D.host.conj α * γ / (Ideal.absNorm cc : D.host.E)}

def lsB (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a : ℕ) : GlobalTheory.InertSign.Lat D a :=
  Submodule.pi Set.univ fun _ => bInv D cc r

theorem mem_lsB {D : Formalism.BasicNotions.D7} {cc : Ideal (𝓞 D.host.K)} {r : D.host.E} {a : ℕ} {y : Fin a → D.host.E} :
    y ∈ lsB D cc r a ↔ ∀ i, y i ∈ bInv D cc r := by
  simp [lsB, Submodule.mem_pi]

end GlobalTheory.VacRead
