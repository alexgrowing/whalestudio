import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.TameIwahori

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsIwVec {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (θ : Fin n → kˣ →* ℂˣ)
    (π : Representation ℂ (GL (Fin n) k) V) (v : V) : Prop :=
  (∀ h ∈ KO k (Fin n), (∀ i j, j < i → valuation k (h.val i j) < 1) →
    (∀ i, valuation k (h.val i i - 1) < 1) → π h v = v) ∧
  ∀ t ∈ torusO k (Fin n), π (diagT k (Fin n) t) v = (torusChar θ t : ℂ) • v

end GlobalTheory.TameIwahori
