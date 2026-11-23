import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardFrameOfDiagonalStages
open NumberField IsDedekindDomain Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Mem.Col2.PinsCoord

def PinsP (B : Pre) (pi : B.Word → 𝓞 B.host.E) : Prop :=
  (∀ (a : Fin B.sp.X'.rank) (b : Fin (B.sp.X B.R.m).rank), (a : ℕ) = b →
    B.sp.iX' (B.sp.X'.frame a) = (B.sp.X B.R.m).frame b) ∧ ∀ u, B.cOf u * (pi u : B.host.E) = (pi B.u₀ : B.host.E)

theorem extTo_basis {E : Type} [Field E] (n N : ℕ) (a : Fin n) (b : Fin N) (h : (a:ℕ) = b) : DiagSp.extTo (E := E) n N (Pi.basisFun E (Fin n) a) = Pi.basisFun E (Fin N) b := by
  funext i
  simp only [Pi.basisFun_apply]
  show (if h : (i:ℕ) < n then (Pi.single a (1:E) : Fin n → E) ⟨i, h⟩ else 0) = _
  by_cases e : i = b
  · subst e
    have : (i:ℕ) < n := h ▸ a.2
    rw [dif_pos this, show (⟨i, this⟩ : Fin n) = a from Fin.ext h.symm]; simp
  · rw [Pi.single_eq_of_ne e]
    split_ifs with h1
    · exact Pi.single_eq_of_ne (fun e' => e (Fin.ext (by rw [← h, ← e']))) _
    · rfl

end GlobalTheory.Mem.Col2.PinsCoord
