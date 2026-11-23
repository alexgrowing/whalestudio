import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL Matrix

namespace GlobalTheory.WhitHered

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def unipLevi {c : ℕ} (m : Fin c → ℕ) : Subgroup (Levi k fun a => Fin (m a)) :=
  Subgroup.pi Set.univ fun a => unipB k (Fin (m a))

variable {k}

def unipLeviProj {c : ℕ} (m : Fin c → ℕ) (a : Fin c) : unipLevi k m →* unipB k (Fin (m a)) :=
  ((Pi.evalMonoidHom (fun b => GL (Fin (m b)) k) a).comp (unipLevi k m).subtype).codRestrict _
    fun u => u.2 a (Set.mem_univ a)

def whitLevi (ψ : AddChar k Circle) {c : ℕ} (m : Fin c → ℕ) : unipLevi k m →* ℂˣ :=
  ∏ a, (GlobalTheory.LocGL.whitChar ψ (m a)).comp (unipLeviProj m a)

variable {N c : ℕ} {m : Fin c → ℕ}

def blockColRank (e : (Σ a, Fin (m a)) ≃ Fin N) (g : GL (Fin N) k) (a : Fin c) (j : Fin N) : ℕ :=
  ((g : Matrix (Fin N) (Fin N) k).submatrix (fun i : {i : Fin N // a ≤ blk e i} => i.1)
    (fun j' : {j' : Fin N // j' ≤ j} => j'.1)).rank

def cellHt (e : (Σ a, Fin (m a)) ≃ Fin N) (g : GL (Fin N) k) : ℕ :=
  ∑ a, ∑ j, blockColRank e g a j

def cellHtMax (e : (Σ a, Fin (m a)) ≃ Fin N) : ℕ :=
  ∑ a : Fin c, ∑ j : Fin N, min (Fintype.card {i : Fin N // a ≤ blk e i}) ((j : ℕ) + 1)

end GlobalTheory.WhitHered

end
