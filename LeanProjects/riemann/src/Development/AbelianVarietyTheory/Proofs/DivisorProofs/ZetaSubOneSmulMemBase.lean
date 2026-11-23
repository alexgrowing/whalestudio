import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff

set_option autoImplicit false

open CategoryTheory WittVector GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published GlobalTheory.PerfdLat
open scoped ChangeOfRings Pointwise

namespace GlobalTheory.PerfdLat

theorem zeta_sub_one_smul_mem_base (p : ℕ) [Fact p.Prime] (D : PrismData p) (S : CycPerfd p) (G : PDivGroup p S.R)
    (c : ConstTate (eps S) G) : ∀ n, ∀ x ∈ H D c n, (zeta S.ε (n + 1) - 1) • x ∈ base S G.height := fun n x hx => by
  obtain ⟨k, -, h⟩ := (mem_H D c n x).1 hx
  exact (mem_base S _).2 ⟨_, h⟩

end GlobalTheory.PerfdLat
