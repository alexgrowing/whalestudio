import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp

set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra

namespace GlobalTheory.PDiv

def frobKerIdeal (p : ℕ) (R H : Type) [CommRing R] [CommRing H] [Bialgebra R H] : Ideal H :=
  Ideal.span ((fun a : H => a ^ p) '' (augIdeal R H : Set H))

theorem pow_mem_frobKerIdeal {p : ℕ} {R H : Type} [CommRing R] [CommRing H] [Bialgebra R H] {a : H}
    (ha : a ∈ augIdeal R H) : a ^ p ∈ frobKerIdeal p R H :=
  Ideal.subset_span ⟨a, ha, rfl⟩

theorem frobKerIdeal_le_augIdeal {p : ℕ} (hp : p ≠ 0) (R H : Type) [CommRing R] [CommRing H]
    [Bialgebra R H] : frobKerIdeal p R H ≤ augIdeal R H :=
  Ideal.span_le.2 fun _ ⟨a, ha, e⟩ => e ▸ Ideal.pow_mem_of_mem _ ha p (Nat.pos_of_ne_zero hp)

end GlobalTheory.PDiv
