import Mathlib

open ValuativeRel

namespace PI

def HenselStrong : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (f : Polynomial 𝒪[F]) (a : 𝒪[F]),
    valuation F ((f.eval a : 𝒪[F]) : F) < valuation F ((f.derivative.eval a : 𝒪[F]) : F) ^ 2 →
    ∃ b : 𝒪[F], f.eval b = 0 ∧
      valuation F (((b - a : 𝒪[F])) : F) < valuation F ((f.derivative.eval a : 𝒪[F]) : F)

end PI
