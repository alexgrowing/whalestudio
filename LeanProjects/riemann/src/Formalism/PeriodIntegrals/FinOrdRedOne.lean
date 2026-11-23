import Mathlib

noncomputable section

namespace PI.FinOrdRedOne

open NumberField IsDedekindDomain Ideal

abbrev OP (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : Type :=
  P.adicCompletionIntegers E

def red {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {N : ℕ}
    (M : Matrix (Fin N) (Fin N) (OP E P)) :
    Matrix (Fin N) (Fin N) (IsLocalRing.ResidueField (OP E P)) :=
  M.map (IsLocalRing.residue (OP E P))

def Unram (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  ∀ (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})], Q.ramificationIdx ℤ = 1

end PI.FinOrdRedOne

namespace PI

open NumberField IsDedekindDomain Ideal PI.FinOrdRedOne

def FinOrdRedOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → 3 ≤ p → Unram E p →
  ∀ (P : HeightOneSpectrum (𝓞 E)), (p : 𝓞 E) ∈ P.asIdeal →
  ∀ (N : ℕ) (β : GL (Fin N) (OP E P)), IsOfFinOrder β →
    red (β : Matrix (Fin N) (Fin N) (OP E P)) = 1 → β = 1

end PI
