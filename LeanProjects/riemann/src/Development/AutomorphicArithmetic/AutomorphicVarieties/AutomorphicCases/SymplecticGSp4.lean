import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CongruenceNumberRankThree

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.Top

namespace UpperTheory.V.Aut

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

structure OfChar (D : Raw Ω c) (e : ℕ) {N : ℕ} [NeZero N] (ψ : DirichletCharacter c.O N) (n' p₁ m₀ : ℕ) : Prop where
  e_eq : D.e = e
  psi : D.ψ = Chr.dirG ℚ Ω ψ
  S_eq : D.S = (2 * l * N * p₁).primeFactors
  xi : ∃ (_ : NeZero p₁) (ξ' : DirichletCharacter c.O (2 ^ n')) (ξ₀ : DirichletCharacter c.O p₁), ξ'.IsPrimitive ∧ ξ' (-1) = -1 ∧
    orderOf ξ₀ = m₀ ∧ D.ξ = Chr.dirG ℚ Ω ξ₀ * Chr.dirG ℚ Ω ξ'

def OfCase (D : Raw Ω c) (h : Host) (e : ℕ) (ψ : DirichletCharacter c.O h.N) : Prop :=
  (h.CaseII l e ψ ∧ OfChar D e ψ (h.nII l ψ) 1 1) ∨ (h.CaseIII l e ψ ∧ OfChar D e ψ (h.nIII l ψ) (pOne h.chi) (orderOf ψ))

def IsAut4 (ι : PadicAlgCl l ≃+* ℂ) (r : G ℚ Ω →* M4 (PadicAlgCl l)) : Prop := Af.IsAutQ ι r.toHomUnits

def Sp4In : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (h : Host) (t : ℕ), h.Big t →
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ), l ≠ 2 → 0 < e → e < t → ∀ ψ ∈ h.X c e, ∀ D : Raw Ω c, D.Good → OfCase D h e ψ →
      D.Fin0 ∧ D.NoEnd ∧ ∃ ι : PadicAlgCl l ≃+* ℂ, D.AllIrr (IsAut4 ι)

end UpperTheory.V.Aut

end
