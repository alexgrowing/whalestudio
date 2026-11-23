import Development.WeilBound.ThetaLifts.SphericalLattices.LocModSt

noncomputable section

namespace PositivityTheory.Sph.M2

open Matrix Formalism.UG GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

def LocCommSt : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (c : L →+* L) (q : ℕ), IsUnramInv ϖ c q →
    ∀ (m : ℕ), ∀ p ∈ PW L c m,
      ((KPW L c m).map (MulAut.conj p).toMonoidHom).relIndex (KPW L c m) ≠ 0 ∧
        (KPW L c m).relIndex ((KPW L c m).map (MulAut.conj p).toMonoidHom) ≠ 0

def ZCountSt : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (c : L →+* L) (q : ℕ), IsUnramInv ϖ c q →
    ∀ (m : ℕ) (x : Lˣ), (x : L) = ϖ →
      (KPW L c m).map (MulAut.conj (zW L m x)).toMonoidHom ≤ KPW L c m ∧
        ((KPW L c m).map (MulAut.conj (zW L m x)).toMonoidHom).relIndex (KPW L c m) = q ^ (2 * m * m)

def GenSt : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (c : L →+* L) (q : ℕ), IsUnramInv ϖ c q →
    ∀ (m : ℕ) (χ : GL (Fin m ⊕ Fin m) L → ℝ), (∀ a ∈ PW L c m, ∀ b ∈ PW L c m, χ (a * b) = χ a * χ b) →
      (∀ a ∈ PW L c m, 0 < χ a) → (∀ k ∈ KPW L c m, χ k = 1) → (∀ x : Lˣ, (x : L) = ϖ → χ (zW L m x) = 1) →
      ∀ a ∈ PW L c m, χ a = 1

end PositivityTheory.Sph.M2

end
