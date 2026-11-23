import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open GlobalTheory.Cartier

namespace GlobalTheory.PrimeOrd

theorem charZero_functionField {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} {D : ℕ} (h : IsArithVar p D) : CharZero X.functionField :=
  ((fnOf (⊤ : X.Opens) (TopologicalSpace.Opens.mem_top _)).charZero_iff
    (fnOf_injective ⊤ (TopologicalSpace.Opens.mem_top _))).1 h.charZero

theorem ord_natCast_nonneg {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] {l : ℕ}
    (hl : (l : X.functionField) ≠ 0) (z : X) : 0 ≤ Scheme.ord (l : X.functionField) z := by
  by_cases hz : Order.coheight z = 1
  · have e : (l : X.functionField) = algebraMap (X.presheaf.stalk z) X.functionField l :=
      (map_natCast _ l).symm
    have ha : (l : X.presheaf.stalk z) ≠ 0 := fun h0 => hl (by rw [e, h0, map_zero])
    rw [e, ord_algebraMap hz ha]
    exact Nat.cast_nonneg _
  · exact (Scheme.ord_eq_zero_of_coheight_neq_one hz _).ge

theorem ord_eq_zero_or_of_coprime {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    {l l' : ℕ} (h : l.Coprime l') (z : X) :
    Scheme.ord (l : X.functionField) z = 0 ∨ Scheme.ord (l' : X.functionField) z = 0 := by
  obtain ⟨u, v, huv⟩ : IsCoprime (l : X.presheaf.stalk z) (l' : X.presheaf.stalk z) :=
    h.cast
  have hu : IsUnit (u * (l : X.presheaf.stalk z) + v * (l' : X.presheaf.stalk z)) :=
    huv ▸ isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with h₁ | h₁
  · exact .inl (UnitAt.ord_eq_zero ⟨_, isUnit_of_mul_isUnit_right h₁, map_natCast _ l⟩)
  · exact .inr (UnitAt.ord_eq_zero ⟨_, isUnit_of_mul_isUnit_right h₁, map_natCast _ l'⟩)

theorem prime_ord : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ l : ℕ, l.Prime → (∀ z, 0 ≤ Scheme.ord ((l : X.functionField)) z) ∧ (Function.support fun z => Scheme.ord ((l : X.functionField)) z).Finite ∧ ∀ l' : ℕ, l'.Prime → l ≠ l' → ∀ z, Scheme.ord ((l : X.functionField)) z = 0 ∨ Scheme.ord ((l' : X.functionField)) z = 0 := by
  intro k _ X _ _ p D h l hl
  have := charZero_functionField h
  have := h.isNoetherian
  have h0 : (l : X.functionField) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  refine ⟨ord_natCast_nonneg h0, ?_, fun l' hl' hne z =>
    ord_eq_zero_or_of_coprime ((Nat.coprime_primes hl hl').2 hne) z⟩
  refine (CartierDiv.principal (Units.mk0 _ h0)).finite_support_mult.subset fun z hz h₁ => hz ?_
  rwa [(CartierDiv.isEqn_principal _ z).mult_eq, Units.val_mk0] at h₁

end GlobalTheory.PrimeOrd
