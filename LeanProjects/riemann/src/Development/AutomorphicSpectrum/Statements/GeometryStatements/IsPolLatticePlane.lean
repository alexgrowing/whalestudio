import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OmStable
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NonemptyLinearEquivOfPiFinPowFinite
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi

def IsPointOf {C O : Type} [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
    {c : E ≃+* E} {κ : O} {N : ℕ} {La : Type} [AddCommGroup La] [Module (𝓞 E) La]
    {L : Type} [AddCommGroup L] [Module O L] (p : ℕ)
    (der : ∀ n, (LevGrp La p n → O) → Module.Dual O L → Prop) (EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : ℕ → Oˣ)
    (ρL : 𝓞 E →+* Module.End O L) (u : Fin N → La)
    (P : HTPoint C O c κ N (C ⊗[ℤ] La) (C ⊗[O] Module.Dual O L)) : Prop :=
  (∀ i, P.t i = 1 ⊗ₜ u i) ∧ (∀ (a : 𝓞 E) (x : La), P.ρ a (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) ∧
  (∀ x y : La, P.e (1 ⊗ₜ x) (1 ⊗ₜ y) = (EF x y : C)) ∧
  P.om = LinearMap.range (TensorProduct.mk O C (Module.Dual O L) 1) ∧
  (∀ (a : 𝓞 E) (w : Module.Dual O L),
    P.ρΩ a (1 ⊗ₜ w) = 1 ⊗ₜ (w ∘ₗ ρL (RingOfIntegers.mapRingEquiv c a))) ∧
  ∀ (n : ℕ) (x : La) (f : LevGrp La p n → O) (w : Module.Dual O L),
    (∀ b, f (lev p n b) = ((ζ n ^ EF x b : Oˣ) : O)) → der n f w →
      ∃ y ∈ P.om, P.ht (1 ⊗ₜ x) = 1 ⊗ₜ w + (p ^ n) • y

def IsHTConst {C O : Type} [Field C] [CommRing O] [Algebra O C] (v : Valuation C NNReal) (p : ℕ) (κ : O) : Prop :=
  algebraMap O C κ ≠ 0 ∧ v (algebraMap O C κ) ^ (p - 1) ≤ v (p : C)

structure IsPolLattice {E : Type} [Field E] [NumberField E] (c : E ≃+* E) (p : ℕ) {La : Type} [AddCommGroup La]
    [Module (𝓞 E) La] (EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) {N : ℕ} (u : Fin N → La) : Prop where
  free : Module.Free ℤ La
  finite : Module.Finite ℤ La
  alt : ∀ x, EF x x = 0
  unimod : Function.Bijective EF
  adj : ∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (RingOfIntegers.mapRingEquiv c a • y)
  rank : Module.finrank ℤ La = N * Module.finrank ℚ E
  span : ∀ x : La, ∃ (a : Fin N → 𝓞 E) (x' : La), x = ∑ i, a i • u i + p • x'

def PointHT : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [IsDomain O] [Algebra O C], v.Integers O → v (p : C) < 1 →
    IsAdicComplete (Ideal.span {(p : O)}) O →
    ∀ (E : Type) [Field E] [NumberField E] (c : E ≃+* E), (∀ x, c (c x) = x) →
    ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (y : Spec (CommRingCat.of O) ⟶ S) (La : Type) [AddCommGroup La] [Module (𝓞 E) La]
      (EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (N : ℕ) (u : Fin N → La), IsPolLattice c p EF u →
    ∀ (X : TorsTower p G y La) (L : Type) [AddCommGroup L] [Module O L] (M : LieModel G y L)
      (act : 𝓞 E → (G ⟶ G)) (ρL : 𝓞 E →+* Module.End O L), (∀ a, IsMonHom (act a)) → M.IsActOf act ρL →
      (∀ a : 𝓞 E, X.Induces (act a) (DistribMulAction.toAddMonoidHom La a)) →
      2 * Module.finrank O L = Module.finrank ℤ La →
    ∀ ζ : ℕ → Oˣ, (∀ n, IsPrimitiveRoot (ζ n) (p ^ n)) → (∀ n, ζ (n + 1) ^ p = ζ n) → X.PairingRegular EF ζ →
    ∀ κ : O, IsHTConst v p κ →
      ∃ P : HTPoint C O c κ N (C ⊗[ℤ] La) (C ⊗[O] Module.Dual O L), IsPointOf p (X.IsDer M) EF ζ ρL u P

namespace PointTest

def toInt : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv

def planeForm : (Fin 2 → 𝓞 ℚ) →ₗ[ℤ] (Fin 2 → 𝓞 ℚ) →ₗ[ℤ] ℤ :=
  LinearMap.mk₂ ℤ (fun x y => toInt (x 0 * y 1 - x 1 * y 0)) (by intros; simp; ring) (by intros; simp; ring)
    (by intros; simp; ring) (by intros; simp; ring)

variable {C O : Type} [Field C] [CommRing O] [Algebra O C] {v : Valuation C NNReal} {p : ℕ}

theorem val_sub_one_pow [hp : Fact p.Prime] {ζ : C} (hζ : IsPrimitiveRoot ζ p) : v (ζ - 1) ^ (p - 1) = v (p : C) := by
  have h1 : v ζ ≤ 1 := by
    have := congrArg v hζ.pow_eq_one
    rw [map_pow, map_one] at this
    exact ((pow_eq_one_iff_of_nonneg zero_le hp.out.ne_zero).1 this).le
  let z : v.integer := ⟨ζ, h1⟩
  have hz : IsPrimitiveRoot z p := IsPrimitiveRoot.of_map_of_injective (f := v.integer.subtype) hζ Subtype.val_injective
  have key : ∀ k ∈ Finset.range (p - 1), v (1 - ζ ^ (k + 1)) = v (ζ - 1) := by
    intro k hk
    have hk' : k + 1 < p := by have := Finset.mem_range.1 hk; omega
    have hc : (k + 1).Coprime p :=
      ((Nat.Prime.coprime_iff_not_dvd hp.out).2 (Nat.not_dvd_of_pos_of_lt k.succ_pos hk')).symm
    have ha := hz.associated_sub_one_pow_sub_one_of_coprime hc
    rw [Valuation.map_sub_swap]
    exact le_antisymm ((Valuation.integer.integers v).le_of_dvd ha.dvd)
      ((Valuation.integer.integers v).le_of_dvd ha.symm.dvd)
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.out.pos; omega⟩
  rw [Nat.add_sub_cancel] at key
  have := congrArg v hζ.prod_one_sub_pow_eq_order
  rw [map_prod, Finset.prod_congr rfl key, Finset.prod_const, Finset.card_range] at this
  simpa using this

theorem isHTConst_sub_one [hp : Fact p.Prime] {ζ : O} (hζ : IsPrimitiveRoot (algebraMap O C ζ) p) :
    IsHTConst v p (ζ - 1) := by
  refine ⟨?_, ?_⟩ <;> rw [map_sub, map_one]
  · exact hζ.sub_one_ne_zero hp.out.one_lt
  · exact (val_sub_one_pow hζ).le

theorem isHTConst_two [CharZero C] : IsHTConst v 2 (2 : O) :=
  ⟨by rw [map_ofNat]; exact two_ne_zero, by rw [map_ofNat]; simp⟩

theorem not_isHTConst_one (h : v (p : C) < 1) : ¬ IsHTConst v p (1 : O) := fun h1 =>
  absurd (by simpa using h1.2) (not_le.2 h)

end PointTest

end GlobalTheory.CompanionTheory.Ar.HT
