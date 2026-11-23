import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharExt

private theorem isAddUnit_of_pow {M : Type} [AddCommMonoid M] {p : ℕ} (hp : p ≠ 0) {a : M}
    (h : ∃ k, p ^ k • a = 0) : IsAddUnit a := by
  obtain ⟨k, hk⟩ := h
  have h1 : p ^ k = (p ^ k - 1) + 1 := by
    have : 0 < p ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ hp)
    omega
  rw [h1, add_nsmul, one_nsmul, add_comm] at hk
  exact ⟨⟨a, (p ^ k - 1) • a, hk, by rw [add_comm]; exact hk⟩, rfl⟩

private theorem extend_group {A B : Type} [AddCommGroup A] [AddCommGroup B] (j : A →+ B)
    (hj : Function.Injective j) (C : Type) [Field C] [IsAlgClosed C]
    (χ : A →+ Additive Cˣ) : ∃ κ : B →+ Additive Cˣ, ∀ a, κ (j a) = χ a := by
  classical
  have hsurj : ∀ n : ℕ, n ≠ 0 → ∀ x : Additive Cˣ, ∃ y : Additive Cˣ, n • y = x := by
    intro n hn x
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul x : Cˣ) : C)
      (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hz
      exact (Additive.toMul x : Cˣ).ne_zero hz.symm
    refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
    apply Additive.toMul.injective
    ext
    simpa using hz
  letI : DivisibleBy (Additive Cˣ) ℕ :=
    divisibleByOfSMulRightSurj (Additive Cˣ) ℕ (fun {n} hn x => hsurj n hn x)
  letI : DivisibleBy (Additive Cˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨κ, hκ⟩ := (Module.Baer.of_divisible (Additive Cˣ)).extension_property_addMonoidHom
    j hj χ
  exact ⟨κ, fun a => DFunLike.congr_fun hκ a⟩

theorem exists_extension : ∀ (M M' : Type) [AddCommMonoid M] [AddCommMonoid M'] (j : M' →+ M), Function.Injective j → ∀ (C : Type) [Field C] [IsAlgClosed C] (p : ℕ), p ≠ 0 → ∀ χ : M' → Cˣ, (∀ a b, χ (a + b) = χ a * χ b) → ∃ κ : M → Cˣ, (∀ a b, (∃ k, p ^ k • a = 0) → (∃ k, p ^ k • b = 0) → κ (a + b) = κ a * κ b) ∧ κ 0 = 1 ∧ ∀ a, (∃ k, p ^ k • a = 0) → κ (j a) = χ a := by
  intro M M' _ _ j hj C _ _ p hp χ hχ
  classical
  let χ' : AddUnits M' →+ Additive Cˣ := AddMonoidHom.mk' (fun u => Additive.ofMul (χ u.val))
    (fun a b => by rw [AddUnits.val_add, hχ]; rfl)
  have hj' : Function.Injective (AddUnits.map j) := by
    intro a b hab
    ext
    exact hj (congrArg AddUnits.val hab)
  obtain ⟨κ, hκ⟩ := extend_group (AddUnits.map j) hj' C χ'
  have key : ∀ u : AddUnits M,
      (if h : IsAddUnit u.val then Additive.toMul (κ h.addUnit) else 1) = Additive.toMul (κ u) := by
    intro u
    rw [dif_pos u.isAddUnit]
    congr 2
    ext
    exact IsAddUnit.addUnit_spec _
  refine ⟨fun a => if h : IsAddUnit a then Additive.toMul (κ h.addUnit) else 1, ?_, ?_, ?_⟩
  · intro a b ha hb
    obtain ⟨u, rfl⟩ := isAddUnit_of_pow hp ha
    obtain ⟨v, rfl⟩ := isAddUnit_of_pow hp hb
    have h3 := key (u + v)
    have h1 := key u
    have h2 := key v
    beta_reduce
    rw [h1, h2]
    refine Eq.trans h3 ?_
    rw [map_add]; rfl
  · have := key 0
    refine Eq.trans this ?_
    rw [map_zero]; rfl
  · intro a ha
    obtain ⟨u, rfl⟩ := isAddUnit_of_pow hp ha
    have h1 := key (AddUnits.map j u)
    refine Eq.trans h1 ?_
    rw [hκ]; rfl

end GlobalTheory.CharExt
