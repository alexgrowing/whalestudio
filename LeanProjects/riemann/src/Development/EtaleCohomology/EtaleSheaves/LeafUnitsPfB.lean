import Development.EtaleCohomology.EtaleSheaves.LeafUnitsPfA

namespace LateralTheory.E.E4

theorem mem_range_of_isIntegral {k B : Type} [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B]
    [Algebra k B] {x : B} (hx : IsIntegral k x) : x ∈ Set.range (algebraMap k B) := by
  have h : (minpoly k x).degree = 1 := IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hx)
  have hm : Polynomial.aeval x (minpoly k x) = 0 := minpoly.aeval k x
  have hq : (minpoly k x).leadingCoeff = 1 := minpoly.monic hx
  rw [Polynomial.eq_X_add_C_of_degree_eq_one h, hq, Polynomial.C_1, one_mul, map_add,
    Polynomial.aeval_X, Polynomial.aeval_C, add_eq_zero_iff_eq_neg] at hm
  exact ⟨-(minpoly k x).coeff 0, by rw [map_neg]; exact hm.symm⟩

theorem fg_subgroup_mult (n : ℕ) (H : Subgroup (Multiplicative (Fin n → ℤ))) : Group.FG H := by
  have : IsNoetherian ℤ (Additive (Multiplicative (Fin n → ℤ))) :=
    isNoetherian_of_linearEquiv (AddEquiv.additiveMultiplicative (Fin n → ℤ)).symm.toIntLinearEquiv
  rw [Group.fg_iff_subgroup_fg, Subgroup.fg_iff_add_fg]
  have := IsNoetherian.noetherian (R := ℤ) H.toAddSubgroup.toIntSubmodule
  exact (Submodule.fg_iff_addSubgroup_fg _).1 this

def LeafUnitsOrd : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B],
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 → IsIntegral k (u : B)

theorem LeafUnitsFG_of (h : LeafUnitsOrd) : LeafUnitsFG := by
  intro k B _ _ _ _ _ _
  obtain ⟨n, φ, hφ⟩ := h k B
  have hker : φ.ker ≤ (Units.map (algebraMap k B).toMonoidHom).range := by
    intro u hu
    obtain ⟨a, ha⟩ := mem_range_of_isIntegral (hφ u hu)
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [map_zero] at ha
      exact u.ne_zero ha.symm
    exact ⟨Units.mk0 a ha0, Units.ext (by simpa using ha)⟩
  have : Group.FG φ.range := fg_subgroup_mult n _
  have : Group.FG (Bˣ ⧸ φ.ker) :=
    Group.fg_of_surjective (f := ((QuotientGroup.quotientKerEquivRange φ).symm : φ.range →* Bˣ ⧸ φ.ker))
      (QuotientGroup.quotientKerEquivRange φ).symm.surjective
  refine Group.fg_of_surjective
    (f := QuotientGroup.map φ.ker (Units.map (algebraMap k B).toMonoidHom).range (MonoidHom.id _) hker) ?_
  intro x
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨QuotientGroup.mk u, rfl⟩

def LeafUnitsOrdCurve : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B →
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 → IsIntegral k (u : B)

theorem isIntegral_of_isField {k B : Type} [Field k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (hB : IsField B) (x : B) : IsIntegral k x := by
  let _ := hB.toField
  have : Module.Finite k B := finite_of_finite_type_of_isJacobsonRing k B
  exact Algebra.IsIntegral.isIntegral x

theorem LeafUnitsOrd_of (h : LeafUnitsOrdCurve) : LeafUnitsOrd := by
  intro k B _ _ _ _ _ _
  by_cases hB : IsField B
  · exact ⟨0, 1, fun u _ => isIntegral_of_isField hB _⟩
  · exact h k B hB

theorem LeafUnitsFG_of_curve (h : LeafUnitsOrdCurve) : LeafUnitsFG := LeafUnitsFG_of (LeafUnitsOrd_of h)

def LeafNoetherCurve : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], ¬ IsField B →
  ∃ g : Polynomial k →ₐ[k] B, Function.Injective g ∧ g.Finite

def LeafOrdAtInfinity : Prop := ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B] (g : Polynomial k →ₐ[k] B), Function.Injective g → g.Finite →
  ∃ (n : ℕ) (φ : Bˣ →* Multiplicative (Fin n → ℤ)), ∀ u : Bˣ, φ u = 1 → IsIntegral k (u : B)

theorem LeafUnitsOrdCurve_of (hN : LeafNoetherCurve) (hV : LeafOrdAtInfinity) : LeafUnitsOrdCurve := by
  intro k B _ _ _ _ _ _ hB
  obtain ⟨g, hg, hf⟩ := hN k B hB
  exact hV k B g hg hf

theorem LeafUnitsFG_of_leaves (hN : LeafNoetherCurve) (hV : LeafOrdAtInfinity) : LeafUnitsFG :=
  LeafUnitsFG_of_curve (LeafUnitsOrdCurve_of hN hV)

end LateralTheory.E.E4
