import Development.EtaleCohomology.EtaleSheaves.EtaleBaseChangeFractionFieldIndEtaleOverPolynomi

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.E.t_E3Cut

theorem etale_base_change_fraction_field_of_etale_polynomial_algebra (hC3 : C3) (q : ℕ) [NeZero q] (i : ℤ) (T K : Type) [CommRing T] [IsDomain T] [IsLocalRing T]
    [Field K] [Algebra T K] [IsFractionRing T K] (hA : AIC T) (hq : IsUnit (q : T))
    (C : CommRingCat.{0}) (c : CommRingCat.of (Polynomial T) ⟶ C) (hc : Et c) :
    BC q i (CommRingCat.ofHom (algebraMap T K)) (pC (CommRingCat.of T) ≫ c) := by
  letI : Algebra (Polynomial T) C := c.hom.toAlgebra
  haveI : Algebra.Etale (Polynomial T) C := hc
  letI : Algebra T C := (pC (CommRingCat.of T) ≫ c).hom.toAlgebra
  haveI : IsScalarTower T (Polynomial T) C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h3 := hC3 q T hA hq C i
  have hsq := CommRingCat.isPushout_tensorProduct T (FractionRing T) C
  let e : CommRingCat.of (FractionRing T) ≅ CommRingCat.of K :=
    (IsLocalization.algEquiv (nonZeroDivisors T) (FractionRing T) K).toRingEquiv.toCommRingCatIso
  have hsq' : IsPushout (CommRingCat.ofHom (algebraMap T K)) (pC (CommRingCat.of T) ≫ c)
      (e.inv ≫ CommRingCat.ofHom (S := FractionRing T ⊗[T] C) Algebra.TensorProduct.includeLeftRingHom)
      (CommRingCat.ofHom (S := FractionRing T ⊗[T] C) Algebra.TensorProduct.includeRight.toRingHom) := by
    refine hsq.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · ext x
      simp [e]
    · rfl
    · simp
    · rfl
  exact BC.of_one hsq' h3

theorem etale_base_change_polynomial_induction_of_limit (hL : Limit) : EtaleBaseChangeFractionFieldIndEtaleOverPolynomial := by
  intro hH q _ i T K _ _ _ _ _ _ hA hq X h hIE
  have hC3 : C3 := hH.2.2.2.2.2.2.2.2.2.1
  let k := CommRingCat.ofHom (algebraMap T K)
  let φ := pushout.inr k (pC (CommRingCat.of T))
  have P1 : IsPushout k (pC (CommRingCat.of T)) (pushout.inl k (pC (CommRingCat.of T))) φ :=
    IsPushout.of_hasPushout _ _
  have hqX : IsUnit ((q : ℕ) : CommRingCat.of (Polynomial T)) := by
    have := hq.map (Polynomial.C : T →+* Polynomial T)
    simpa using this
  have hEt : ∀ (C : CommRingCat.{0}) (c : CommRingCat.of (Polynomial T) ⟶ C), Et c → BC q i φ c := by
    intro C c hc
    have hb := etale_base_change_fraction_field_of_etale_polynomial_algebra hC3 q i T K hA hq C c hc
    have P2 := IsPushout.of_hasPushout φ c
    exact BC.of_one P2 (hb _ _ _ (P1.paste_vert P2))
  have hB := hL hH q i φ hqX hEt X h hIE
  have P2 := IsPushout.of_hasPushout φ h
  exact BC.of_one (P1.paste_vert P2) (hB _ _ _ P2)

end LateralTheory.E.t_E3Cut
