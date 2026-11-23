import Development.EtaleCohomology.KummerTheory.SecSHPf

open Polynomial IsLocalRing CategoryTheory AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.KummerTheory.ShSectPf

theorem isUnit_of_map {A K : Type} [CommRing A] [IsLocalRing A] [Field K] (φ : A →+* K)
    (hφ : ∀ a ∈ maximalIdeal A, φ a = 0) {a : A} (h : IsUnit (φ a)) : IsUnit a := by
  by_contra ha
  have := hφ a ((mem_maximalIdeal a).2 ha)
  rw [this] at h; exact not_isUnit_zero h

theorem alg_sect (A B : Type) [CommRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]
    [CommRing B] [Algebra A B] [Algebra.Etale A B] (Q : Ideal B) [Q.IsPrime]
    (hQ : Q.comap (algebraMap A B) = maximalIdeal A) : Nonempty (B →ₐ[A] A) := by
  obtain ⟨s, hsQ, hst⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) Q
  let S := Localization.Away s
  let P : StandardEtalePresentation A S := hst.nonempty_standardEtalePresentation.some
  let K := Q.ResidueField
  have hsu : IsUnit ((IsScalarTower.toAlgHom A B K) s) := by
    rw [isUnit_iff_ne_zero]
    show algebraMap B Q.ResidueField s ≠ 0
    rw [Ne, Ideal.algebraMap_residueField_eq_zero]; exact hsQ
  let ψ : S →ₐ[A] K := IsLocalization.Away.liftAlgHom s hsu
  let xb : K := ψ P.x
  have hmap := P.hasMap.map ψ
  have hder := hmap.isUnit_derivative_f

  have hkill : ∀ a ∈ maximalIdeal A, algebraMap A K a = 0 := by
    intro a ha
    rw [IsScalarTower.algebraMap_apply A B K, Ideal.algebraMap_residueField_eq_zero]
    rw [← hQ] at ha; exact ha
  have hloc : IsLocalHom (algebraMap A K) := ⟨fun a h => isUnit_of_map _ hkill h⟩
  let i : ResidueField A →+* K := ResidueField.lift (algebraMap A K)
  have hi : ∀ a, i (residue A a) = algebraMap A K a := fun a => ResidueField.lift_residue_apply _ a
  let _ : Algebra (ResidueField A) K := i.toAlgebra
  have hev : ∀ q : A[X], aeval xb (q.map (residue A)) = aeval xb q := by
    intro q
    rw [aeval_def, aeval_def, eval₂_map]
    congr 1
  let fb := P.f.map (residue A)
  have hint : IsIntegral (ResidueField A) xb :=
    ⟨fb, P.monic_f.map _, by rw [← aeval_def, hev]; exact hmap.1⟩
  have hirr := minpoly.irreducible hint
  have hsep : (minpoly (ResidueField A) xb).Separable := by
    rw [Polynomial.separable_iff_derivative_ne_zero hirr]
    intro h0
    obtain ⟨h, hh⟩ := minpoly.dvd (ResidueField A) xb (p := fb) (by rw [hev]; exact hmap.1)
    have : aeval xb (derivative fb) = 0 := by
      rw [hh, derivative_mul, h0]; simp
    rw [show derivative fb = (derivative P.f).map (residue A) from derivative_map _ _,
      hev] at this
    rw [this] at hder; exact not_isUnit_zero hder
  obtain ⟨a0, ha0⟩ := IsSepClosed.exists_root _ (minpoly.degree_pos hint).ne' hsep
  have hd0 : X - C a0 ∣ minpoly (ResidueField A) xb := dvd_iff_isRoot.2 ha0
  have hdvd : minpoly (ResidueField A) xb ∣ X - C a0 :=
    Irreducible.dvd_symm (irreducible_X_sub_C a0) hirr hd0
  obtain ⟨a00, ha00⟩ := residue_surjective a0
  have hxb : xb = algebraMap A K a00 := by
    have h1 : aeval xb (X - C a0) = 0 := by
      obtain ⟨c, hc⟩ := hdvd; rw [hc, map_mul, minpoly.aeval, zero_mul]
    rw [map_sub, aeval_X, aeval_C, sub_eq_zero] at h1
    rw [h1, ← ha00]; exact hi a00
  have hzero : ∀ a : A, algebraMap A K a = 0 → a ∈ maximalIdeal A := by
    intro a ha; by_contra hn
    have := ((mem_maximalIdeal a).not.1 hn |> not_not.1).map (algebraMap A K)
    rw [ha] at this; exact not_isUnit_zero this
  have hev' : ∀ q : A[X], algebraMap A K (q.eval a00) = aeval xb q := by
    intro q; rw [hxb, aeval_algebraMap_apply, coe_aeval_eq_eval]
  obtain ⟨r, hr, hra⟩ := HenselianLocalRing.is_henselian P.f P.monic_f a00
    (hzero _ (by rw [hev']; exact hmap.1)) (isUnit_of_map _ hkill (by rw [hev']; exact hder))
  have hrK : algebraMap A K r = xb := by
    rw [hxb, ← sub_eq_zero, ← map_sub]; exact hkill _ hra
  have hr' : P.HasMap r := by
    refine ⟨by rw [coe_aeval_eq_eval]; exact hr, isUnit_of_map _ hkill ?_⟩
    rw [← aeval_algebraMap_apply, hrK]; exact hmap.2
  exact ⟨((P.lift r hr').comp P.equivRing.toAlgHom).comp (IsScalarTower.toAlgHom A B S)⟩

theorem ShSect_of : LateralTheory.KummerTheory.SecSHPf.ShSect := by
  intro A _ hA Y f hf hsurj
  obtain ⟨hH, hsc⟩ := hA
  obtain ⟨y, hy⟩ := hsurj.surj (IsLocalRing.closedPoint A : Spec (CommRingCat.of A))
  let 𝒰 := Y.affineOpenCover
  let j := 𝒰.idx y
  obtain ⟨y', hy'⟩ := 𝒰.covers y
  let g := 𝒰.f j
  let φ : CommRingCat.of A ⟶ 𝒰.X j := Spec.preimage (g ≫ f)
  have hφ : Spec.map φ = g ≫ f := Spec.map_preimage _
  have het : φ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @Etale), hφ]; infer_instance
  algebraize [φ.hom]
  have hpt : (Spec.map φ) y' = IsLocalRing.closedPoint A := by
    rw [hφ, Scheme.Hom.comp_apply]
    simp only [g, j] at hy' ⊢
    rw [hy', hy]
  have hQ : y'.asIdeal.comap (algebraMap A (𝒰.X j)) = IsLocalRing.maximalIdeal A := by
    have := congrArg PrimeSpectrum.asIdeal hpt
    exact this
  have : y'.asIdeal.IsPrime := PrimeSpectrum.isPrime y'
  obtain ⟨ψ⟩ := alg_sect A (𝒰.X j) y'.asIdeal hQ
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ g, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp]
  convert Spec.map_id (CommRingCat.of A)
  ext a
  exact ψ.commutes a

end LateralTheory.KummerTheory.ShSectPf
