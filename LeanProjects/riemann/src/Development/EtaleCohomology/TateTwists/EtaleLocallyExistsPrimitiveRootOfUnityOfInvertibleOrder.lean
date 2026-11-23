import Development.EtaleCohomology.TateTwists.EtaleLocallyExistsPrimitiveRootOfUnityOfInvertib

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.EtaleFoundations.PrimLocExPf

noncomputable abbrev cyc (A : Type) [CommRing A] (q : ℕ) : A[X] := (cyclotomic q ℤ).map (Int.castRingHom A)

theorem cyc_monic (A : Type) [CommRing A] (q : ℕ) : (cyc A q).Monic :=
  (cyclotomic.monic q ℤ).map _

theorem cyc_cond (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    ∃ p₁ p₂ : A[X], derivative (cyc A q) * p₁ + cyc A q * p₂ = 1 := by
  obtain ⟨h, hh⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
  have hh' : (X ^ q - 1 : A[X]) = cyc A q * h.map (Int.castRingHom A) := by
    have := congrArg (Polynomial.map (Int.castRingHom A)) hh
    simpa [Polynomial.map_mul] using this
  set H := h.map (Int.castRingHom A)
  have hd : (C (q : A)) * X ^ (q - 1) = derivative (cyc A q) * H + cyc A q * derivative H := by
    have := congrArg derivative hh'
    rw [derivative_mul] at this
    rw [← this]; simp [derivative_X_pow]
  obtain ⟨u, hu⟩ := hq
  refine ⟨C (↑u⁻¹ : A) * X * H, C (↑u⁻¹ : A) * (X * derivative H - C (q : A) * H), ?_⟩
  have hX : X * X ^ (q - 1) = (X ^ q : A[X]) := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_neZero q)]
  have key : C (q : A) * X ^ q = X * (derivative (cyc A q) * H + cyc A q * derivative H) := by
    rw [← hd, ← hX]; ring
  have hXq : (X ^ q : A[X]) = cyc A q * H + 1 := by rw [← hh']; ring
  have hCu : C (↑u⁻¹ : A) * C (q : A) = 1 := by rw [← C_mul, ← hu, Units.inv_mul, C_1]
  calc derivative (cyc A q) * (C (↑u⁻¹ : A) * X * H) + cyc A q * (C (↑u⁻¹ : A) * (X * derivative H - C (q : A) * H))
      = C (↑u⁻¹ : A) * (X * (derivative (cyc A q) * H + cyc A q * derivative H) - C (q : A) * (cyc A q * H)) := by ring
    _ = C (↑u⁻¹ : A) * (C (q : A) * X ^ q - C (q : A) * (cyc A q * H)) := by rw [key]
    _ = C (↑u⁻¹ : A) * C (q : A) := by rw [hXq]; ring
    _ = 1 := hCu

noncomputable def pair (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    StandardEtalePair A where
  f := cyc A q
  monic_f := cyc_monic A q
  g := 1
  cond := by obtain ⟨p₁, p₂, h⟩ := cyc_cond A q hq; exact ⟨p₁, p₂, 0, by simpa using h⟩

theorem hasMap_root (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    (pair A q hq).HasMap (AdjoinRoot.root (cyc A q)) := by
  refine ⟨?_, ?_⟩
  · have : (pair A q hq).f = cyc A q := rfl
    rw [this, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  · have : (pair A q hq).g = 1 := rfl
    rw [this, map_one]; exact isUnit_one

noncomputable def equivB (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    (pair A q hq).Ring ≃ₐ[A] AdjoinRoot (cyc A q) := by
  refine AlgEquiv.ofAlgHom ((pair A q hq).lift (AdjoinRoot.root (cyc A q)) (hasMap_root A q hq))
    (AdjoinRoot.liftAlgHom (cyc A q) (Algebra.ofId A _) (pair A q hq).X
      (pair A q hq).hasMap_X.1) ?_ ?_
  · apply AdjoinRoot.algHom_ext
    simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_id, id_eq]
    exact (congrArg ((pair A q hq).lift _ (hasMap_root A q hq)) (AdjoinRoot.liftAlgHom_root _ _ _ _)).trans
      (StandardEtalePair.lift_X _ _ _)
  · apply StandardEtalePair.hom_ext
    simp only [AlgHom.coe_comp, Function.comp_apply, AlgHom.coe_id, id_eq]
    exact (congrArg (AdjoinRoot.liftAlgHom (cyc A q) (Algebra.ofId A _) (pair A q hq).X
      (pair A q hq).hasMap_X.1) (StandardEtalePair.lift_X _ _ _)).trans (AdjoinRoot.liftAlgHom_root _ _ _ _)

theorem etaleB (A : Type) [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    Algebra.Etale A (AdjoinRoot (cyc A q)) := by
  haveI : Algebra.IsStandardEtale A (AdjoinRoot (cyc A q)) :=
    Algebra.IsStandardEtale.of_equiv (equivB A q hq)
  infer_instance

theorem surjB (A : Type) [CommRing A] (q : ℕ) [NeZero q] :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A (AdjoinRoot (cyc A q)))) := by
  intro p
  haveI : Nontrivial A := ⟨⟨0, 1, fun h => p.2.ne_top (by rw [Ideal.eq_top_iff_one, ← h]; exact p.1.zero_mem)⟩⟩
  have hm := cyc_monic A q
  have hdeg : 0 < (cyc A q).natDegree := by
    show 0 < ((cyclotomic q ℤ).map (Int.castRingHom A)).natDegree
    rw [(cyclotomic.monic q ℤ).natDegree_map, natDegree_cyclotomic]; exact Nat.totient_pos.mpr (Nat.pos_of_neZero q)
  haveI : Module.Free A (AdjoinRoot (cyc A q)) := .of_basis (AdjoinRoot.powerBasis' hm).basis
  haveI : Nontrivial (AdjoinRoot (cyc A q)) := by
    have hne : (AdjoinRoot.powerBasis' hm).basis ⟨0, hdeg⟩ ≠ 0 := (AdjoinRoot.powerBasis' hm).basis.ne_zero _
    exact nontrivial_of_ne _ _ hne
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat p

end LateralTheory.EtaleFoundations.PrimLocExPf

namespace LateralTheory.EtaleFoundations.PrimLocExPf

def primMap {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (q : ℕ) (ζ : Prim q R) : Prim q S :=
  ⟨φ ζ.1, by simpa using ζ.2.1.map φ, by
    have h := Polynomial.aeval_algHom_apply φ.toIntAlgHom ζ.1 (Polynomial.cyclotomic q ℤ)
    rw [ζ.2.2, map_zero] at h
    simpa using h⟩

theorem root_prim (A : Type) [CommRing A] (q : ℕ) (hq : IsUnit (q : A)) :
    IsUnit (q : AdjoinRoot (cyc A q)) ∧
      aeval (AdjoinRoot.root (cyc A q)) (cyclotomic q ℤ) = 0 := by
  refine ⟨by simpa using hq.map (algebraMap A (AdjoinRoot (cyc A q))), ?_⟩
  have : cyc A q = (cyclotomic q ℤ).map (algebraMap ℤ A) := by rw [algebraMap_int_eq]
  rw [← Polynomial.aeval_map_algebraMap A, ← this, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]

theorem mono_prim (q : ℕ) {U : Scheme.{0}} : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V),
    Nonempty (Prim q Γ(V, ⊤)) → Nonempty (Prim q Γ(W, ⊤)) := by
  rintro V W g k ⟨ζ⟩
  exact ⟨primMap k.appTop.hom q ζ⟩

end LateralTheory.EtaleFoundations.PrimLocExPf

namespace LateralTheory.EtaleFoundations

open PrimLocExPf in
theorem etale_locally_exists_primitive_root_of_unity_of_invertible_order : EtaleLocallyExistsPrimitiveRootOfUnityOfInvertibleOrder := by
  intro q _ U hq
  rw [etale_sheaf_section_locally_iff_of_presheaf_facts U (fun V _ => Nonempty (Prim q Γ(V, ⊤))) (mono_prim q)]
  intro y
  obtain ⟨W, hWa, hyW, -⟩ : ∃ W : U.Opens, IsAffineOpen W ∧ y ∈ W ∧ W ≤ ⊤ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp U.isBasis_affineOpens) (show y ∈ (⊤ : U.Opens) from trivial)
  have hqA : IsUnit (q : Γ(U, W)) := by
    simpa using hq.map (U.presheaf.map (homOfLE le_top).op).hom
  have hE := etaleB Γ(U, W) q hqA
  let φ : Γ(U, W) ⟶ CommRingCat.of (AdjoinRoot (cyc Γ(U, W) q)) := CommRingCat.ofHom (algebraMap _ _)
  have hφ : Etale (Spec.map φ) :=
    HasRingHomProperty.Spec_iff.mpr
      ((RingHom.etale_algebraMap (R := Γ(U, W)) (S := AdjoinRoot (cyc Γ(U, W) q))).mpr hE)
  refine ⟨_, Spec.map φ ≫ hWa.fromSpec, inferInstance, inferInstance, ?_, ?_⟩
  · have hy : y ∈ Set.range hWa.fromSpec := by rw [hWa.range_fromSpec]; exact hyW
    obtain ⟨p, rfl⟩ := hy
    obtain ⟨r, hr⟩ := surjB Γ(U, W) q p
    exact ⟨r, congrArg hWa.fromSpec hr⟩
  · have h := root_prim Γ(U, W) q hqA
    exact ⟨primMap (Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot (cyc Γ(U, W) q)))).inv.hom q
      ⟨AdjoinRoot.root _, h.1, h.2⟩⟩

end LateralTheory.EtaleFoundations
