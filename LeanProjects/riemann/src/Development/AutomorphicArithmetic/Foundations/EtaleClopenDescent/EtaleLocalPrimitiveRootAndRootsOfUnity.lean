import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Cb.PrimLoc

open Polynomial

private theorem etale_adjoinRoot {A : Type} [CommRing A] (f : A[X]) (hf : f.Monic)
    (h : IsUnit (AdjoinRoot.mk f (derivative f))) : Algebra.Etale A (AdjoinRoot f) := by
  obtain ⟨v, hv⟩ := h.exists_right_inv
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective v
  rw [← map_mul, ← map_one (AdjoinRoot.mk f), ← sub_eq_zero, ← map_sub,
    AdjoinRoot.mk_eq_zero] at hv
  obtain ⟨c, hc⟩ := hv
  let P : StandardEtalePair A :=
    { f := f, monic_f := hf, g := 1,
      cond := ⟨p, -c, 1, by rw [pow_one]; linear_combination hc⟩ }
  have hX : eval₂ (↑(Algebra.ofId A P.Ring)) P.X f = 0 := by
    simpa [aeval_def] using P.hasMap_X.1
  have hR : P.HasMap (AdjoinRoot.root f) :=
    ⟨by simp [P, AdjoinRoot.aeval_eq], by simp [P]⟩
  let e : AdjoinRoot f ≃ₐ[A] P.Ring :=
    AlgEquiv.ofAlgHom (AdjoinRoot.liftAlgHom f (Algebra.ofId A P.Ring) P.X hX)
      (P.lift (AdjoinRoot.root f) hR)
      (P.hom_ext (by simp)) (AdjoinRoot.algHom_ext (by simp))
  exact Algebra.Etale.of_equiv e.symm

private theorem exists_affine (U : Scheme.{0}) (x : U) :
    ∃ (V : Scheme.{0}) (j : V ⟶ U), IsAffine V ∧ Etale j ∧ x ∈ Set.range j ∧ Nontrivial Γ(V, ⊤) := by
  obtain ⟨i, y, hy⟩ := U.affineCover.exists_eq x
  haveI : IsOpenImmersion (U.affineCover.f i) := U.affineCover.map_prop i
  refine ⟨U.affineCover.X i, U.affineCover.f i, ?_, inferInstance, ⟨y, hy⟩, ?_⟩
  · dsimp [Scheme.affineCover]
    infer_instance
  · exact RingHom.domain_nontrivial ((U.affineCover.X i).presheaf.germ ⊤ y trivial).hom

private theorem exists_cover (V₀ : Scheme.{0}) [IsAffine V₀] [Nontrivial Γ(V₀, ⊤)] (f : Γ(V₀, ⊤)[X])
    (hf : f.Monic) (hd : 0 < f.natDegree) (h : IsUnit (AdjoinRoot.mk f (derivative f))) :
    ∃ (V : Scheme.{0}) (g : V ⟶ V₀) (θ : Γ(V, ⊤)), IsAffine V ∧ Etale g ∧ Function.Surjective g ∧
      eval₂ g.appTop.hom θ f = 0 := by
  haveI : Module.Free Γ(V₀, ⊤) (AdjoinRoot f) := Module.Free.of_basis (AdjoinRoot.powerBasis' hf).basis
  haveI : Module.Finite Γ(V₀, ⊤) (AdjoinRoot f) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis' hf).basis
  haveI : Nontrivial (AdjoinRoot f) := by
    by_contra hB
    rw [not_nontrivial_iff_subsingleton] at hB
    have hdim : 0 < (AdjoinRoot.powerBasis' hf).dim := by
      rw [AdjoinRoot.powerBasis'_dim]
      exact hd
    exact (AdjoinRoot.powerBasis' hf).basis.ne_zero ⟨0, hdim⟩ (Subsingleton.elim _ _)
  let φ : Γ(V₀, ⊤) ⟶ CommRingCat.of (AdjoinRoot f) :=
    CommRingCat.ofHom (algebraMap Γ(V₀, ⊤) (AdjoinRoot f))
  have hφ : Etale (Spec.map φ) :=
    HasRingHomProperty.Spec_iff.mpr
      ((RingHom.etale_algebraMap (R := Γ(V₀, ⊤)) (S := AdjoinRoot f)).mpr
        (etale_adjoinRoot f hf h))
  have hsφ : Surjective (Spec.map φ) := by
    rw [surjective_iff]
    intro y
    obtain ⟨p, hp⟩ :=
      PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := Γ(V₀, ⊤)) (B := AdjoinRoot f) y
    refine ⟨p, ?_⟩
    show (Spec.map φ).base p = y
    rw [Spec.map_base]
    exact hp
  refine ⟨Spec (CommRingCat.of (AdjoinRoot f)), Spec.map φ ≫ V₀.isoSpec.inv,
    (Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot f))).inv.hom (AdjoinRoot.root f),
    inferInstance, inferInstance, (surjective_iff _).mp inferInstance, ?_⟩
  have e1 : V₀.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(V₀, ⊤)).inv := by
    have := congrArg Scheme.Hom.appTop (Scheme.isoSpec_inv_toSpecΓ V₀)
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.Hom.id_appTop] at this
    rw [← cancel_epi (Scheme.ΓSpecIso Γ(V₀, ⊤)).hom, this, Iso.hom_inv_id]
  have e2 : (Spec.map φ).appTop =
      (Scheme.ΓSpecIso _).hom ≫ φ ≫ (Scheme.ΓSpecIso (CommRingCat.of (AdjoinRoot f))).inv := by
    rw [← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [Scheme.Hom.comp_appTop, e1, e2, Iso.inv_hom_id_assoc, CommRingCat.hom_comp, ← hom_eval₂]
  simp [φ, AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root]

private theorem isUnit_restrict_basicOpen (X : Scheme.{0}) (a : Γ(X, ⊤)) :
    IsUnit ((X.basicOpen a).ι.appTop.hom a) := by
  have hb := Scheme.Opens.ι_preimage_self (X.basicOpen a)
  rw [Scheme.preimage_basicOpen] at hb
  apply RingedSpace.isUnit_of_isUnit_germ _ ⊤
  intro x hx
  have hx' : x ∈ (X.basicOpen a).toScheme.basicOpen
      ((ConcreteCategory.hom ((X.basicOpen a).ι.app ⊤)) a) := by
    rw [hb]
    trivial
  exact (Scheme.mem_basicOpen _ _ x hx).mp hx'

private theorem local_eq (U : Scheme.{0}) (s : Finset ℕ) (y : Γ(U, ⊤)) (t : ℕ → Γ(U, ⊤))
    (hd : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → IsUnit (t a - t b)) (hp : ∏ a ∈ s, (y - t a) = 0) :
    Loc U fun _ g => ∃ a ∈ s, g.appTop.hom y = g.appTop.hom (t a) := by
  classical
  let p : ℕ → Γ(U, ⊤) := fun a => ∏ b ∈ s.erase a, (y - t b)
  let O : s → U.Opens := fun a => U.basicOpen (p a)
  have hcov : TopologicalSpace.IsOpenCover O := by
    apply eq_top_iff.mpr
    intro x _
    let g := ConcreteCategory.hom (U.presheaf.germ ⊤ x trivial)
    have hz : ∏ a ∈ s, g (y - t a) = 0 := by rw [← map_prod, hp, map_zero]
    have hex : ∃ a ∈ s, ¬ IsUnit (g (y - t a)) := by
      by_contra hne
      push_neg at hne
      have hu : IsUnit (∏ a ∈ s, g (y - t a)) := IsUnit.prod_iff.mpr hne
      rw [hz] at hu
      exact not_isUnit_zero hu
    obtain ⟨a, ha, hna⟩ := hex
    have hoth : ∀ b ∈ s.erase a, IsUnit (g (y - t b)) := by
      intro b hb
      obtain ⟨hba, hbs⟩ := Finset.mem_erase.mp hb
      by_contra hnb
      have hu : IsUnit (g (t a - t b)) := (hd a ha b hbs (Ne.symm hba)).map g
      have he : g (t a - t b) = g (y - t b) + -(g (y - t a)) := by
        simp only [map_sub]
        ring
      rw [he] at hu
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with h1 | h1
      · exact hnb h1
      · exact hna (IsUnit.neg_iff _ |>.mp h1)
    have hx : x ∈ O ⟨a, ha⟩ := by
      show x ∈ U.basicOpen (p a)
      rw [Scheme.mem_basicOpen_top]
      show IsUnit (g (p a))
      rw [map_prod]
      exact IsUnit.prod_iff.mpr hoth
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨a, ha⟩, hx⟩
  let C := U.openCoverOfIsOpenCover O hcov
  refine ⟨Sieve.ofArrows C.X C.f,
    Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology C), ?_⟩
  intro V g hg
  obtain ⟨⟨a, ha⟩, c, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ g).mp hg
  refine ⟨a, ha, ?_⟩
  have hu : IsUnit ((U.basicOpen (p a)).ι.appTop.hom (p a)) := isUnit_restrict_basicOpen U (p a)
  have hprod : (y - t a) * p a = 0 := by
    rw [Finset.mul_prod_erase s (fun b => y - t b) ha]
    exact hp
  have h2 := congrArg (U.basicOpen (p a)).ι.appTop.hom hprod
  rw [map_mul, map_zero] at h2
  have h3 := (hu.mul_left_eq_zero).mp h2
  rw [map_sub, sub_eq_zero] at h3
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, RingHom.comp_apply]
  exact congrArg c.appTop.hom h3

private theorem unit_deriv_cyclotomic {A : Type} [CommRing A] (q : ℕ) [NeZero q]
    (hq : IsUnit (q : A)) :
    IsUnit (AdjoinRoot.mk (cyclotomic q A) (derivative (cyclotomic q A))) := by
  obtain ⟨g, hg⟩ := cyclotomic.dvd_X_pow_sub_one q A
  have hm := congrArg (AdjoinRoot.mk (cyclotomic q A)) (congrArg derivative hg)
  rw [derivative_mul, map_add, map_mul, map_mul, AdjoinRoot.mk_self, zero_mul, add_zero] at hm
  have hX : IsUnit (AdjoinRoot.mk (cyclotomic q A) (X : A[X])) := by
    have h1 := congrArg (AdjoinRoot.mk (cyclotomic q A)) hg
    rw [map_mul, AdjoinRoot.mk_self, zero_mul, map_sub, map_pow, map_one, sub_eq_zero] at h1
    exact IsUnit.of_pow_eq_one h1 (NeZero.ne q)
  have hl : IsUnit (AdjoinRoot.mk (cyclotomic q A) (derivative (X ^ q - 1 : A[X]))) := by
    rw [derivative_sub, derivative_one, sub_zero, derivative_X_pow, map_mul, map_pow]
    refine IsUnit.mul ?_ (hX.pow _)
    simpa using hq.map (AdjoinRoot.of (cyclotomic q A))
  rw [hm] at hl
  exact isUnit_of_mul_isUnit_left hl

private theorem unit_deriv_kummer {A : Type} [CommRing A] (q : ℕ) [NeZero q]
    (hq : IsUnit (q : A)) (u : A) (hu : IsUnit u) :
    IsUnit (AdjoinRoot.mk (X ^ q - C u) (derivative (X ^ q - C u))) := by
  have hr : (AdjoinRoot.root (X ^ q - C u)) ^ q = AdjoinRoot.of (X ^ q - C u) u := by
    have h1 := AdjoinRoot.eval₂_root (X ^ q - C u)
    simpa [sub_eq_zero] using h1
  have hR : IsUnit (AdjoinRoot.root (X ^ q - C u)) := by
    rw [← isUnit_pow_iff (NeZero.ne q), hr]
    exact hu.map _
  rw [derivative_sub, derivative_C, sub_zero, derivative_X_pow, map_mul, map_pow, AdjoinRoot.mk_X]
  refine IsUnit.mul ?_ (hR.pow _)
  simpa using hq.map (AdjoinRoot.of (X ^ q - C u))

private theorem part_prim (q : ℕ) [NeZero q] (U : Scheme.{0}) (hq : IsUnit (q : Γ(U, ⊤))) :
    Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤)) := by
  refine (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover U _ ?_).2 fun x => ?_
  · rintro V W g k ⟨ζ⟩
    exact ⟨ζ.map k.appTop.hom⟩
  obtain ⟨V₀, j, hV, hj, ⟨y, hy⟩, hnt⟩ := exists_affine U x
  have hq₀ : IsUnit ((q : ℕ) : Γ(V₀, ⊤)) := by simpa using hq.map j.appTop.hom
  obtain ⟨V, g, θ, hVa, hg, hs, hθ⟩ := exists_cover V₀ (cyclotomic q Γ(V₀, ⊤))
    (cyclotomic.monic q _) (by rw [natDegree_cyclotomic]; exact Nat.totient_pos.2 (NeZero.pos q))
    (unit_deriv_cyclotomic q hq₀)
  obtain ⟨z, hz⟩ := hs y
  refine ⟨V, g ≫ j, hVa, inferInstance, ⟨z, by simp [hz, hy]⟩,
    ⟨Subtype.mk θ ⟨by simpa using hq₀.map g.appTop.hom, ?_⟩⟩⟩
  rw [← map_cyclotomic_int, eval₂_map] at hθ
  rw [aeval_def]
  rwa [show algebraMap ℤ Γ(V, ⊤) = g.appTop.hom.comp (Int.castRingHom Γ(V₀, ⊤)) from
    Subsingleton.elim _ _]

private theorem part_kummer (q : ℕ) [NeZero q] (U : Scheme.{0}) (hq : IsUnit (q : Γ(U, ⊤)))
    (u : (Γ(U, ⊤))ˣ) :
    Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u := by
  refine (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover U _ ?_).2 fun x => ?_
  · rintro V W g k ⟨v, hv⟩
    refine ⟨Units.map k.appTop.hom.toMonoidHom v, ?_⟩
    rw [← map_pow, hv]
    ext
    simp only [Units.coe_map, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
    rfl
  obtain ⟨V₀, j, hV, hj, ⟨y, hy⟩, hnt⟩ := exists_affine U x
  have hq₀ : IsUnit ((q : ℕ) : Γ(V₀, ⊤)) := by simpa using hq.map j.appTop.hom
  have hu₀ : IsUnit (j.appTop.hom (u : Γ(U, ⊤))) := u.isUnit.map _
  obtain ⟨V, g, θ, hVa, hg, hs, hθ⟩ := exists_cover V₀ (X ^ q - C (j.appTop.hom (u : Γ(U, ⊤))))
    (monic_X_pow_sub_C _ (NeZero.ne q))
    (by rw [natDegree_X_pow_sub_C]; exact NeZero.pos q)
    (unit_deriv_kummer q hq₀ _ hu₀)
  obtain ⟨z, hz⟩ := hs y
  have h1 : θ ^ q = g.appTop.hom (j.appTop.hom (u : Γ(U, ⊤))) := by
    simpa [eval₂_sub, sub_eq_zero] using hθ
  have hθu : IsUnit θ := (isUnit_pow_iff (NeZero.ne q)).1 (h1 ▸ hu₀.map _)
  refine ⟨V, g ≫ j, hVa, inferInstance, ⟨z, by simp [hz, hy]⟩, hθu.unit, ?_⟩
  ext
  simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.coe_map, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp]
  exact h1

end UpperTheory.Cb.PrimLoc

open UpperTheory.Cb.PrimLoc in
theorem UpperTheory.Cb.etaleLocal_primitiveRoot_and_roots_of_unity :
    ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}), (IsUnit (q : Γ(U, ⊤)) → Loc U fun V _ => Nonempty (Prim q Γ(V, ⊤))) ∧ (∀ ζ ξ : Prim q Γ(U, ⊤), Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val) ∧ (∀ (ζ : Prim q Γ(U, ⊤)) (x : Γ(U, ⊤)), x ^ q = 1 → Loc U fun _ g => ∃ a : ℕ, g.appTop.hom x = g.appTop.hom ζ.1 ^ a) ∧ (IsUnit (q : Γ(U, ⊤)) → ∀ u : (Γ(U, ⊤))ˣ, Loc U fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ q = Units.map g.appTop.hom.toMonoidHom u) := by
  intro q _ U
  refine ⟨part_prim q U, ?_, ?_, part_kummer q U⟩
  · intro ζ ξ
    have hprod := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q Γ(U, ⊤)).2.2.2.2.1 ζ ξ
    have hdist : ∀ a ∈ (Finset.range q).filter (fun a => a.Coprime q),
        ∀ b ∈ (Finset.range q).filter (fun a => a.Coprime q), a ≠ b →
          IsUnit (ζ.1 ^ a - ζ.1 ^ b) := by
      intro a ha b hb hab
      rw [Finset.mem_filter, Finset.mem_range] at ha hb
      apply (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q _).2.2.1 ζ a b
      intro hmod
      apply hab
      simpa [Nat.ModEq, Nat.mod_eq_of_lt ha.1, Nat.mod_eq_of_lt hb.1] using hmod
    obtain ⟨S, hS, hall⟩ := local_eq U _ ξ.1 (fun a => ζ.1 ^ a) hdist hprod
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨a, ha, he⟩ := hall V g hg
    rw [Finset.mem_filter, Finset.mem_range] at ha
    refine ⟨ZMod.unitOfCoprime a ha.2, ?_⟩
    rw [he, map_pow]
    congr 1
    simp [ZMod.val_natCast, Nat.mod_eq_of_lt ha.1]
  · intro ζ x hx
    have hprod := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q Γ(U, ⊤)).2.2.2.1 ζ x hx
    have hdist : ∀ a ∈ Finset.range q, ∀ b ∈ Finset.range q, a ≠ b →
          IsUnit (ζ.1 ^ a - ζ.1 ^ b) := by
      intro a ha b hb hab
      rw [Finset.mem_range] at ha hb
      apply (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties q _).2.2.1 ζ a b
      intro hmod
      apply hab
      simpa [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hmod
    obtain ⟨S, hS, hall⟩ := local_eq U _ x (fun a => ζ.1 ^ a) hdist hprod
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨a, -, he⟩ := hall V g hg
    exact ⟨a, by rw [he, map_pow]⟩
