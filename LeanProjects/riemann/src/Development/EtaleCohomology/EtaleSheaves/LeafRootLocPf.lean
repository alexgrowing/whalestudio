import Development.EtaleCohomology.EtaleSheaves.ChernClassRootLocalization

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial GlobalTheory.EtC

namespace LateralTheory.E.LeafRootLocPf

def kpair {A : Type} [CommRing A] (q : ℕ) [NeZero q] (c : A) (hc : c * q = 1) (u : A) : StandardEtalePair A where
  f := X ^ q - C u
  monic_f := monic_X_pow_sub_C _ (NeZero.ne q)
  g := X
  cond := ⟨C c * X, 0, q, by
    obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
    subst hk
    simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, mul_zero, add_zero, Nat.add_sub_cancel]
    rw [show (C (((k + 1 : ℕ) : A)) * X ^ k) * (C c * X) = C (c * ((k + 1 : ℕ) : A)) * X ^ (k + 1) by
      rw [C_mul, pow_succ]; ring]
    rw [hc, C_1, one_mul]⟩

theorem kpair_root {A : Type} [CommRing A] (q : ℕ) [NeZero q] (c : A) (hc : c * q = 1) (u : A) :
    (kpair q c hc u).X ^ q = algebraMap A (kpair q c hc u).Ring u := by
  have h : aeval (kpair q c hc u).X (X ^ q - C u) = 0 := (kpair q c hc u).hasMap_X.1
  rw [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h
  exact h

theorem kpair_surj {A : Type} [CommRing A] (q : ℕ) [NeZero q] (c : A) (hc : c * q = 1) (u : Aˣ) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap A (kpair q c hc (u : A)).Ring)) := by
  intro p
  let K := p.asIdeal.ResidueField
  let Ω := AlgebraicClosure K
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A Ω u) (Nat.pos_of_ne_zero (NeZero.ne q))
  have hu : IsUnit (algebraMap A Ω u) := u.isUnit.map _
  have hzu : IsUnit z := by
    rw [← hz] at hu; exact (isUnit_pow_iff (NeZero.ne q)).mp hu
  have hm : (kpair q c hc (u : A)).HasMap z := by
    refine ⟨?_, ?_⟩
    · simp [kpair, hz]
    · simpa [kpair] using hzu
  let ψ := (kpair q c hc (u : A)).lift z hm
  refine ⟨⟨RingHom.ker ψ.toRingHom, RingHom.ker_isPrime _⟩, ?_⟩
  ext1
  change Ideal.comap _ (RingHom.ker ψ.toRingHom) = p.asIdeal
  rw [RingHom.comap_ker, show ψ.toRingHom.comp (algebraMap A _) = algebraMap A Ω from ψ.comp_algebraMap]
  rw [IsScalarTower.algebraMap_eq A K Ω, ← RingHom.comap_ker,
    (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap K Ω).injective, ← RingHom.ker_eq_comap_bot,
    Ideal.ker_algebraMap_residueField]

theorem loc_of_cover {U Y : Scheme.{0}} (π : Y ⟶ U) [Etale π] [Surjective π]
    (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) (hP : ∀ (V : Scheme.{0}) (h : V ⟶ Y), P V (h ≫ π)) : Loc U P := by
  let 𝒰 : U.Cover (Scheme.precoverage @Etale) :=
    Scheme.Cover.mkOfCovers PUnit.{1} (fun _ => Y) (fun _ => π)
      (fun x => ⟨PUnit.unit, π.surjective x⟩) inferInstance
  refine ⟨Sieve.ofArrows 𝒰.X 𝒰.f, Scheme.Cover.mem_grothendieckTopology 𝒰, ?_⟩
  intro V g hg
  obtain ⟨i, h, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hg
  exact hP V h

theorem LeafRootLoc_of : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc := by
  intro q _ U hq u
  obtain ⟨c, hc⟩ := hq.exists_left_inv
  let P := kpair q c hc (u : Γ(U, ⊤))
  let B : CommRingCat.{0} := CommRingCat.of P.Ring
  let φ : Γ(U, ⊤) ⟶ B := CommRingCat.ofHom (algebraMap _ P.Ring)
  have : Etale (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  have : Surjective (Spec.map φ) := ⟨kpair_surj q c hc u⟩
  refine loc_of_cover (pullback.fst U.toSpecΓ (Spec.map φ)) _ fun V h => ?_
  have hX : IsUnit P.X := (isUnit_pow_iff (NeZero.ne q)).mp (by rw [kpair_root]; exact u.isUnit.map _)
  have e : (h ≫ pullback.snd _ _) ≫ Spec.map φ = (h ≫ pullback.fst _ _) ≫ U.toSpecΓ := by
    simp [pullback.condition]
  have hcomp : φ ≫ (Scheme.ΓSpecIso B).inv ≫ (h ≫ pullback.snd _ _).appTop = (h ≫ pullback.fst _ _).appTop := by
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc, ← Scheme.Hom.comp_appTop, e,
      Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  refine ⟨Units.map ((h ≫ pullback.snd _ _).appTop.hom.comp (Scheme.ΓSpecIso B).inv.hom).toMonoidHom hX.unit, ?_⟩
  ext
  simp only [Units.val_pow_eq_pow_val, Units.coe_map, IsUnit.unit_spec, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe]
  rw [← map_pow, kpair_root]
  exact congrArg (fun f => f.hom (u : Γ(U, ⊤))) hcomp

end LateralTheory.E.LeafRootLocPf
