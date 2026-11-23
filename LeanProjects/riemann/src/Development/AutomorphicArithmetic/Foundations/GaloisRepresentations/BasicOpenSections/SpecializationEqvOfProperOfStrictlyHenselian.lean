import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

private theorem eqv_of_isIso_comp {R : Type} [CommRing R] {E E' E'' : Spc} (a : E ⟶ E') [IsIso a]
    (b : E' ⟶ E'') (F : Shv R) (h : Eqv R b F) : Eqv R (a ≫ b) F := by
  intro n
  have hl : Function.LeftInverse (pull R (inv a) F n) (pull R a F n) := fun x => by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  have hr : Function.RightInverse (pull R (inv a) F n) (pull R a F n) := fun x => by
    rw [← pull_comp, IsIso.hom_inv_id, pull_id]
  have ha : Function.Bijective (pull R a F n) := ⟨hl.injective, hr.surjective⟩
  have he : (pull R (a ≫ b) F n : H R E'' F n → H R E F n) = pull R a F n ∘ pull R b F n := by
    funext x
    exact pull_comp R a b F n x
  rw [he]
  exact ha.comp (h n)

theorem UpperTheory.Gal.Mod.specialization_eqv_of_proper_of_strictly_henselian :
    GlobalTheory.EtC.E2 → ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) → ∀ (k : Type) [Field k] (r : A →+* k), Function.Surjective r → ∀ {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)) [IsProper p] (i : ℤ), Eqv _ (sch.map (pullback.fst p (Spec.map (CommRingCat.ofHom r)))) (tw q i) := by
  intro hE2 q A _ _ hSH hq k _ r hr X p _ i
  have hker : RingHom.ker r = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective r hr)

  let e0 : (A ⧸ RingHom.ker r) ≃+* k := RingHom.quotientKerEquivOfSurjective hr
  let e1 : IsLocalRing.ResidueField A ≃+* (A ⧸ RingHom.ker r) :=
    Ideal.quotEquivOfEq hker.symm
  let e : IsLocalRing.ResidueField A ≃+* k := e1.trans e0
  have hfac : (e : IsLocalRing.ResidueField A →+* k).comp (IsLocalRing.residue A) = r := by
    ext x
    rfl
  have hcomp : CommRingCat.ofHom r =
      CommRingCat.ofHom (IsLocalRing.residue A) ≫ CommRingCat.ofHom (e : IsLocalRing.ResidueField A →+* k) := by
    rw [← CommRingCat.ofHom_comp, hfac]
  let s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField A)) :=
    Spec.map (CommRingCat.ofHom (e : IsLocalRing.ResidueField A →+* k))
  have hIso : IsIso (CommRingCat.ofHom (e : IsLocalRing.ResidueField A →+* k)) :=
    (e.toCommRingCatIso).isIso_hom
  haveI : IsIso s := by
    dsimp only [s]
    infer_instance
  let f := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  have hg : Spec.map (CommRingCat.ofHom r) = s ≫ f := by
    dsimp only [s, f]
    rw [hcomp, Spec.map_comp]
  let φ : pullback p (Spec.map (CommRingCat.ofHom r)) ⟶ pullback p f :=
    pullback.map _ _ _ _ (𝟙 _) s (𝟙 _) (by simp) (by simp [hg])
  haveI : IsIso φ := by
    dsimp only [φ]
    infer_instance
  have hφ : pullback.fst p (Spec.map (CommRingCat.ofHom r)) = φ ≫ pullback.fst p f := by
    simp only [φ, pullback.map, pullback.lift_fst, Category.comp_id]
  rw [hφ, Functor.map_comp]
  exact eqv_of_isIso_comp (sch.map φ) _ _ (hE2 q A hSH hq p i)
