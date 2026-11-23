import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.TubeCut

def LeafChPush : Prop := ∀ (q : ℕ) (P : Arrow Spc),
  IsPushout ((chains (ZMod q)).map P.hom) ((chains (ZMod q)).map P.hom) ((chains (ZMod q)).map (dbl.inl P))
    ((chains (ZMod q)).map (dbl.inr P))

def LeafHKSplit : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {A B D : Cx R} (f : A ⟶ B) (l r : B ⟶ D)
  (s : D ⟶ B), IsPushout f f l r → r ≫ s = 𝟙 _ → ∀ p : D ⟶ cokernel f, l ≫ p = cokernel.π f → r ≫ p = 0 →
  Function.Injective (HK.pull R p F n) ∧ ∀ x, HK.pull R r F n x = 0 → ∃ y, HK.pull R p F n y = x

theorem hk_pull_pull {R : Type} [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R f F n (HK.pull R g F n x) = HK.pull R (f ≫ g) F n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem hk_pull_zero {R : Type} [CommRing R] {K L : Cx R} (F : Shv R) (n : ℤ) (x : HK R L F n) :
    HK.pull R (0 : K ⟶ L) F n x = 0 := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [← CohomologyClass.mk_zero]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem LeafRel_of (h1 : LeafChPush) (h2 : LeafHKSplit) : LeafRel := by
  intro q i
  have ex : ∀ P : Arrow Spc, ∃ p : (chains (ZMod q)).obj (dbl P) ⟶ cokernel ((chains (ZMod q)).map P.hom),
      (chains _).map (dbl.inl P) ≫ p = cokernel.π _ ∧ (chains _).map (dbl.inr P) ≫ p = 0 := fun P =>
    ⟨(h1 q P).desc (cokernel.π _) 0 (by simp), (h1 q P).inl_desc _ _ _, (h1 q P).inr_desc _ _ _⟩
  choose p hl hr using ex
  have hs : ∀ P : Arrow Spc, (chains (ZMod q)).map (dbl.inr P) ≫ (chains _).map (dbl.fold P) = 𝟙 _ := fun P => by
    rw [← Functor.map_comp, dbl.inr_fold, CategoryTheory.Functor.map_id]
  have mem : ∀ (P : Arrow Spc) (n : ℤ) x, HK.pull _ (p P) (tw q i) n x ∈ Hs q P n i := fun P n x => by
    change HK.pull _ ((chains _).map (dbl.inr P)) (tw q i) n (HK.pull _ (p P) (tw q i) n x) = 0
    rw [hk_pull_pull, hr, hk_pull_zero]
  refine ⟨fun P n => AddEquiv.ofBijective ((HK.pull _ (p P) (tw q i) n).codRestrict _ (mem P n)) ⟨fun x y h => ?_, fun x => ?_⟩,
    fun P n p' hl' hr' x => ?_⟩
  · exact (h2 _ (tw q i) n _ _ _ _ (h1 q P) (hs P) (p P) (hl P) (hr P)).1 (congrArg Subtype.val h)
  · obtain ⟨y, hy⟩ := (h2 _ (tw q i) n _ _ _ _ (h1 q P) (hs P) (p P) (hl P) (hr P)).2 x.1 x.2
    exact ⟨y, Subtype.ext hy⟩
  · have e : p' = p P := (h1 q P).hom_ext (hl'.trans (hl P).symm) (hr'.trans (hr P).symm)
    subst e; rfl

end LateralTheory.CohomologicalPurity.TubeCut
