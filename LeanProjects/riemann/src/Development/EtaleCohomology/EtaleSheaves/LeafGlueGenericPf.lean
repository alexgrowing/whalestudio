import Development.EtaleCohomology.EtaleSheaves.LeafGlueProperPf

noncomputable section
open AlgebraicGeometry.StructureSheaf CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.LeafGlueGenericPf

example (A : Type) [CommRing A] : Sp A = Spec (CommRingCat.of A) := rfl

def eta (A : Type) [CommRing A] [IsDomain A] : Sp A := ⟨⊥, Ideal.isPrime_bot⟩

theorem eta_generic (A : Type) [CommRing A] [IsDomain A] : IsGenericPoint (eta A) (⊤ : Set (Sp A)) := by
  rw [isGenericPoint_iff_specializes]
  intro y
  simp only [Set.top_eq_univ, Set.mem_univ, iff_true]
  exact (PrimeSpectrum.le_iff_specializes (eta A) y).1 bot_le

def etaT (A : Type) [CommRing A] [IsDomain A] : PrimeSpectrum.Top A := ⟨⊥, Ideal.isPrime_bot⟩

def psi0 {A L : Type} [CommRing A] [IsDomain A] [Field L] [Algebra A L] [IsFractionRing A L] :
    L →+* (structurePresheafInCommRingCat A).stalk (etaT A) := by
  have : (etaT A).asIdeal.IsPrime := Ideal.isPrime_bot
  exact IsLocalization.lift (M := nonZeroDivisors A) (S := L)
    (g := algebraMap A ((structurePresheafInCommRingCat A).stalk (etaT A))) (by
      intro y
      have hy : (y : A) ∈ (etaT A).asIdeal.primeCompl := by
        intro h0; exact nonZeroDivisors.ne_zero y.2 h0
      exact IsLocalization.map_units ((structurePresheafInCommRingCat A).stalk (etaT A))
        (⟨y, hy⟩ : (etaT A).asIdeal.primeCompl))

theorem fractionFieldToGenericStalk_algebraMap_eq {A L : Type} [CommRing A] [IsDomain A] [Field L] [Algebra A L] [IsFractionRing A L] (a : A) :
    psi0 (L := L) (algebraMap A L a) = StructureSheaf.toStalk A (etaT A) a := by
  unfold psi0; simp only [IsLocalization.lift_eq]; rfl

example {A : Type} [CommRing A] [IsDomain A] : (structurePresheafInCommRingCat A).stalk (etaT A) = (Sp A).presheaf.stalk (eta A) := rfl

theorem glued_curve_generic_point_maps_to_function_field : LeafGlueGeneric := by
  intro Ω L _ _ _ A B u h G
  have := G.hiA
  have : IsFractionRing A L := h.2.2.2.2.2.2.2.2.2.1
  have : IsIntegral G.C0 := glued_affine_curve_is_integral_scheme Ω L A B u h G
  let s := G.iA.stalkMap (eta A)
  refine ⟨G.iA.base (eta A), Spec.map (inv s) ≫ Spec.map (CommRingCat.ofHom (psi0 (L := L))), ?_, ?_⟩
  · have hg := (eta_generic A).image G.iA.base.hom.continuous
    rw [Set.top_eq_univ, Set.image_univ,
      (G.iA.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)).closure_eq] at hg
    exact hg
  · have key := Scheme.SpecMap_stalkMap_fromSpecStalk G.iA (x := eta A)
    have hinv : G.C0.fromSpecStalk (G.iA.base (eta A)) =
        Spec.map (inv s) ≫ (Sp A).fromSpecStalk (eta A) ≫ G.iA := by
      rw [← key, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
    rw [Category.assoc, hinv, Category.assoc, Category.assoc, G.hcA]
    congr 1
    rw [Spec.fromSpecStalk_eq']
    erw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    have ha : algebraMap Ω L a = algebraMap A L (algebraMap Ω A a) := rfl
    change psi0 (L := L) (algebraMap Ω L a) = StructureSheaf.toStalk A (etaT A) (algebraMap Ω A a)
    rw [ha, fractionFieldToGenericStalk_algebraMap_eq]

end LateralTheory.E.LeafGlueGenericPf
