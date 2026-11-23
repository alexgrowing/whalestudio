import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.StalkIdeal

theorem exists_stalk_ideal : ∀ (X Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (x : X), x ∈ Set.range i → (∀ z : Z, IsClosed ({z} : Set Z)) → ∃ I : Ideal (X.presheaf.stalk x), I ≠ ⊤ ∧ (∀ q : Ideal (X.presheaf.stalk x), q.IsPrime → I ≤ q → q = IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ∧ ∀ J : Ideal (X.presheaf.stalk x), (∃ z : Sp (X.presheaf.stalk x ⧸ J) ⟶ Z, z ≫ i = spMap (Ideal.Quotient.mk J) ≫ X.fromSpecStalk x) ↔ I ≤ J := by
  intro X Z i _ x hx hcl
  have hq : IsClosedImmersion (pullback.snd i (X.fromSpecStalk x)) := inferInstance
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.1 hq
  have hpt : ∀ p : ↥(pullback i (X.fromSpecStalk x)),
      X.fromSpecStalk x (pullback.snd i (X.fromSpecStalk x) p) =
        i (pullback.fst i (X.fromSpecStalk x) p) := by
    intro p
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  have hsnd : ∀ s : ↥(Spec (CommRingCat.of (X.presheaf.stalk x ⧸ I))),
      pullback.snd i (X.fromSpecStalk x) (e.inv s) = PrimeSpectrum.comap (Ideal.Quotient.mk I) s := by
    intro s
    rw [he, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply e.inv e.hom, Iso.inv_hom_id]
    rfl
  refine ⟨I, ?_, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hx
    obtain ⟨p, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := i) (g := X.fromSpecStalk x)
      z (IsLocalRing.closedPoint _) (by rw [Scheme.fromSpecStalk_closedPoint, hz])
    have hs : (show PrimeSpectrum (X.presheaf.stalk x ⧸ I) from e.hom p).asIdeal.IsPrime :=
      PrimeSpectrum.isPrime _
    rw [← Ideal.Quotient.nontrivial_iff]
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    exact hs.ne_top (Subsingleton.elim _ _)
  · intro q hq hIq
    have hQ : (Ideal.map (Ideal.Quotient.mk I) q).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    let Q0 : PrimeSpectrum (X.presheaf.stalk x ⧸ I) := ⟨_, hQ⟩
    let Q : ↥(Spec (CommRingCat.of (X.presheaf.stalk x ⧸ I))) := Q0
    let P : PrimeSpectrum (X.presheaf.stalk x) := ⟨q, hq⟩
    have hPQ : PrimeSpectrum.comap (Ideal.Quotient.mk I) Q = P := by
      ext1
      show Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) q) = q
      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.2 hIq]
    have h1 : X.fromSpecStalk x P = i (pullback.fst i (X.fromSpecStalk x) (e.inv Q)) := by
      rw [← hPQ, ← hsnd, hpt]
    have hspec : P ⤳ IsLocalRing.closedPoint (X.presheaf.stalk x) := by
      rw [← PrimeSpectrum.le_iff_specializes, ← PrimeSpectrum.asIdeal_le_asIdeal]
      exact IsLocalRing.le_maximalIdeal hq.ne_top
    have h2 : X.fromSpecStalk x P ⤳ x := by
      have := hspec.map (X.fromSpecStalk x).continuous
      rwa [Scheme.fromSpecStalk_closedPoint] at this
    have hclosed : IsClosed ({i (pullback.fst i (X.fromSpecStalk x) (e.inv Q))} : Set X) := by
      rw [← Set.image_singleton]
      exact i.isClosedEmbedding.isClosedMap _ (hcl _)
    have h3 : x = X.fromSpecStalk x P := by
      have := h2.mem_closed hclosed (by rw [h1]; exact Set.mem_singleton _)
      rw [Set.mem_singleton_iff] at this
      exact this.trans h1.symm
    have h4 : P = IsLocalRing.closedPoint (X.presheaf.stalk x) :=
      (X.fromSpecStalk x).isEmbedding.injective (by rw [Scheme.fromSpecStalk_closedPoint]; exact h3.symm)
    exact congrArg PrimeSpectrum.asIdeal h4
  · intro J
    constructor
    · rintro ⟨z, hz⟩
      have hw := pullback.lift_snd z (spMap (Ideal.Quotient.mk J)) hz
      rw [he, ← Category.assoc] at hw
      have h2 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
          Spec.preimage (S := CommRingCat.of (X.presheaf.stalk x ⧸ J))
            (pullback.lift z (spMap (Ideal.Quotient.mk J)) hz ≫ e.hom)) =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
        rw [Spec.map_comp, Spec.map_preimage]
        exact hw
      rw [Spec.map_inj] at h2
      intro a ha
      have h3 := congrArg (fun g => g.hom a) h2
      have h4 : Ideal.Quotient.mk I a = 0 := Ideal.Quotient.eq_zero_iff_mem.2 ha
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply, h4, map_zero] at h3
      exact Ideal.Quotient.eq_zero_iff_mem.1 h3.symm
    · intro hIJ
      refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hIJ)) ≫ e.inv ≫
        pullback.fst i (X.fromSpecStalk x), ?_⟩
      rw [Category.assoc, Category.assoc, pullback.condition, he, Category.assoc, Iso.inv_hom_id_assoc,
        ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.Quotient.factor_comp_mk]

end GlobalTheory.CompanionTheory.StalkIdeal
