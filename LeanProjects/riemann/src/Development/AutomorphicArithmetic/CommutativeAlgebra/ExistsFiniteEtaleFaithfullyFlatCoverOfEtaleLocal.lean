import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleToSheafifyLocallyBijectiveAndLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafSectionsExactStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC TensorProduct

private lemma exists_local (A : Type) [CommRing A]
    (P : ∀ V : Scheme.{0}, (V ⟶ Spec (CommRingCat.of A)) → Prop)
    (hP : ∀ (V W : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of A)) (k : W ⟶ V), P V g → P W (k ≫ g))
    (V : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of A)) (hV : IsAffine V) (hg : Etale g)
    (hPV : P V g) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Algebra.Etale A B ∧
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap A B))) = Set.range g ∧
      P (Spec (CommRingCat.of B)) (Spec.map (CommRingCat.ofHom (algebraMap A B))) := by
  haveI := hg
  let φ : CommRingCat.of A ⟶ Γ(V, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ g.appTop
  letI : Algebra A Γ(V, ⊤) := φ.hom.toAlgebra
  have hg' : g = V.isoSpec.hom ≫ Spec.map φ := by
    rw [Scheme.isoSpec_hom, Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
      Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hinv : Spec.map φ = V.isoSpec.inv ≫ g := by
    rw [hg', Iso.inv_hom_id_assoc]
  have hmap : Spec.map (CommRingCat.ofHom (algebraMap A Γ(V, ⊤))) = Spec.map φ := rfl
  refine ⟨Γ(V, ⊤), inferInstance, inferInstance, ?_, ?_, ?_⟩
  · have he : Etale (Spec.map φ) := by
      rw [hinv]
      infer_instance
    exact RingHom.etale_algebraMap.mp (HasRingHomProperty.Spec_iff.mp he)
  · rw [hmap, hg']
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨V.isoSpec.inv z, by simp⟩
    · rintro ⟨z, rfl⟩
      exact ⟨V.isoSpec.hom z, rfl⟩
  · rw [hmap, hinv]
    exact hP V _ g V.isoSpec.inv hPV

theorem UpperTheory.exists_finite_etale_faithfullyFlat_cover_of_etaleLocal_affine :
    ∀ (A : Type) [CommRing A] (P : ∀ V : Scheme.{0}, (V ⟶ Spec (CommRingCat.of A)) → Prop),
        (∀ (V W : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of A)) (k : W ⟶ V), P V g → P W (k ≫ g)) →
        Loc (Spec (CommRingCat.of A)) P →
        ∃ (n : ℕ) (C : Fin n → Type) (_ : ∀ i, CommRing (C i)) (_ : ∀ i, Algebra A (C i)),
          Algebra.Etale A (∀ i, C i) ∧ Module.FaithfullyFlat A (∀ i, C i) ∧
          ∀ i, P (Spec (CommRingCat.of (C i))) (Spec.map (CommRingCat.ofHom (algebraMap A (C i)))) := by
  intro A _ P hP hL
  have hx := (GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover _ P hP).1 hL
  choose V g hVa hge hxm hPx using hx
  have h1 := fun x => exists_local A P hP (V x) (g x) (hVa x) (hge x) (hPx x)
  choose B iB aB hBe hBr hBP using h1
  letI : ∀ x, CommRing (B x) := iB
  letI : ∀ x, Algebra A (B x) := aB
  have hopen : ∀ x, IsOpen (Set.range (g x)) := fun x => by
    haveI := hge x
    exact IsOpenMap.isOpen_range (g x).isOpenMap
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => Set.range (g x)) hopen
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hxm x⟩)
  let e : Fin t.card ≃ t := t.equivFin.symm
  haveI : ∀ i, Algebra.Etale A (B (e i)) := fun i => hBe _
  refine ⟨t.card, fun i => B (e i), fun i => inferInstance, fun i => inferInstance,
    inferInstance, ?_, fun i => hBP _⟩
  refine Module.FaithfullyFlat.of_comap_surjective fun p => ?_
  obtain ⟨x, hxt, hpx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ p))
  obtain ⟨i, hi⟩ := e.surjective ⟨x, hxt⟩
  have hpi : p ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (B (e i))))) := by
    rw [hBr, hi]
    exact hpx
  obtain ⟨q, hq⟩ := hpi
  refine ⟨PrimeSpectrum.comap (Pi.evalRingHom (fun j => B (e j)) i) q, ?_⟩
  rw [← hq]
  rfl
