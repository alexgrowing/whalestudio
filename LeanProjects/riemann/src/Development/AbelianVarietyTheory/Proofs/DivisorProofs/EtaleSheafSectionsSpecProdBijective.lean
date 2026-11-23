import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCover
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.SecProd

variable (A B : Type) [CommRing A] [CommRing B]

theorem pt_fst (y : Spec (CommRingCat.of A)) :
    (Spec.map (CommRingCat.ofHom (RingHom.fst A B))) y =
      (PrimeSpectrum.primeSpectrumProd A B).symm (.inl (show PrimeSpectrum A from y)) := by
  apply PrimeSpectrum.ext
  rw [PrimeSpectrum.primeSpectrumProd_symm_inl_asIdeal]
  change Ideal.comap _ _ = _
  ext; simp [Ideal.prod, CommRingCat.ofHom]

theorem pt_snd (y : Spec (CommRingCat.of B)) :
    (Spec.map (CommRingCat.ofHom (RingHom.snd A B))) y =
      (PrimeSpectrum.primeSpectrumProd A B).symm (.inr (show PrimeSpectrum B from y)) := by
  apply PrimeSpectrum.ext
  rw [PrimeSpectrum.primeSpectrumProd_symm_inr_asIdeal]
  change Ideal.comap _ _ = _
  ext; simp [Ideal.prod, CommRingCat.ofHom]

theorem pt_cover (x : Spec (CommRingCat.of (A × B))) :
    x ∈ Set.range (Spec.map (CommRingCat.ofHom (RingHom.fst A B))) ∨
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (RingHom.snd A B))) := by
  have hx := (PrimeSpectrum.primeSpectrumProd A B).symm_apply_apply (show PrimeSpectrum (A × B) from x)
  rcases h : PrimeSpectrum.primeSpectrumProd A B x with y | y
  · left; refine ⟨y, (pt_fst A B y).trans ?_⟩; dsimp only at hx ⊢; rw [h] at hx; exact hx
  · right; refine ⟨y, (pt_snd A B y).trans ?_⟩; dsimp only at hx ⊢; rw [h] at hx; exact hx

theorem pt_disj (y : Spec (CommRingCat.of A)) (z : Spec (CommRingCat.of B)) :
    (Spec.map (CommRingCat.ofHom (RingHom.fst A B))) y ≠ (Spec.map (CommRingCat.ofHom (RingHom.snd A B))) z := by
  rw [pt_fst, pt_snd]
  intro h
  exact Sum.inl_ne_inr ((PrimeSpectrum.primeSpectrumProd A B).symm.injective h)

instance : IsOpenImmersion (Spec.map (CommRingCat.ofHom (RingHom.fst A B))) := by
  let := (RingHom.fst A B).toAlgebra
  exact IsOpenImmersion.of_isLocalization (1, 0)

instance : IsOpenImmersion (Spec.map (CommRingCat.ofHom (RingHom.snd A B))) := by
  let := (RingHom.snd A B).toAlgebra
  exact IsOpenImmersion.of_isLocalization (0, 1)

theorem res_comp {R : Type} [CommRing R] (F : Shv R) {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res (k ≫ g) a = Sec.res k (Sec.res g a) := by
  simp [Sec.res]

theorem res_id {R : Type} [CommRing R] (F : Shv R) {U : Scheme.{0}} (a : Sec F U) :
    Sec.res (𝟙 U) a = a := by
  simp [Sec.res]

end GlobalTheory.EtC.SecProd

namespace GlobalTheory.EtC.SecProd

variable (A B : Type) [CommRing A] [CommRing B]

theorem sec_empty {R : Type} [CommRing R] (F : Shv R) (W : Scheme.{0}) [IsEmpty W] (a b : Sec F W) : a = b := by
  apply (sec_ext_glue R F W).1 a b
  rw [loc_iff_etale_affine_points]
  · intro x; exact isEmptyElim x
  · intro V W' g k h; rw [res_comp, res_comp, h]

theorem empty_of_fac {W : Scheme.{0}} (w₁ : W ⟶ Spec (CommRingCat.of A)) (w₂ : W ⟶ Spec (CommRingCat.of B))
    (h : w₁ ≫ Spec.map (CommRingCat.ofHom (RingHom.fst A B)) = w₂ ≫ Spec.map (CommRingCat.ofHom (RingHom.snd A B))) :
    IsEmpty W :=
  ⟨fun x => pt_disj A B (w₁ x) (w₂ x) (by rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply])⟩

def facSieve : Sieve (Spec (CommRingCat.of (A × B))) where
  arrows := fun _ g => (∃ w, g = w ≫ Spec.map (CommRingCat.ofHom (RingHom.fst A B))) ∨
    (∃ w, g = w ≫ Spec.map (CommRingCat.ofHom (RingHom.snd A B)))
  downward_closed := by
    rintro W V g (⟨w, rfl⟩ | ⟨w, rfl⟩) k
    · exact Or.inl ⟨k ≫ w, by simp⟩
    · exact Or.inr ⟨k ≫ w, by simp⟩

theorem facSieve_mem : facSieve A B ∈ Scheme.etaleTopology (Spec (CommRingCat.of (A × B))) := by
  have hL : Loc _ fun _ g => (facSieve A B).arrows g := by
    rw [loc_iff_etale_affine_points]
    · intro x
      rcases pt_cover A B x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨_, _, inferInstance, inferInstance, ⟨y, hy⟩, Or.inl ⟨𝟙 _, by simp⟩⟩
      · exact ⟨_, _, inferInstance, inferInstance, ⟨y, hy⟩, Or.inr ⟨𝟙 _, by simp⟩⟩
    · intro V W g k h; exact (facSieve A B).downward_closed h k
  obtain ⟨S, hS, hSP⟩ := hL
  exact Scheme.etaleTopology.superset_covering (fun W g hg => hSP W g hg) hS

end GlobalTheory.EtC.SecProd

namespace GlobalTheory.EtC

open SecProd in

theorem sec_prod : ∀ (R : Type) [CommRing R] (A B : Type) [CommRing A] [CommRing B] (F : Shv R),
    Function.Bijective fun s : Sec F (Spec (CommRingCat.of (A × B))) =>
      (Sec.res (Spec.map (CommRingCat.ofHom (RingHom.fst A B))) s,
        Sec.res (Spec.map (CommRingCat.ofHom (RingHom.snd A B))) s) := by
  intro R _ A B _ _ F
  constructor
  · intro a b hab
    simp only [Prod.mk.injEq] at hab
    apply (sec_ext_glue R F _).1 a b
    refine ⟨facSieve A B, facSieve_mem A B, ?_⟩
    rintro W g (⟨w, rfl⟩ | ⟨w, rfl⟩)
    · rw [res_comp, res_comp, hab.1]
    · rw [res_comp, res_comp, hab.2]
  · rintro ⟨s1, s2⟩
    classical
    let i1 := Spec.map (CommRingCat.ofHom (RingHom.fst A B))
    let i2 := Spec.map (CommRingCat.ofHom (RingHom.snd A B))
    let s : ∀ (V : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of (A × B))), (facSieve A B).arrows g → Sec F V :=
      fun V g hg => if h : ∃ w, g = w ≫ i1 then Sec.res h.choose s1 else Sec.res (hg.resolve_left h).choose s2
    have key1 : ∀ V g (w : V ⟶ Spec (CommRingCat.of A)) (e : g = w ≫ i1) hg, s V g hg = Sec.res w s1 := by
      intro V g w e hg
      have h : ∃ w', g = w' ≫ i1 := ⟨w, e⟩
      simp only [s, dif_pos h]
      congr 1
      exact (cancel_mono i1).1 (h.choose_spec.symm.trans e)
    have key2 : ∀ V g (w : V ⟶ Spec (CommRingCat.of B)) (e : g = w ≫ i2) hg, s V g hg = Sec.res w s2 := by
      intro V g w e hg
      by_cases h : ∃ w', g = w' ≫ i1
      · haveI := empty_of_fac A B h.choose w (h.choose_spec.symm.trans e)
        exact sec_empty F V _ _
      · simp only [s, dif_neg h]
        congr 1
        exact (cancel_mono i2).1 ((hg.resolve_left h).choose_spec.symm.trans e)
    have hs : ∀ (V W : Scheme.{0}) (g : V ⟶ _) (k : W ⟶ V) (hg : (facSieve A B).arrows g),
        Sec.res k (s V g hg) = s W (k ≫ g) ((facSieve A B).downward_closed hg k) := by
      intro V W g k hg
      have hg' := hg
      rcases hg' with ⟨w, e⟩ | ⟨w, e⟩
      · rw [key1 V g w e hg, key1 W _ (k ≫ w) (by rw [e, Category.assoc]) ((facSieve A B).downward_closed hg k), res_comp]
      · rw [key2 V g w e hg, key2 W _ (k ≫ w) (by rw [e, Category.assoc]) ((facSieve A B).downward_closed hg k), res_comp]
    obtain ⟨a, ha⟩ := (sec_ext_glue R F _).2 _ (facSieve_mem A B) s hs
    refine ⟨a, Prod.ext ?_ ?_⟩
    · change Sec.res i1 a = s1
      have h1 : (facSieve A B).arrows i1 := Or.inl ⟨𝟙 _, (Category.id_comp _).symm⟩
      rw [ha _ i1 h1, key1 _ i1 (𝟙 _) (Category.id_comp _).symm h1, res_id]
    · change Sec.res i2 a = s2
      have h2 : (facSieve A B).arrows i2 := Or.inr ⟨𝟙 _, (Category.id_comp _).symm⟩
      rw [ha _ i2 h2, key2 _ i2 (𝟙 _) (Category.id_comp _).symm h2, res_id]

end GlobalTheory.EtC
