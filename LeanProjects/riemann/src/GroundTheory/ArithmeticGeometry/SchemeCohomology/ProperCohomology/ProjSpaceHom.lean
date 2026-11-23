import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjHom
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveSpaceChart
set_option maxSynthPendingDepth 1

open AlgebraicGeometry CategoryTheory Limits Opposite HomogeneousLocalization

namespace GroundTheory.Arith.SchemeCoh
universe u
noncomputable section

namespace ProjHom

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {X : Scheme.{u}}

lemma corr_apply (g : X ⟶ Proj 𝒜) (r : A) (V : X.Opens) (h : V ≤ g ⁻¹ᵁ Proj.basicOpen 𝒜 r)
    (y : Away 𝒜 r) :
    corr 𝒜 g r V h y = V.topIso.inv (g.appLE _ V h (Proj.awayToSection 𝒜 r y)) := by
  rw [corr, ConcreteCategory.comp_apply, Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply]
  have hB := congr($(Proj.basicOpenToSpec_app_top 𝒜 r) ((Scheme.ΓSpecIso _).inv y))
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at hB
  have hR := congr($(Scheme.Hom.resLE_app_top g h)
    ((Proj.basicOpen 𝒜 r).topIso.inv (Proj.awayToSection 𝒜 r y)))
  simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] at hR
  erw [hB]
  exact hR

set_option backward.isDefEq.respectTransparency false in

lemma ι_appTop_eq (V : X.Opens) (z : Γ(X, ⊤)) :
    V.ι.appTop z = V.topIso.inv (X.presheaf.map (homOfLE le_top).op z) := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv, ← CommRingCat.comp_apply,
    ← Functor.map_comp]
  congr

lemma basicOpen_awayToSection_isLocalizationElem {f g : A} {d e : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (hg : g ∈ 𝒜 e) (he : 0 < e) :
    (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg)) =
      Proj.basicOpen 𝒜 f ⊓ Proj.basicOpen 𝒜 g := by
  set U := Proj.basicOpen 𝒜 f
  have h1 : (Proj 𝒜).basicOpen (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg)) =
      U.ι ''ᵁ (U.ι ⁻¹ᵁ (Proj 𝒜).basicOpen
        (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg))) := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr ((Proj 𝒜).basicOpen_le _)]
  have h2 : U.ι ⁻¹ᵁ (Proj 𝒜).basicOpen
      (Proj.awayToSection 𝒜 f (Away.isLocalizationElem hf hg)) = U.ι ⁻¹ᵁ Proj.basicOpen 𝒜 g := by
    rw [← Scheme.Opens.toSpecΓ_preimage_basicOpen, ← SpecMap_preimage_basicOpen]
    change Proj.basicOpenToSpec 𝒜 f ⁻¹ᵁ
      (PrimeSpectrum.basicOpen (Away.isLocalizationElem hf hg) : (Spec (.of (Away 𝒜 f))).Opens) = _
    rw [← Proj.awayι_preimage_basicOpen 𝒜 hf hd hg he, ← Proj.basicOpenIsoSpec_inv_ι 𝒜 f hf hd,
      ← Scheme.Hom.comp_preimage, ← Proj.basicOpenIsoSpec_hom 𝒜 f hf hd, Iso.hom_inv_id_assoc]
  rw [h1, h2, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

end ProjHom

namespace ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

open MvPolynomial

variable {A : Type u} [CommRing A] {n : ℕ}

def chartHom (i : Fin (n + 1)) :
    MvPolynomial (Fin (n + 1)) A →+* Γ(projectiveSpace A n, Proj.basicOpen (grading A n) (X i)) :=
  (Proj.awayToSection (grading A n) (X i)).hom.comp ((polyToChart A i).comp (dehom A i))

lemma polyToChart_dehom_of_mem (i : Fin (n + 1)) {m : ℕ} {a : MvPolynomial (Fin (n + 1)) A}
    (ha : a ∈ grading A n m) :
    polyToChart A i (dehom A i a) =
      Away.mk (grading A n) (X_mem i) m a (by rwa [smul_eq_mul, mul_one]) := by
  apply HomogeneousLocalization.val_injective
  have h1 := congr($(scaleMap_eq A i) a)
  simp only [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply] at h1
  rw [h1, Away.val_mk, Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq]
  exact scaleMap_homog A i ha

lemma chartHom_of_mem (i : Fin (n + 1)) {m : ℕ} {a : MvPolynomial (Fin (n + 1)) A}
    (ha : a ∈ grading A n m) :
    chartHom i a = Proj.awayToSection (grading A n) (X i)
      (Away.mk (grading A n) (X_mem i) m a (by rwa [smul_eq_mul, mul_one])) := by
  rw [chartHom, RingHom.comp_apply, RingHom.comp_apply, polyToChart_dehom_of_mem i ha]

lemma chartHom_X (i j : Fin (n + 1)) :
    chartHom i (X j : MvPolynomial (Fin (n + 1)) A) = Proj.awayToSection (grading A n) (X i)
      (Away.isLocalizationElem (X_mem i) (X_mem j)) := by
  rw [chartHom_of_mem i (X_mem j)]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp [Away.val_mk]

lemma chartHom_X_self (i : Fin (n + 1)) : chartHom i (X i : MvPolynomial (Fin (n + 1)) A) = 1 := by
  rw [chartHom, RingHom.comp_apply, RingHom.comp_apply, dehom_X_self, map_one, map_one]

lemma basicOpen_chartHom_X (i j : Fin (n + 1)) :
    (projectiveSpace A n).basicOpen (chartHom i (X j : MvPolynomial (Fin (n + 1)) A)) =
      Proj.basicOpen (grading A n) (X i) ⊓ Proj.basicOpen (grading A n) (X j) := by
  rw [chartHom_X]
  exact ProjHom.basicOpen_awayToSection_isLocalizationElem _ (X_mem i) one_pos (X_mem j) one_pos

lemma basicOpen_mul_le_left (j k : Fin (n + 1)) :
    Proj.basicOpen (grading A n) (X k * X j : MvPolynomial (Fin (n + 1)) A) ≤
      Proj.basicOpen (grading A n) (X k) :=
  Proj.basicOpen_mono _ _ _ ⟨_, rfl⟩

lemma basicOpen_mul_le_right (j k : Fin (n + 1)) :
    Proj.basicOpen (grading A n) (X k * X j : MvPolynomial (Fin (n + 1)) A) ≤
      Proj.basicOpen (grading A n) (X j) :=
  Proj.basicOpen_mono _ _ _ ⟨_, mul_comm _ _⟩

lemma chart_identity (j k : Fin (n + 1)) {t : ℕ} {a : MvPolynomial (Fin (n + 1)) A}
    (ha : a ∈ grading A n (t • 1)) :
    (projectiveSpace A n).presheaf.map (homOfLE (basicOpen_mul_le_right j k)).op
        (Proj.awayToSection (grading A n) (X j) (Away.mk (grading A n) (X_mem j) t a ha)) *
      (projectiveSpace A n).presheaf.map (homOfLE (basicOpen_mul_le_left j k)).op
        (chartHom k (X j)) ^ t =
    (projectiveSpace A n).presheaf.map (homOfLE (basicOpen_mul_le_left j k)).op (chartHom k a) := by
  have ha' : a ∈ grading A n t := by rwa [smul_eq_mul, mul_one] at ha
  rw [chartHom_of_mem k (X_mem j), chartHom_of_mem k ha']
  have e1 : Proj.awayToSection (grading A n) (X k * X j)
      (awayMap (grading A n) (X_mem k) (show X k * X j = X j * X k from mul_comm _ _)
        (Away.mk (grading A n) (X_mem j) t a ha)) =
      (projectiveSpace A n).presheaf.map (homOfLE (basicOpen_mul_le_right j k)).op
        (Proj.awayToSection (grading A n) (X j) (Away.mk (grading A n) (X_mem j) t a ha)) := by
    have := congr($(Proj.awayMap_awayToSection (grading A n) (X_mem k)
      (show X k * X j = X j * X k from mul_comm _ _)) (Away.mk (grading A n) (X_mem j) t a ha))
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    exact this
  have e2 : ∀ y, Proj.awayToSection (grading A n) (X k * X j)
      (awayMap (grading A n) (X_mem j) (show X k * X j = X k * X j from rfl) y) =
      (projectiveSpace A n).presheaf.map (homOfLE (basicOpen_mul_le_left j k)).op
        (Proj.awayToSection (grading A n) (X k) y) := fun y => by
    have := congr($(Proj.awayMap_awayToSection (grading A n) (X_mem j)
      (show X k * X j = X k * X j from rfl)) y)
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at this
    exact this
  rw [← e1, ← e2, ← e2, ← map_pow, ← map_mul]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow, awayMap_mk,
    Away.val_mk, Localization.mk_pow, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, SubmonoidClass.coe_pow, OneMemClass.coe_one, one_mul]
  ring

lemma map_mul_pow_eq {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {u v w : R} (t : ℕ)
    (h : u * v ^ t = w) : φ u * φ v ^ t = φ w := by
  rw [← map_pow, ← map_mul, h]

lemma X_mem_irrelevant (k : Fin (n + 1)) :
    (X k : MvPolynomial (Fin (n + 1)) A) ∈ (HomogeneousIdeal.irrelevant (grading A n)).toIdeal := by
  change X k ∈ HomogeneousIdeal.irrelevant (grading A n)
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
    DirectSum.decompose_of_mem_ne _ (X_mem k) one_ne_zero]

lemma map_irrelevant_eq_top {S : Type*} [CommRing S] (f : MvPolynomial (Fin (n + 1)) A →+* S)
    (k : Fin (n + 1)) (hk : IsUnit (f (X k))) :
    (HomogeneousIdeal.irrelevant (grading A n)).toIdeal.map f = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem f (X_mem_irrelevant k)) hk

lemma iSup_basicOpen_X : ⨆ j : Fin (n + 1), Proj.basicOpen (grading A n)
    (X j : MvPolynomial (Fin (n + 1)) A) = ⊤ :=
  iSup_stdOpen

theorem eq_fromOfGlobalSections_of_preimage_eq_top {O : Scheme.{u}} (q : O ⟶ projectiveSpace A n)
    (k : Fin (n + 1)) (hq : q ⁻¹ᵁ Proj.basicOpen (grading A n) (X k) = ⊤) :
    q = Proj.fromOfGlobalSections (grading A n) ((q.appLE _ ⊤ hq.ge).hom.comp (chartHom k))
      (map_irrelevant_eq_top _ k (by
        rw [RingHom.comp_apply, chartHom_X_self, map_one]
        exact isUnit_one)) := by
  set f := (q.appLE _ ⊤ hq.ge).hom.comp (chartHom k)
  have hpre : ∀ j, q ⁻¹ᵁ Proj.basicOpen (grading A n) (X j) = O.basicOpen (f (X j)) := fun j => by
    rw [RingHom.comp_apply, Scheme.basicOpen_appLE, basicOpen_chartHom_X, Scheme.Hom.preimage_inf,
      hq, top_inf_eq, top_inf_eq]
  refine ProjHom.eq_fromOfGlobalSections f _ (fun j => X j) (fun _ => 1)
    (fun _ => one_pos) (fun j => X_mem j) iSup_basicOpen_X q hpre fun j t a ha => ?_
  have hW : O.basicOpen (f (X j)) ≤ q ⁻¹ᵁ Proj.basicOpen (grading A n) (X k * X j) := by
    rw [Proj.basicOpen_mul, Scheme.Hom.preimage_inf, hq, top_inf_eq, hpre]
  have hk : ∀ z, O.presheaf.map (homOfLE le_top).op (f z) =
      q.appLE _ (O.basicOpen (f (X j))) (hW.trans (q.preimage_mono (basicOpen_mul_le_left j k)))
        (chartHom k z) := fun z => by
    change O.presheaf.map _ (q.appLE _ ⊤ hq.ge (chartHom k z)) = _
    rw [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]
  have hk' : ∀ z, q.appLE _ (O.basicOpen (f (X j))) (hW.trans (q.preimage_mono (basicOpen_mul_le_left j k))) z =
      q.appLE _ (O.basicOpen (f (X j))) hW ((projectiveSpace A n).presheaf.map
        (homOfLE (basicOpen_mul_le_left j k)).op z) := fun z => by
    rw [← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE]
  have hj' : ∀ (h : O.basicOpen (f (X j)) ≤ q ⁻¹ᵁ Proj.basicOpen (grading A n) (X j)) z, q.appLE _ (O.basicOpen (f (X j))) h z =
      q.appLE _ (O.basicOpen (f (X j))) hW ((projectiveSpace A n).presheaf.map
        (homOfLE (basicOpen_mul_le_right j k)).op z) := fun h z => by
    rw [← ConcreteCategory.comp_apply, Scheme.Hom.map_appLE]
  rw [ProjHom.corr_apply, ProjHom.ι_appTop_eq, ProjHom.ι_appTop_eq, hk, hk, hk', hk', hj']
  exact map_mul_pow_eq _ t (map_mul_pow_eq _ t (chart_identity j k ha))

end ProjSpace
end
end GroundTheory.Arith.SchemeCoh
