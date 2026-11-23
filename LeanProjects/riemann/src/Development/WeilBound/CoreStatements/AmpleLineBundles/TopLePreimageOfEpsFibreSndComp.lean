import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CoverDenseAlt

variable {Z : Scheme.{0}} {A A' : Type} [CommRing A] [CommRing A']

def val (z : Sp A ⟶ Z) (V : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ V) : Γ(Z, V) →+* A :=
  (z.appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom

theorem val_congr {z z' : Sp A ⟶ Z} (e : z = z') (V : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ V) (h' : ⊤ ≤ z' ⁻¹ᵁ V) :
    val z V h = val z' V h' := by subst e; rfl

theorem le_comp (φ : A →+* A') {z : Sp A ⟶ Z} {V : Z.Opens} (h : ⊤ ≤ z ⁻¹ᵁ V) :
    ⊤ ≤ (spMap φ ≫ z) ⁻¹ᵁ V := fun p _ => h (Set.mem_univ ((spMap φ) p))

theorem val_comp (φ : A →+* A') (z : Sp A ⟶ Z) (V : Z.Opens) (h : ⊤ ≤ z ⁻¹ᵁ V) {z' : Sp A' ⟶ Z}
    (e : z' = spMap φ ≫ z) (h' : ⊤ ≤ z' ⁻¹ᵁ V) (s : Γ(Z, V)) :
    val z' V h' s = φ (val z V h s) := by
  subst e
  have h1 : (spMap φ ≫ z).appLE V ⊤ h' = z.appLE V ⊤ h ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have h2 : (spMap φ ≫ z).appLE V ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of A')).hom =
      z.appLE V ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom φ := by
    rw [h1, Category.assoc, Scheme.ΓSpecIso_naturality]
  unfold val
  rw [h2]
  rfl

theorem val_rep (z : Sp A ⟶ Z) {U : Z.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ z ⁻¹ᵁ U) :
    spMap (val z U h) ≫ hU.fromSpec = z := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec z hU (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
  change Spec.map (z.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom) ≫ hU.fromSpec = z
  rw [Spec.map_comp, Category.assoc, this, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id,
    Spec.map_id, Category.id_comp]

theorem val_ext {z z' : Sp A ⟶ Z} {U : Z.Opens} (hU : IsAffineOpen U) (h : ⊤ ≤ z ⁻¹ᵁ U)
    (h' : ⊤ ≤ z' ⁻¹ᵁ U) (e : ∀ s, val z U h s = val z' U h' s) : z = z' := by
  rw [← val_rep z hU h, ← val_rep z' hU h', RingHom.ext e]

theorem le_of_nil (φ : A →+* A') (hs : Function.Surjective φ) (hn : ∀ a, φ a = 0 → IsNilpotent a)
    {z : Sp A ⟶ Z} {V : Z.Opens} (h : ⊤ ≤ (spMap φ ≫ z) ⁻¹ᵁ V) : ⊤ ≤ z ⁻¹ᵁ V := by
  intro p _
  have : p ∈ Set.range (PrimeSpectrum.comap φ) := by
    have e : Set.range (PrimeSpectrum.comap φ) = Set.univ :=
      (range_comap_of_surjective _ _ hs).trans ((PrimeSpectrum.zeroLocus_eq_univ_iff _).2
        (fun a ha => mem_nilradical.2 (hn a ha)))
    exact e.ge (Set.mem_univ (α := PrimeSpectrum A) p)
  obtain ⟨q, rfl⟩ := this
  exact h (Set.mem_univ q)

theorem exists_affine {B : Type} [CommRing B] [IsLocalRing B] (z : Sp B ⟶ Z) :
    ∃ U : Z.Opens, IsAffineOpen U ∧ ⊤ ≤ z ⁻¹ᵁ U := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (z (IsLocalRing.closedPoint B))) isOpen_univ
  exact ⟨U, hU, (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of B) z hxU).ge⟩

theorem spMap_spMap {A'' : Type} [CommRing A''] (φ : A →+* A') (ψ : A' →+* A'') :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := by
  rw [← Spec.map_comp]; rfl

theorem mul_zero_of {J : Ideal A} (hJ : J ^ 2 = ⊥) {a b : A} (ha : a ∈ J) (hb : b ∈ J) : a * b = 0 := by
  have := Ideal.mul_mem_mul ha hb
  rwa [← pow_two, hJ, Ideal.mem_bot] at this

def Tri (J : Ideal A) : Subring (A × A × A) where
  carrier := {t | t.1 - t.2.1 ∈ J ∧ t.2.2 - t.2.1 ∈ J}
  mul_mem' := fun {a b} ha hb => ⟨by
      have := J.add_mem (J.mul_mem_right b.1 ha.1) (J.mul_mem_left a.2.1 hb.1)
      convert this using 1
      simp only [Prod.fst_mul, Prod.snd_mul]; ring, by
      have := J.add_mem (J.mul_mem_right b.2.2 ha.2) (J.mul_mem_left a.2.1 hb.2)
      convert this using 1
      simp only [Prod.fst_mul, Prod.snd_mul]; ring⟩
  one_mem' := ⟨by simp, by simp⟩
  add_mem' := fun {a b} ha hb => ⟨by
      have := J.add_mem ha.1 hb.1
      convert this using 1
      simp only [Prod.fst_add, Prod.snd_add]; ring, by
      have := J.add_mem ha.2 hb.2
      convert this using 1
      simp only [Prod.fst_add, Prod.snd_add]; ring⟩
  zero_mem' := ⟨by simp, by simp⟩
  neg_mem' := fun {a} ha => ⟨by
      have := J.neg_mem ha.1
      convert this using 1
      simp only [Prod.fst_neg, Prod.snd_neg]; ring, by
      have := J.neg_mem ha.2
      convert this using 1
      simp only [Prod.fst_neg, Prod.snd_neg]; ring⟩

variable (J : Ideal A)

def p1 : Tri J →+* A := (RingHom.fst _ _).comp (Tri J).subtype

def p2 : Tri J →+* A := ((RingHom.fst _ _).comp (RingHom.snd _ _)).comp (Tri J).subtype

def p3 : Tri J →+* A := ((RingHom.snd _ _).comp (RingHom.snd _ _)).comp (Tri J).subtype

def triLift {C : Type} [CommRing C] (a b c : C →+* A) (h1 : ∀ s, a s - b s ∈ J) (h2 : ∀ s, c s - b s ∈ J) :
    C →+* Tri J :=
  (a.prod (b.prod c)).codRestrict (Tri J) fun s => ⟨h1 s, h2 s⟩

def dg : A →+* Tri J := triLift J (RingHom.id A) (RingHom.id A) (RingHom.id A) (by simp) (by simp)

def mal (hJ : J ^ 2 = ⊥) : Tri J →+* A where
  toFun t := t.1.1 - t.1.2.1 + t.1.2.2
  map_one' := by simp
  map_zero' := by simp
  map_add' a b := by simp only [Subring.coe_add, Prod.fst_add, Prod.snd_add]; ring
  map_mul' a b := by
    have e1 := mul_zero_of hJ a.2.1 b.2.1
    have e2 := mul_zero_of hJ a.2.1 b.2.2
    have e3 := mul_zero_of hJ a.2.2 b.2.1
    have e4 := mul_zero_of hJ a.2.2 b.2.2
    simp only [Subring.coe_mul, Prod.fst_mul, Prod.snd_mul]
    linear_combination (-1 : A) * e2 - e3

theorem exists_tri (hJ : J ^ 2 = ⊥) (x o y : Sp A ⟶ Z) {W : Z.Opens} (hW : IsAffineOpen W) (ho : ⊤ ≤ o ⁻¹ᵁ W)
    (hx : spMap (Ideal.Quotient.mk J) ≫ x = spMap (Ideal.Quotient.mk J) ≫ o)
    (hy : spMap (Ideal.Quotient.mk J) ≫ y = spMap (Ideal.Quotient.mk J) ≫ o) :
    ∃ z : Sp (Tri J) ⟶ Z, spMap (p1 J) ≫ z = x ∧ spMap (p2 J) ≫ z = o ∧ spMap (p3 J) ≫ z = y ∧
      (y = o → spMap (mal J hJ) ≫ z = x) ∧ (x = o → spMap (mal J hJ) ≫ z = y) := by
  have hl : ∀ x : Sp A ⟶ Z, spMap (Ideal.Quotient.mk J) ≫ x = spMap (Ideal.Quotient.mk J) ≫ o → ⊤ ≤ x ⁻¹ᵁ W :=
    fun x hx => le_of_nil (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective (fun a ha => ⟨2, by
      have := Ideal.Quotient.eq_zero_iff_mem.1 ha
      rw [pow_two, mul_zero_of hJ this this]⟩) (hx ▸ le_comp _ ho)
  have hm : ∀ (x : Sp A ⟶ Z) (hx : spMap (Ideal.Quotient.mk J) ≫ x = spMap (Ideal.Quotient.mk J) ≫ o) s,
      val x W (hl x hx) s - val o W ho s ∈ J := fun x hx s =>
    Ideal.Quotient.eq.1 ((val_comp _ x W (hl x hx) rfl (le_comp _ (hl x hx)) s).symm.trans
      (val_comp _ o W ho hx _ s))
  refine ⟨spMap (triLift J _ _ _ (hm x hx) (hm y hy)) ≫ hW.fromSpec, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, spMap_spMap]; exact val_rep x hW _
  · rw [← Category.assoc, spMap_spMap]; exact val_rep o hW _
  · rw [← Category.assoc, spMap_spMap]; exact val_rep y hW _
  · rintro rfl
    rw [← Category.assoc, spMap_spMap]
    refine Eq.trans ?_ (val_rep x hW (hl x hx))
    congr 2
    ext s
    exact sub_add_cancel _ _
  · rintro rfl
    rw [← Category.assoc, spMap_spMap]
    refine Eq.trans ?_ (val_rep y hW (hl y hy))
    congr 2
    ext s
    change val x W _ s - val x W _ s + val y W _ s = _
    rw [sub_self, zero_add]

end CoverDenseAlt
