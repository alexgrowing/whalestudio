import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialField

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory
namespace TorusConst

open Polynomial TorusToProper

lemma exists_elim {R L : Type} [CommRing R] [Field L] (e : R →+* L) (a b : R[X])
    (ha : a.map e = 1) (hb : b.map e = 1) :
    ∃ g : R, e g ≠ 0 ∧ ∀ (A : Type) [Field A] (c : R →+* A) (x : A), eval₂ c x a = 0 →
      (x ≠ 0 → eval₂ c x⁻¹ b = 0) → c g = 0 := by
  let n := b.natDegree
  let h : R[X] := X * reflect n b
  have hh : h.natDegree ≤ n + 1 := by
    refine natDegree_mul_le.trans ?_
    have h1 : (reflect n b).natDegree ≤ n := natDegree_reflect_le.trans (by simp [n])
    have h2 : (X : R[X]).natDegree ≤ 1 := natDegree_X_le
    omega
  obtain ⟨p, q, -, -, hpq⟩ := exists_mul_add_mul_eq_C_resultant a h (m := a.natDegree) (n := n + 1)
    le_rfl hh (Or.inr (by omega))
  refine ⟨resultant a h a.natDegree (n + 1), ?_, fun A _ c x h1 h2 => ?_⟩
  · rw [← resultant_map_map, ha, resultant_one_left]
    have : h.map e = X ^ (n + 1) := by
      rw [Polynomial.map_mul, ← reflect_map, hb, reflect_one, map_X, pow_succ']
    simp [this]
  · have h3 : eval₂ c x h = 0 := by
      rw [eval₂_mul, eval₂_X]
      by_cases hx : x = 0
      · simp [hx]
      · letI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
        have := (eval₂_reflect_eq_zero_iff c x⁻¹ n b le_rfl).2 (h2 hx)
        rw [invOf_eq_inv, inv_inv] at this
        rw [this, mul_zero]
    have := congrArg (eval₂ c x) hpq
    rw [eval₂_add, eval₂_mul, eval₂_mul, h1, h3, eval₂_C] at this
    simpa using this.symm

lemma natDegree_eq_zero_of_inv {F : Type} [Field F] (a b : F[X])
    (h : algebraMap F[X] (FractionRing F[X]) a =
      eval₂ (algebraMap F (FractionRing F[X])) (algebraMap F[X] (FractionRing F[X]) X)⁻¹ b) :
    a.natDegree = 0 := by
  set x := algebraMap F[X] (FractionRing F[X]) X with hxd
  have hx : x ≠ 0 := fun h0 => X_ne_zero (IsFractionRing.injective F[X] (FractionRing F[X])
    (h0.trans (map_zero _).symm))
  letI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
  have h1 := eval₂_reflect_mul_pow (algebraMap F (FractionRing F[X])) x⁻¹ b.natDegree b le_rfl
  rw [invOf_eq_inv, inv_inv, ← h] at h1
  have h2 : ∀ p : F[X], eval₂ (algebraMap F (FractionRing F[X])) x p =
      algebraMap F[X] (FractionRing F[X]) p := fun p => by
    rw [← aeval_def, hxd, aeval_algebraMap_apply, aeval_X_left_apply]
  have h3 : reflect b.natDegree b = a * X ^ b.natDegree := by
    apply IsFractionRing.injective F[X] (FractionRing F[X])
    rw [map_mul, map_pow, ← h1, h2, ← hxd, _root_.mul_assoc, ← mul_pow, inv_mul_cancel₀ hx, one_pow, _root_.mul_one]
  by_cases ha : a = 0
  · simp [ha]
  have h4 : (reflect b.natDegree b).natDegree ≤ b.natDegree := natDegree_reflect_le.trans (by simp)
  rw [h3, natDegree_mul_X_pow _ ha] at h4
  omega

set_option backward.isDefEq.respectTransparency false in

lemma exists_extension {W Z Y S : Scheme.{0}} [IsIntegral Z]
    (hZ : ∀ x : Z, ValuationRing (Z.presheaf.stalk x)) (w : W ⟶ Z) [IsOpenImmersion w] [Nonempty W]
    (sZ : Z ⟶ S) (sY : Y ⟶ S) [IsProper sY] [Y.IsSeparated] [S.IsSeparated] (u : W ⟶ Y)
    (hu : u ≫ sY = w ≫ sZ) : ∃ g : Z ⟶ Y, w ≫ g = u ∧ g ≫ sY = sZ := by
  have hd : Dense (w.opensRange : Set Z) :=
    w.opensRange.2.dense (Set.range_nonempty _)
  let f : Z.PartialMap Y := ⟨w.opensRange, hd, w.isoOpensRange.inv ≫ u⟩
  have hspec : ∀ (p : Z.PartialMap Y) (x : Z) (hx : x ∈ p.domain),
      Spec.map (CommRingCat.ofHom (algebraMap (Z.presheaf.stalk x) Z.functionField)) ≫
        p.fromSpecStalkOfMem hx = p.fromFunctionField := by
    intro p x hx
    simp only [Scheme.PartialMap.fromSpecStalkOfMem]
    rw [← Category.assoc]
    congr 1
    rw [← cancel_mono p.domain.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι]
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec Z).specializes trivial)
  have hf : f.fromFunctionField ≫ sY = Z.fromSpecStalk _ ≫ sZ := by
    simp only [Scheme.PartialMap.fromSpecStalkOfMem, f, Category.assoc, hu]
    rw [Scheme.Hom.isoOpensRange_inv_comp_assoc, ← Category.assoc,
      Scheme.Opens.fromSpecStalkOfMem_ι]
  have hE : ValuativeCriterion.Existence sY := by
    have h : UniversallyClosed sY := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  have htop : f.toRationalMap.domain = ⊤ := by
    refine top_le_iff.1 fun x _ => ?_
    have := hZ x
    let Q : ValuativeCommSq sY :=
      { R := Z.presheaf.stalk x, K := Z.functionField, i₁ := f.fromFunctionField,
        i₂ := Z.fromSpecStalk x ≫ sZ,
        commSq := ⟨by
          rw [hf, ← Category.assoc]
          congr 1
          exact (Scheme.SpecMap_stalkSpecializes_fromSpecStalk
            ((genericPoint_spec Z).specializes trivial)).symm⟩ }
    obtain ⟨⟨l, h1, h2⟩⟩ := hE Q
    refine Scheme.RationalMap.mem_domain.2 ⟨Scheme.PartialMap.ofFromSpecStalk (x := x) sZ sY l h2,
      Scheme.PartialMap.mem_domain_ofFromSpecStalk (x := x) sZ sY l h2, ?_⟩
    apply Scheme.RationalMap.eq_of_fromFunctionField_eq
    rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
      Scheme.RationalMap.fromFunctionField_toRationalMap,
      ← hspec _ x (Scheme.PartialMap.mem_domain_ofFromSpecStalk (x := x) sZ sY l h2),
      Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk]
    exact h1
  let k : Z ⟶ f.toRationalMap.domain.toScheme := IsOpenImmersion.lift f.toRationalMap.domain.ι (𝟙 Z)
    (by rw [Scheme.Opens.range_ι, htop]; simp)
  have hk : k ≫ f.toRationalMap.domain.ι = 𝟙 Z := IsOpenImmersion.lift_fac _ _ _
  have key : w ≫ k ≫ f.toRationalMap.toPartialMap.hom = u := by
    have h1 := f.toPartialMap_toRationalMap_restrict
    have h2 : w ≫ k = w.isoOpensRange.hom ≫ Z.homOfLE f.le_domain_toRationalMap := by
      rw [← cancel_mono f.toRationalMap.domain.ι, Category.assoc, hk, Category.assoc,
        Scheme.homOfLE_ι, Category.comp_id]
      exact (Scheme.Hom.isoOpensRange_hom_ι w).symm
    rw [← Category.assoc, h2, Category.assoc]
    exact (congrArg (w.isoOpensRange.hom ≫ ·) h1).trans (Iso.hom_inv_id_assoc _ _)
  refine ⟨k ≫ f.toRationalMap.toPartialMap.hom, key, ?_⟩
  have : IsDominant w := ⟨hd⟩
  exact ext_of_isDominant w (by rw [← Category.assoc, key, hu])

lemma valuationRing_stalk (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (x : Spec (CommRingCat.of R)) : ValuationRing ((Spec (CommRingCat.of R)).presheaf.stalk x) := by
  letI : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk x) :=
    StructureSheaf.stalkAlgebra R x
  have : x.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := R) x
  have : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk x) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R x
  have : IsPrincipalIdealRing ((Spec (CommRingCat.of R)).presheaf.stalk x) := ⟨fun J => by
    rw [← IsLocalization.map_under x.asIdeal.primeCompl _ J]
    obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal (J.under R)).principal
    rw [ha]
    exact ⟨⟨_, by rw [Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton]⟩⟩⟩
  exact ValuationRing.iff_local_bezout_domain.2 ⟨inferInstance, inferInstance⟩

variable {K : Type} [Field K] {B : Over (Spec (CommRingCat.of K))}

lemma comp_aevalTower {R A A' : Type} [CommRing R] [Algebra K R] [CommRing A] [Algebra K A]
    [CommRing A'] [Algebra K A'] (g : A →ₐ[K] A') (c : R →ₐ[K] A) (x : A) :
    g.comp (aevalTower c x) = aevalTower (g.comp c) (g x) := by
  apply Polynomial.algHom_ext'
  · ext r
    simp
  · simp

lemma aevalTower_apply' {R A : Type} [CommRing R] [Algebra K R] [CommRing A] [Algebra K A]
    (c : R →ₐ[K] A) (x : A) (a : R[X]) : aevalTower c x a = eval₂ (c : R →+* A) x a := rfl

noncomputable def val {R A : Type} [CommRing R] [Algebra K R] [CommRing A] [Algebra K A]
    (F : sp K R[X] ⟶ B) (c : R →ₐ[K] A) (x : A) : sp K A ⟶ B :=
  spm (aevalTower c x) ≫ F

lemma spm_val {R A A' : Type} [CommRing R] [Algebra K R] [CommRing A] [Algebra K A]
    [CommRing A'] [Algebra K A'] (F : sp K R[X] ⟶ B) (g : A →ₐ[K] A') (c : R →ₐ[K] A) (x : A) :
    spm g ≫ val F c x = val F (g.comp c) (g x) := by
  rw [val, ← Category.assoc, spm_comp, comp_aevalTower, val]

lemma val_val {R S A : Type} [CommRing R] [Algebra K R] [CommRing S] [Algebra K S] [CommRing A]
    [Algebra K A] (F : sp K R[X] ⟶ B) (c : R →ₐ[K] S[X]) (x : S[X]) (d : S →ₐ[K] A) (y : A) :
    val (val F c x) d y = val F ((aevalTower d y).comp c) (aevalTower d y x) :=
  spm_val F _ c x

def Glue {R : Type} [CommRing R] [Algebra K R] (F G : sp K R[X] ⟶ B) : Prop :=
  ∀ (A : Type) [Field A] [Algebra K A] (c : R →ₐ[K] A) (x : A), x ≠ 0 → val F c x = val G c x⁻¹

lemma Glue.symm {R : Type} [CommRing R] [Algebra K R] {F G : sp K R[X] ⟶ B} (h : Glue F G) :
    Glue G F := fun A _ _ c x hx => by
  rw [h A c x⁻¹ (inv_ne_zero hx), inv_inv]

lemma exists_poly {R L : Type} [CommRing R] [Algebra K R] [Field L] [Algebra K L]
    (F : sp K R[X] ⟶ B) (V : B.left.Opens) (e : R →ₐ[K] L) (he : Function.Surjective e)
    (hF : ∀ q, (val F (CAlgHom.comp e) (X : L[X])).left q ∈ V) :
    ∃ a : R[X], a.map (e : R →+* L) = 1 ∧ ∀ (A : Type) [Field A] [Algebra K A] (c : R →ₐ[K] A) (x : A) (q),
      (val F c x).left q ∉ V → eval₂ (c : R →+* A) x a = 0 := by
  let Z : Set (PrimeSpectrum R[X]) := F.left ⁻¹' (V : Set B.left)ᶜ
  have hZ : IsClosed Z := V.2.isClosed_compl.preimage F.left.continuous
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal Z).1 hZ
  let φ : R[X] →+* L[X] := (aevalTower (CAlgHom.comp e) (X : L[X])).toRingHom
  have hφ : φ = mapRingHom (e : R →+* L) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [φ]
    · simp [φ]
  have htop : I.map φ = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have h1 : PrimeSpectrum.comap φ ⟨m, hm.isPrime⟩ ∈ Z := by
      rw [hI]
      exact Ideal.map_le_iff_le_comap.1 hle
    exact h1 (hF ⟨m, hm.isPrime⟩)
  have hs : Function.Surjective φ := by
    rw [hφ]
    exact Polynomial.map_surjective _ he
  obtain ⟨a, ha, ha1⟩ := (Ideal.mem_map_iff_of_surjective φ hs).1 (htop ▸ Submodule.mem_top : (1 : L[X]) ∈ I.map φ)
  refine ⟨a, by rw [← ha1, hφ]; rfl, fun A _ _ c x (q : PrimeSpectrum A) hq => ?_⟩
  have h1 : PrimeSpectrum.comap (aevalTower c x).toRingHom q ∈ Z := hq
  rw [hI] at h1
  have h2 : aevalTower c x a ∈ q.asIdeal := h1 ha
  rw [Ideal.eq_bot_of_prime q.asIdeal] at h2
  exact h2

lemma exists_good {R L : Type} [CommRing R] [Algebra K R] [Field L] [Algebra K L]
    {F G : sp K R[X] ⟶ B} (h : Glue F G) (V : B.left.Opens) (e : R →ₐ[K] L)
    (he : Function.Surjective e)
    (hF : ∀ q, (val F (CAlgHom.comp e) (X : L[X])).left q ∈ V)
    (hG : ∀ q, (val G (CAlgHom.comp e) (X : L[X])).left q ∈ V) :
    ∃ g : R, e g ≠ 0 ∧ ∀ (A : Type) [Field A] [Algebra K A] (c : R →ₐ[K] A), c g ≠ 0 →
      ∀ q, (val F (CAlgHom.comp c) (X : A[X])).left q ∈ V := by
  obtain ⟨a, ha, ha'⟩ := exists_poly F V e he hF
  obtain ⟨b, hb, hb'⟩ := exists_poly G V e he hG
  obtain ⟨g, hg, hg'⟩ := exists_elim (e : R →+* L) a b ha hb
  refine ⟨g, hg, fun A _ _ c hc (q : PrimeSpectrum A[X]) => ?_⟩
  let κ := q.asIdeal.ResidueField
  let π : A[X] →ₐ[K] κ := IsScalarTower.toAlgHom K A[X] κ
  let o : PrimeSpectrum κ := ⟨⊥, Ideal.isPrime_bot⟩
  have hq : (spm π).left o = q := by
    apply PrimeSpectrum.ext
    exact Ideal.ker_algebraMap_residueField q.asIdeal
  have h1 : (val F (π.comp (CAlgHom.comp c)) (π X)).left o =
      (val F (CAlgHom.comp c) (X : A[X])).left q := by
    rw [← spm_val]
    exact congrArg (val F (CAlgHom.comp c) (X : A[X])).left hq
  by_contra hn
  rw [← h1] at hn
  have h2 := hg' κ _ (π X) (ha' κ _ _ o hn) (fun hx => hb' κ _ _ o (by rwa [← h κ _ _ hx]))
  exact hc (((π.comp CAlgHom : A →ₐ[K] κ) : A →+* κ).injective (h2.trans (map_zero _).symm))

lemma val_eq_of_affine {A : Type} [Field A] [Algebra K A] {F G : sp K A[X] ⟶ B} (h : Glue F G)
    (V : B.left.Opens) (hV : IsAffineOpen V) (hF : ∀ q, F.left q ∈ V) (hG : ∀ q, G.left q ∈ V)
    (x y : A) : val F (AlgHom.id K A) x = val F (AlgHom.id K A) y := by
  have lift : ∀ H : sp K A[X] ⟶ B, (∀ q, H.left q ∈ V) →
      ∃ φ : Γ(B.left, V) ⟶ CommRingCat.of A[X], Spec.map φ ≫ hV.fromSpec = H.left := by
    intro H hH
    have hr : Set.range H.left ⊆ Set.range hV.fromSpec := by
      rw [hV.range_fromSpec]
      rintro _ ⟨q, rfl⟩
      exact hH q
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hV.fromSpec H.left hr)
    exact ⟨φ, by rw [hφ]; exact IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨φ, hφ⟩ := lift F hF
  obtain ⟨ψ, hψ⟩ := lift G hG
  let E := FractionRing A[X]
  let t : E := algebraMap A[X] E X
  have ht : t ≠ 0 := fun h0 => X_ne_zero (IsFractionRing.injective A[X] E
    (h0.trans (map_zero _).symm))
  let c : A →ₐ[K] E := IsScalarTower.toAlgHom K A E
  have h1 : Spec.map (CommRingCat.ofHom (aevalTower c t).toRingHom) ≫ F.left =
      Spec.map (CommRingCat.ofHom (aevalTower c t⁻¹).toRingHom) ≫ G.left :=
    congrArg CommaMorphism.left (h E c t ht)
  rw [← hφ, ← hψ, ← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp,
    ← Spec.map_comp] at h1
  have h2 := Spec.map_injective h1
  have h3 : ∀ s, (φ.hom s).natDegree = 0 := by
    intro s
    apply natDegree_eq_zero_of_inv _ (ψ.hom s)
    have h4 : eval₂ (algebraMap A E) t (φ.hom s) = eval₂ (algebraMap A E) t⁻¹ (ψ.hom s) :=
      congrArg (fun g : Γ(B.left, V) ⟶ CommRingCat.of E => g.hom s) h2
    rw [← h4, ← aeval_def, aeval_algebraMap_apply, aeval_X_left_apply]
  ext1
  change Spec.map (CommRingCat.ofHom (aevalTower (AlgHom.id K A) x).toRingHom) ≫ F.left =
    Spec.map (CommRingCat.ofHom (aevalTower (AlgHom.id K A) y).toRingHom) ≫ F.left
  rw [← hφ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext s
  change aevalTower (AlgHom.id K A) x (φ.hom s) = aevalTower (AlgHom.id K A) y (φ.hom s)
  rw [eq_C_of_natDegree_eq_zero (h3 s), aevalTower_C, aevalTower_C]

section group
variable [GrpObj B] {L R : Type} [Field L] [Algebra K L] [CommRing R] [Algebra K R]

noncomputable def twist (b : sp K L[X] ⟶ B) (i : L →ₐ[K] R) (s : R) : sp K R[X] ⟶ B :=
  val b (CAlgHom.comp i) (C s * X) * (val b (CAlgHom.comp i) X)⁻¹

lemma val_twist (b : sp K L[X] ⟶ B) (i : L →ₐ[K] R) (s : R) {A : Type} [CommRing A] [Algebra K A]
    (c : R →ₐ[K] A) (x : A) :
    val (twist b i s) c x = val b (c.comp i) (c s * x) * (val b (c.comp i) x)⁻¹ := by
  have h : (aevalTower c x).comp (CAlgHom.comp i) = c.comp i := by
    ext a
    simp
  rw [val, twist, MonObj.comp_mul, GrpObj.comp_inv, spm_val, spm_val, h, map_mul, aevalTower_C,
    aevalTower_X]

lemma val_unit_eq [IsSeparated B.hom] [IsDomain R] {b b' : sp K L[X] ⟶ B} (h : Glue b b')
    (i : L →ₐ[K] R) (t : Rˣ) (e : R →ₐ[K] L) (he : Function.Surjective e) (het : e t = 1) :
    val b i (t : R) = val b i 1 := by
  have het' : e (t⁻¹ : Rˣ) = 1 := by
    have := congrArg e t.mul_inv
    rwa [map_mul, het, _root_.one_mul, map_one] at this
  have hg : Glue (twist b i t) (twist b' i (t⁻¹ : Rˣ)) := by
    intro A _ _ c x hx
    have h1 : c t * c (t⁻¹ : Rˣ) = 1 := by rw [← map_mul, t.mul_inv, map_one]
    have h2 : c t ≠ 0 := left_ne_zero_of_mul_eq_one h1
    rw [val_twist, val_twist, h A _ _ (mul_ne_zero h2 hx), h A _ _ hx, mul_inv,
      eq_inv_of_mul_eq_one_right h1]
  let o : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  obtain ⟨_, ⟨V, hV, rfl⟩, hoV, -⟩ := B.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (η[B].left o)) isOpen_univ
  have h1 : ∀ (b : sp K L[X] ⟶ B) (s : R), e s = 1 →
      ∀ q, (val (twist b i s) (CAlgHom.comp e) (X : L[X])).left q ∈ V := by
    intro b s hs q
    rw [val_twist, AlgHom.comp_apply, hs, map_one, _root_.one_mul, mul_inv_cancel, Hom.one_def]
    have : (toUnit (sp K L[X])).left q = o := Subsingleton.elim (α := Spec (CommRingCat.of K)) _ _
    change η[B].left ((toUnit (sp K L[X])).left q) ∈ V
    rw [this]
    exact hoV
  obtain ⟨g, hg1, hg2⟩ := exists_good hg V e he (h1 _ _ het) (h1 _ _ het')
  obtain ⟨g', hg1', hg2'⟩ := exists_good hg.symm V e he (h1 _ _ het') (h1 _ _ het)
  let E := FractionRing R
  let c : R →ₐ[K] E := IsScalarTower.toAlgHom K R E
  have hc : Function.Injective c := IsFractionRing.injective R E
  have hne : ∀ r, e r ≠ 0 → c r ≠ 0 := fun r hr h0 =>
    hr (by rw [hc (h0.trans (map_zero c).symm), map_zero])
  have hcomp : ∀ (A : Type) [CommRing A] [Algebra K A] (d : E →ₐ[K] A) (x : A),
      (aevalTower d x).comp (CAlgHom.comp c) = d.comp c := by
    intro A _ _ d x
    ext a
    simp
  have hg' : Glue (val (twist b i t) (CAlgHom.comp c) (X : E[X]))
      (val (twist b' i (t⁻¹ : Rˣ)) (CAlgHom.comp c) (X : E[X])) := by
    intro A _ _ d x hx
    rw [val_val, val_val, hcomp, hcomp, aevalTower_X, aevalTower_X, hg A _ _ hx]
  have key := val_eq_of_affine hg' V hV (hg2 E c (hne _ hg1)) (hg2' E c (hne _ hg1')) 1 0
  rw [val_val, val_val, hcomp, hcomp, aevalTower_X, aevalTower_X, val_twist, val_twist,
    mul_zero, mul_inv_cancel, _root_.mul_one, mul_inv_eq_one] at key
  apply point_ext c hc
  rw [spm_val, spm_val, map_one]
  exact key

end group

section laurent
open LaurentPolynomial
variable {L : Type} [Field L] [Algebra K L]

noncomputable def ev {A : Type} [CommRing A] [Algebra K A] (c : L →ₐ[K] A) (x : Aˣ) :
    L[T;T⁻¹] →ₐ[K] A where
  toRingHom := LaurentPolynomial.eval₂ (c : L →+* A) x
  commutes' r := by
    change LaurentPolynomial.eval₂ (c : L →+* A) x (LaurentPolynomial.C (algebraMap K L r)) = _
    rw [LaurentPolynomial.eval₂_C]
    exact c.commutes r

variable (K L) in

noncomputable def inc : L[X] →ₐ[K] L[T;T⁻¹] := (toLaurentAlg : L[X] →ₐ[L] L[T;T⁻¹]).restrictScalars K

variable (K L) in

noncomputable def cst : L →ₐ[K] L[T;T⁻¹] := (inc K L).comp CAlgHom

variable (L) in

noncomputable def tU : (L[T;T⁻¹])ˣ := (isUnit_T (R := L) 1).unit

lemma ev_comp_inc {A : Type} [CommRing A] [Algebra K A] (c : L →ₐ[K] A) (x : Aˣ) :
    (ev c x).comp (inc K L) = aevalTower c (x : A) :=
  AlgHom.ext fun p => eval₂_toLaurent _ _ p

lemma ev_comp_cst {A : Type} [CommRing A] [Algebra K A] (c : L →ₐ[K] A) (x : Aˣ) :
    (ev c x).comp (cst K L) = c := by
  rw [cst, ← AlgHom.comp_assoc, ev_comp_inc]
  ext a
  simp

lemma ev_tU {A : Type} [CommRing A] [Algebra K A] (c : L →ₐ[K] A) (x : Aˣ) :
    ev c x (tU L) = x := by
  change LaurentPolynomial.eval₂ (c : L →+* A) x (T 1) = _
  rw [eval₂_T, zpow_one]

lemma comp_ev {A A' : Type} [CommRing A] [Algebra K A] [CommRing A'] [Algebra K A']
    (g : A →ₐ[K] A') (c : L →ₐ[K] A) (x : Aˣ) :
    g.comp (ev c x) = ev (g.comp c) (Units.map (g : A →* A') x) := by
  have h : (g.comp (ev c x)).comp (inc K L) =
      (ev (g.comp c) (Units.map (g : A →* A') x)).comp (inc K L) := by
    rw [AlgHom.comp_assoc, ev_comp_inc, ev_comp_inc, comp_aevalTower]
    rfl
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (X : L[X]))
  exact RingHom.ext fun p => AlgHom.congr_fun h p

lemma exists_extension_line [IsProper B.hom] (u : sp K L[T;T⁻¹] ⟶ B) :
    ∃ b : sp K L[X] ⟶ B, spm (inc K L) ≫ b = u := by
  have h1 : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap L[X] L[T;T⁻¹]))) :=
    IsOpenImmersion.of_isLocalization (X : L[X])
  have h2 : B.left.IsSeparated := ⟨by
    rw [← terminal.comp_from B.hom]
    infer_instance⟩
  obtain ⟨g, hg, hg'⟩ := exists_extension (valuationRing_stalk L[X])
    (Spec.map (CommRingCat.ofHom (algebraMap L[X] L[T;T⁻¹]))) (sp K L[X]).hom B.hom u.left
    ((Over.w u).trans (Over.w (spm (inc K L))).symm)
  exact ⟨Over.homMk g hg', by ext1; exact hg⟩

lemma ev_eq [GrpObj B] [IsProper B.hom] (u : sp K L[T;T⁻¹] ⟶ B) (x y : Lˣ) :
    spm (ev (AlgHom.id K L) x) ≫ u = spm (ev (AlgHom.id K L) y) ≫ u := by
  obtain ⟨b, hb⟩ := exists_extension_line u
  obtain ⟨b', hb'⟩ := exists_extension_line (spm (ev (cst K L) (tU L)⁻¹) ≫ u)
  have h1 : ∀ (u : sp K L[T;T⁻¹] ⟶ B) (b : sp K L[X] ⟶ B), spm (inc K L) ≫ b = u →
      ∀ (A : Type) [CommRing A] [Algebra K A] (c : L →ₐ[K] A) (x : Aˣ),
        val b c (x : A) = spm (ev c x) ≫ u := by
    intro u b hb A _ _ c x
    rw [← hb, ← Category.assoc, spm_comp, ev_comp_inc, val]
  have hg : Glue b b' := by
    intro A _ _ c x hx
    have e1 := h1 _ _ hb A c (Units.mk0 x hx)
    have e2 := h1 _ _ hb' A c (Units.mk0 x hx)⁻¹
    rw [← Category.assoc, spm_comp, comp_ev, ev_comp_cst, map_inv] at e2
    have e3 : Units.map (ev c (Units.mk0 x hx)⁻¹ : L[T;T⁻¹] →* A) (tU L) = (Units.mk0 x hx)⁻¹ :=
      Units.ext (ev_tU _ _)
    rw [e3, inv_inv] at e2
    simpa using e1.trans e2.symm
  have key := val_unit_eq hg (cst K L) (tU L) (ev (AlgHom.id K L) 1)
    (fun a => ⟨cst K L a, AlgHom.congr_fun (ev_comp_cst (AlgHom.id K L) 1) a⟩) (ev_tU _ _)
  have h2 : ∀ x : Lˣ, spm (ev (AlgHom.id K L) x) ≫ u = val b (AlgHom.id K L) 1 := by
    intro x
    have := congrArg (spm (ev (AlgHom.id K L) x) ≫ ·) key
    simp only [spm_val, ev_comp_cst, ev_tU, map_one] at this
    rw [← this, h1 _ _ hb]
  rw [h2, h2]

end laurent

theorem eq_const (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] [GrpObj B]
    [IsProper B.hom] (f : splitTorus (Spec (CommRingCat.of K)) Y ⟶ B) :
    f = toUnit _ ≫ η ≫ f := by
  have h1 : ∀ (L : Type) [Field L] [Algebra K L] (φ : Multiplicative Y →* Lˣ) (l : Y →+ ℤ) (x : Lˣ),
      pt K Y L (coch l Lˣ x * φ) ≫ f = pt K Y L φ ≫ f := by
    intro L _ _ φ l x
    let ψ : Multiplicative Y →* (LaurentPolynomial L)ˣ :=
      coch l _ (tU L) * (Units.map (cst K L : L →* LaurentPolynomial L)).comp φ
    have h2 : ∀ x : Lˣ, spm (ev (AlgHom.id K L) x) ≫ pt K Y _ ψ = pt K Y L (coch l Lˣ x * φ) := by
      intro x
      rw [← pt_nat]
      congr 1
      refine MonoidHom.ext fun a => ?_
      have e1 : Units.map (ev (AlgHom.id K L) x : LaurentPolynomial L →* L) (tU L) = x :=
        Units.ext (ev_tU _ _)
      have e2 : Units.map (ev (AlgHom.id K L) x : LaurentPolynomial L →* L)
          (Units.map (cst K L : L →* LaurentPolynomial L) (φ a)) = φ a :=
        Units.ext (AlgHom.congr_fun (ev_comp_cst (AlgHom.id K L) x) _)
      change Units.map (ev (AlgHom.id K L) x : LaurentPolynomial L →* L)
        (tU L ^ l a.toAdd * Units.map (cst K L : L →* LaurentPolynomial L) (φ a)) =
        x ^ l a.toAdd * φ a
      rw [map_mul, map_zpow, e1, e2]
    have h3 := ev_eq (pt K Y _ ψ ≫ f) x 1
    rwa [← Category.assoc, ← Category.assoc, h2, h2, map_one, _root_.one_mul] at h3
  have h2 : ∀ (L : Type) [Field L] [Algebra K L] (φ : Multiplicative Y →* Lˣ),
      pt K Y L φ ≫ f = pt K Y L 1 ≫ f := by
    intro L _ _ φ
    rw [char_eq_prod Y (Module.Free.chooseBasis ℤ Y) _ φ]
    generalize (Finset.univ : Finset (Module.Free.ChooseBasisIndex ℤ Y)) = s
    classical
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty]
    | insert i s hi ih => rw [Finset.prod_insert hi, h1, ih]
  have : IsDomain (AddMonoidAlgebra K Y) := NoZeroDivisors.to_isDomain _
  let R := AddMonoidAlgebra K Y
  let F := FractionRing R
  have h3 : pt K Y R (univ K Y) ≫ f = pt K Y R (univ K Y) ≫ toUnit _ ≫ η ≫ f := by
    apply point_ext (IsScalarTower.toAlgHom K R F) (IsFractionRing.injective R F)
    rw [← Category.assoc, ← pt_nat, h2, map_one, Hom.one_def, Category.assoc, ← Category.assoc,
      ← Category.assoc (spm _), ← Category.assoc (spm _ ≫ _), Category.assoc (toUnit _)]
    congr 1
    exact toUnit_unique _ _
  have h4 : (pt K Y R (univ K Y)).left ≫ f.left =
      (pt K Y R (univ K Y)).left ≫ (toUnit _ ≫ η ≫ f).left := congrArg CommaMorphism.left h3
  rw [pt_univ] at h4
  ext1
  exact (cancel_epi _).1 h4

end TorusConst

theorem splitTorus_to_abelian_const : ∀ (K : Type) [Field K] [IsAlgClosed K] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ f : splitTorus (Sp K) X ⟶ B, ∃ b : 𝟙_ (Over (Sp K)) ⟶ B, f = toUnit _ ≫ b := by
  intro K _ _ X _ _ _ B _ hB f
  have := hB.proper
  exact ⟨η ≫ f, TorusConst.eq_const X f⟩

end GlobalTheory
