import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.WeilBound.CoreStatements.AmpleLineBundles.SquareZeroDeformationAdditivity
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

private theorem isHecke_div_and_resEtaPow_div {P G1 : Scheme.{0}} (π1 π2 : P ⟶ G1)
    (hmono : ∀ (T : Scheme.{0}) (f1 f2 : T ⟶ P), f1 ≫ π1 = f2 ≫ π1 → f1 ≫ π2 = f2 ≫ π2 → f1 = f2)
    (C : Type) [CommRing C] [IsLocalRing C] (J : Ideal C) (hJ : J ^ 2 = ⊥)
    (u1 u2 u3 u4 : Spec (CommRingCat.of C) ⟶ P)
    (h12 : u1 ≫ π1 = u2 ≫ π1) (h34 : u3 ≫ π1 = u4 ≫ π1)
    (h13 : u1 ≫ π2 = u3 ≫ π2) (h24 : u2 ≫ π2 = u4 ≫ π2)
    (e1 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u1 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u4)
    (e2 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u2 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u4)
    (e3 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u3 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u4)
    (O : P.Opens) (o1 : ⊤ ≤ u1 ⁻¹ᵁ O) (o2 : ⊤ ≤ u2 ⁻¹ᵁ O) (o3 : ⊤ ≤ u3 ⁻¹ᵁ O)
    (o4 : ⊤ ≤ u4 ⁻¹ᵁ O) (s : Γ(P, O)) :
    (u1.appLE O ⊤ o1).hom s + (u4.appLE O ⊤ o4).hom s =
      (u2.appLE O ⊤ o2).hom s + (u3.appLE O ⊤ o3).hom s := by
  have appLE_eq : ∀ {X Y : Scheme.{0}} (f g : X ⟶ Y), f = g → ∀ (U : Y.Opens) (V : X.Opens)
      (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U), f.appLE U V e = g.appLE U V e' := by
    intro X Y f g h U V e e'
    subst h
    rfl
  have hJP : ∀ (Q : Ideal C), Q.IsPrime → J ≤ Q := by
    intro Q hQ z hz
    have hz2 : z ^ 2 ∈ J ^ 2 := Ideal.pow_mem_pow hz 2
    rw [hJ, Ideal.mem_bot] at hz2
    exact hQ.mem_of_pow_mem 2 (hz2 ▸ Q.zero_mem)
  have hsurj : ∀ t : PrimeSpectrum C, ∃ t' : PrimeSpectrum (C ⧸ J),
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))).base t' = t := by
    intro t
    have : (t.asIdeal.map (Ideal.Quotient.mk J)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hJP _ t.2)
    refine ⟨⟨t.asIdeal.map (Ideal.Quotient.mk J), this⟩, ?_⟩
    apply PrimeSpectrum.ext
    show Ideal.comap (Ideal.Quotient.mk J) (t.asIdeal.map (Ideal.Quotient.mk J)) = t.asIdeal
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker]
    exact sup_eq_left.mpr (hJP _ t.2)
  have hpt : ∀ (u : Spec (CommRingCat.of C) ⟶ P),
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u4 →
      ∀ t : PrimeSpectrum C, u.base t = u4.base t := by
    intro u hu t
    obtain ⟨t', rfl⟩ := hsurj t
    exact congrArg (fun h => h.base t') hu
  let c : PrimeSpectrum C := IsLocalRing.closedPoint C
  have hc4 : u4.base c ∈ O := o4 trivial
  obtain ⟨W1, hW1, hpW1, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := π1.base (u4.base c)) (U := ⊤) trivial
  obtain ⟨W2, hW2, hpW2, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := π2.base (u4.base c)) (U := ⊤) trivial
  obtain ⟨Z, hZ, hpZ, hZsub⟩ := exists_isAffineOpen_mem_and_subset
    (x := u4.base c) (U := O ⊓ π1 ⁻¹ᵁ W1 ⊓ π2 ⁻¹ᵁ W2) ⟨⟨hc4, hpW1⟩, hpW2⟩
  have hZO : Z ≤ O := fun z hz => (hZsub hz).1.1
  have hZ1 : Z ≤ π1 ⁻¹ᵁ W1 := fun z hz => (hZsub hz).1.2
  have hZ2 : Z ≤ π2 ⁻¹ᵁ W2 := fun z hz => (hZsub hz).2
  have hZk : ∀ (u : Spec (CommRingCat.of C) ⟶ P), (∀ t : PrimeSpectrum C, u.base t = u4.base t) →
      ⊤ ≤ u ⁻¹ᵁ Z := by
    intro u hu t _
    show u.base t ∈ Z
    rw [hu t]
    exact ((IsLocalRing.specializes_closedPoint (R := C) t).map u4.base.hom.continuous).mem_open
      Z.isOpen hpZ
  have z1 := hZk u1 (hpt u1 e1)
  have z2 := hZk u2 (hpt u2 e2)
  have z3 := hZk u3 (hpt u3 e3)
  have z4 := hZk u4 (fun _ => rfl)
  have key : ∀ (w : Spec (CommRingCat.of C) ⟶ P) (hw : ⊤ ≤ w ⁻¹ᵁ Z),
      w.appLE Z ⊤ hw ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom ≫
          CommRingCat.ofHom (Ideal.Quotient.mk J) =
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ w).appLE Z ⊤ (fun _ _ => hw trivial) ≫
          (Scheme.ΓSpecIso (CommRingCat.of (C ⧸ J))).hom := by
    intro w hw
    rw [← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) w Z ⊤ ⊤ hw
      (fun _ _ => trivial), Category.assoc, ← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE]
    rfl
  have hmod : ∀ (u : Spec (CommRingCat.of C) ⟶ P) (hu : ⊤ ≤ u ⁻¹ᵁ Z),
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u4 →
      ∀ v, (u.appLE Z ⊤ hu ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom v -
        (u4.appLE Z ⊤ z4 ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom v ∈ J := by
    intro u hu he v
    rw [← Ideal.Quotient.eq]
    have k1 := congrArg (fun φ => φ.hom v) (key u hu)
    have k4 := congrArg (fun φ => φ.hom v) (key u4 z4)
    have k := appLE_eq _ _ he Z ⊤ (fun _ _ => hu trivial) (fun _ _ => z4 trivial)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at k1 k4 ⊢
    rw [k1, k4, k]
  obtain ⟨a1, ha1⟩ : ∃ a : Γ(P, Z) →+* C,
    a = (u1.appLE Z ⊤ z1 ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a : Γ(P, Z) →+* C,
    a = (u2.appLE Z ⊤ z2 ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom := ⟨_, rfl⟩
  obtain ⟨a3, ha3⟩ : ∃ a : Γ(P, Z) →+* C,
    a = (u3.appLE Z ⊤ z3 ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom := ⟨_, rfl⟩
  obtain ⟨a4, ha4⟩ : ∃ a : Γ(P, Z) →+* C,
    a = (u4.appLE Z ⊤ z4 ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom := ⟨_, rfl⟩
  have d1 : ∀ v, a1 v - a4 v ∈ J := by rw [ha1, ha4]; exact hmod u1 z1 e1
  have d2 : ∀ v, a2 v - a4 v ∈ J := by rw [ha2, ha4]; exact hmod u2 z2 e2
  have d3 : ∀ v, a3 v - a4 v ∈ J := by rw [ha3, ha4]; exact hmod u3 z3 e3
  have hsq : ∀ a b : C, a ∈ J → b ∈ J → a * b = 0 := by
    intro a b ha hb
    have hab : a * b ∈ J ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
    rw [hJ] at hab
    exact (Ideal.mem_bot).mp hab
  let ψ : Γ(P, Z) →+* C :=
    { toFun := fun v => a1 v - a2 v - a3 v + a4 v + a4 v
      map_one' := by simp only [map_one]; ring
      map_mul' := by
        intro v w
        simp only [map_mul]
        have z11 := hsq _ _ (d1 v) (d1 w)
        have z12 := hsq _ _ (d1 v) (d2 w)
        have z13 := hsq _ _ (d1 v) (d3 w)
        have z21 := hsq _ _ (d2 v) (d1 w)
        have z22 := hsq _ _ (d2 v) (d2 w)
        have z23 := hsq _ _ (d2 v) (d3 w)
        have z31 := hsq _ _ (d3 v) (d1 w)
        have z32 := hsq _ _ (d3 v) (d2 w)
        have z33 := hsq _ _ (d3 v) (d3 w)
        linear_combination z11 - z22 - z33 -
          (z11 - z12 - z13 - z21 + z22 + z23 - z31 + z32 + z33)
      map_zero' := by simp only [map_zero]; ring
      map_add' := by intro v w; simp only [map_add]; ring }
  have hc : ∀ (Wi : G1.Opens) (πi : P ⟶ G1) (hi : Z ≤ πi ⁻¹ᵁ Wi)
      (u u' : Spec (CommRingCat.of C) ⟶ P) (hu : ⊤ ≤ u ⁻¹ᵁ Z) (hu' : ⊤ ≤ u' ⁻¹ᵁ Z),
      u ≫ πi = u' ≫ πi → ∀ r,
      (u.appLE Z ⊤ hu ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom ((πi.appLE Wi Z hi).hom r) =
        (u'.appLE Z ⊤ hu' ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom
          ((πi.appLE Wi Z hi).hom r) := by
    intro Wi πi hi u u' hu hu' h r
    have := congrArg (fun φ => (φ ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom r)
      ((Scheme.Hom.appLE_comp_appLE u πi Wi Z ⊤ hi hu).trans
        ((appLE_eq _ _ h Wi ⊤ _ _).trans
          (Scheme.Hom.appLE_comp_appLE u' πi Wi Z ⊤ hi hu').symm))
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using this
  have hside : ∀ (Wi : G1.Opens) (πi : P ⟶ G1) (hWi : IsAffineOpen Wi) (hi : Z ≤ πi ⁻¹ᵁ Wi),
      (∀ r, ψ ((πi.appLE Wi Z hi).hom r) = a4 ((πi.appLE Wi Z hi).hom r)) →
      (Spec.map (CommRingCat.ofHom ψ) ≫ hZ.fromSpec) ≫ πi =
        (Spec.map (CommRingCat.ofHom a4) ≫ hZ.fromSpec) ≫ πi := by
    intro Wi πi hWi hi hr
    rw [Category.assoc, Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec πi hWi hZ hi,
      ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    congr 2
    ext r
    exact hr r
  have hψ : CommRingCat.ofHom ψ = CommRingCat.ofHom a4 := by
    have hfrom : Spec.map (CommRingCat.ofHom ψ) ≫ hZ.fromSpec =
        Spec.map (CommRingCat.ofHom a4) ≫ hZ.fromSpec := by
      apply hmono
      · apply hside W1 π1 hW1 hZ1
        intro r
        have q12 := hc W1 π1 hZ1 u1 u2 z1 z2 h12 r
        have q34 := hc W1 π1 hZ1 u3 u4 z3 z4 h34 r
        rw [← ha1, ← ha2] at q12
        rw [← ha3, ← ha4] at q34
        show a1 _ - a2 _ - a3 _ + a4 _ + a4 _ = a4 _
        rw [q12, q34]
        ring
      · apply hside W2 π2 hW2 hZ2
        intro r
        have q13 := hc W2 π2 hZ2 u1 u3 z1 z3 h13 r
        have q24 := hc W2 π2 hZ2 u2 u4 z2 z4 h24 r
        rw [← ha1, ← ha3] at q13
        rw [← ha2, ← ha4] at q24
        show a1 _ - a2 _ - a3 _ + a4 _ + a4 _ = a4 _
        rw [q13, q24]
        ring
    rw [cancel_mono] at hfrom
    exact Spec.map_inj.mp hfrom
  obtain ⟨s', hs'⟩ : ∃ s' : Γ(P, Z), s' = (P.presheaf.map (homOfLE hZO).op).hom s := ⟨_, rfl⟩
  have hfin : a1 s' - a2 s' - a3 s' + a4 s' = 0 := by
    have h := congrArg (fun φ => φ.hom s') hψ
    simp only [CommRingCat.hom_ofHom] at h
    change a1 s' - a2 s' - a3 s' + a4 s' + a4 s' = a4 s' at h
    linear_combination h
  have hres : ∀ (u : Spec (CommRingCat.of C) ⟶ P) (hu : ⊤ ≤ u ⁻¹ᵁ O) (hz : ⊤ ≤ u ⁻¹ᵁ Z),
      (u.appLE O ⊤ hu).hom s = (u.appLE Z ⊤ hz).hom s' := by
    intro u hu hz
    rw [hs', ← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]
  rw [hres u1 o1 z1, hres u2 o2 z2, hres u3 o3 z3, hres u4 o4 z4]
  apply (Scheme.ΓSpecIso (CommRingCat.of C)).commRingCatIsoToRingEquiv.injective
  simp only [map_add]
  have hiso : ∀ (u : Spec (CommRingCat.of C) ⟶ P) (hz : ⊤ ≤ u ⁻¹ᵁ Z),
      (Scheme.ΓSpecIso (CommRingCat.of C)).commRingCatIsoToRingEquiv ((u.appLE Z ⊤ hz).hom s') =
        (u.appLE Z ⊤ hz ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom s' := fun _ _ => rfl
  rw [hiso u1 z1, hiso u2 z2, hiso u3 z3, hiso u4 z4, ← ha1, ← ha2, ← ha3, ← ha4]
  linear_combination hfin

private theorem isPair_and_isPair_of_isTriple {P G1 : Scheme.{0}} (π1 π2 : P ⟶ G1)
    (hmono : ∀ (T : Scheme.{0}) (f1 f2 : T ⟶ P), f1 ≫ π1 = f2 ≫ π1 → f1 ≫ π2 = f2 ≫ π2 → f1 = f2)
    (A : Type) [CommRing A] (J : Ideal A) (hJ : J ^ 2 = ⊥)
    (u1 u2 u3 u4 : Spec (CommRingCat.of A) ⟶ P)
    (h12 : u1 ≫ π1 = u2 ≫ π1) (h34 : u3 ≫ π1 = u4 ≫ π1)
    (h13 : u1 ≫ π2 = u3 ≫ π2) (h24 : u2 ≫ π2 = u4 ≫ π2)
    (e1 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u1 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u4)
    (e2 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u2 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u4)
    (e3 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u3 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u4)
    (O : P.Opens) (o1 : ⊤ ≤ u1 ⁻¹ᵁ O) (o2 : ⊤ ≤ u2 ⁻¹ᵁ O) (o3 : ⊤ ≤ u3 ⁻¹ᵁ O)
    (o4 : ⊤ ≤ u4 ⁻¹ᵁ O) (s : Γ(P, O)) :
    (u1.appLE O ⊤ o1).hom s + (u4.appLE O ⊤ o4).hom s =
      (u2.appLE O ⊤ o2).hom s + (u3.appLE O ⊤ o3).hom s := by
  apply (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.injective
  have hiso : ∀ x, (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv x =
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom x := fun _ => rfl
  simp only [map_add, hiso]
  rw [← sub_eq_zero]
  apply eq_zero_of_localization
  intro m hm
  have natm : ∀ (u : Spec (CommRingCat.of A) ⟶ P) (hu : ⊤ ≤ u ⁻¹ᵁ O),
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime m))) ≫ u).appLE O ⊤
          (fun _ _ => hu trivial) ≫ (Scheme.ΓSpecIso (CommRingCat.of (Localization.AtPrime m))).hom =
        u.appLE O ⊤ hu ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫
          CommRingCat.ofHom (algebraMap A (Localization.AtPrime m)) := by
    intro u hu
    rw [← Scheme.Hom.appLE_comp_appLE (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime m))))
      u O ⊤ ⊤ hu (fun _ _ => trivial), Category.assoc, ← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE]
    rfl
  have natE : ∀ (u : Spec (CommRingCat.of A) ⟶ P) (hu : ⊤ ≤ u ⁻¹ᵁ O),
      (Scheme.ΓSpecIso (CommRingCat.of (Localization.AtPrime m))).hom.hom
          (((Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime m))) ≫ u).appLE O ⊤
            (fun _ _ => hu trivial)).hom s) =
        algebraMap A (Localization.AtPrime m)
          ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((u.appLE O ⊤ hu).hom s)) := by
    intro u hu
    have := congrArg (fun φ => φ.hom s) (natm u hu)
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using this
  have hsq : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map (algebraMap A (Localization.AtPrime m))))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime m))) =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (J.map (algebraMap A (Localization.AtPrime m)))
        (algebraMap A (Localization.AtPrime m)) Ideal.le_comap_map)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have he : ∀ (u : Spec (CommRingCat.of A) ⟶ P),
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ u4 →
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map (algebraMap A (Localization.AtPrime m))))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime m))) ≫ u =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J.map (algebraMap A (Localization.AtPrime m))))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime m))) ≫ u4 := by
    intro u hu
    rw [← Category.assoc, hsq, Category.assoc, hu, ← Category.assoc, ← hsq, Category.assoc]
  have hloc := isHecke_div_and_resEtaPow_div π1 π2 hmono (Localization.AtPrime m) (J.map (algebraMap A (Localization.AtPrime m)))
    (by rw [← Ideal.map_pow, hJ, Ideal.map_bot])
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime m))) ≫ u1)
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime m))) ≫ u2)
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime m))) ≫ u3)
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.AtPrime m))) ≫ u4)
    (by simp only [Category.assoc, h12]) (by simp only [Category.assoc, h34])
    (by simp only [Category.assoc, h13]) (by simp only [Category.assoc, h24])
    (he u1 e1) (he u2 e2) (he u3 e3) O
    (fun _ _ => o1 trivial) (fun _ _ => o2 trivial) (fun _ _ => o3 trivial) (fun _ _ => o4 trivial) s
  have h := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Localization.AtPrime m))).hom.hom hloc
  simp only [map_add] at h
  rw [natE u1 o1, natE u2 o2, natE u3 o3, natE u4 o4] at h
  rw [map_sub, map_add, map_add]
  linear_combination h

theorem sqzero_add : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (B : Type) [CommRing B] [IsLocalRing B] (b : Sp B ⟶ S) (A : Type) [CommRing A] (g : B →+* A) (J : Ideal A), J ^ 2 = ⊥ → ∀ x y : Over.mk (spMap g ≫ b) ⟶ G, spMap (Ideal.Quotient.mk J) ≫ x.left = spMap (Ideal.Quotient.mk J) ≫ (1 : Over.mk (spMap g ≫ b) ⟶ G).left → spMap (Ideal.Quotient.mk J) ≫ y.left = spMap (Ideal.Quotient.mk J) ≫ (1 : Over.mk (spMap g ≫ b) ⟶ G).left → ∀ (V : G.left.Opens) (hx : ⊤ ≤ x.left ⁻¹ᵁ V) (hy : ⊤ ≤ y.left ⁻¹ᵁ V) (hxy : ⊤ ≤ (x * y).left ⁻¹ᵁ V) (h1 : ⊤ ≤ (1 : Over.mk (spMap g ≫ b) ⟶ G).left ⁻¹ᵁ V) (f : Γ(G.left, V)), ((x * y).left.appLE V ⊤ hxy).hom f + ((1 : Over.mk (spMap g ≫ b) ⟶ G).left.appLE V ⊤ h1).hom f = (x.left.appLE V ⊤ hx).hom f + (y.left.appLE V ⊤ hy).hom f := by
  intro S G _ B _ _ b A _ g J hJ x y hx1 hy1 V hx hy hxy h1 f
  have hmono : ∀ (T : Scheme.{0}) (f1 f2 : T ⟶ (G ⊗ G).left), f1 ≫ (fst G G).left = f2 ≫ (fst G G).left →
      f1 ≫ (snd G G).left = f2 ≫ (snd G G).left → f1 = f2 :=
    fun T f1 f2 k1 k2 => Over.tensorObj_ext f1 f2 k1 k2
  have eq_of : ∀ (a c : Over.mk (spMap g ≫ b) ⟶ G),
      spMap (Ideal.Quotient.mk J) ≫ a.left =
        spMap (Ideal.Quotient.mk J) ≫ (1 : Over.mk (spMap g ≫ b) ⟶ G).left →
      spMap (Ideal.Quotient.mk J) ≫ c.left =
        spMap (Ideal.Quotient.mk J) ≫ (1 : Over.mk (spMap g ≫ b) ⟶ G).left →
      spMap (Ideal.Quotient.mk J) ≫ (lift a c).left =
        spMap (Ideal.Quotient.mk J) ≫ (lift (1 : Over.mk (spMap g ≫ b) ⟶ G) 1).left := by
    intro a c ha hc
    apply hmono
    · rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, ha]
    · rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, hc]
  have m1 : (lift x y).left ≫ (μ : G ⊗ G ⟶ G).left = (x * y).left := by
    rw [← Over.comp_left]
    rfl
  have m2 : (lift x 1).left ≫ (μ : G ⊗ G ⟶ G).left = x.left := by
    rw [← Over.comp_left]
    show (x * 1).left = x.left
    rw [_root_.mul_one]
  have m3 : (lift 1 y).left ≫ (μ : G ⊗ G ⟶ G).left = y.left := by
    rw [← Over.comp_left]
    show (1 * y).left = y.left
    rw [_root_.one_mul]
  have m4 : (lift (1 : Over.mk (spMap g ≫ b) ⟶ G) 1).left ≫ (μ : G ⊗ G ⟶ G).left =
      (1 : Over.mk (spMap g ≫ b) ⟶ G).left := by
    rw [← Over.comp_left]
    show ((1 : Over.mk (spMap g ≫ b) ⟶ G) * 1).left = _
    rw [_root_.mul_one]
  have oo : ∀ (u : (Over.mk (spMap g ≫ b)).left ⟶ (G ⊗ G).left) (w : (Over.mk (spMap g ≫ b)).left ⟶ G.left),
      u ≫ (μ : G ⊗ G ⟶ G).left = w → ⊤ ≤ w ⁻¹ᵁ V → ⊤ ≤ u ⁻¹ᵁ ((μ : G ⊗ G ⟶ G).left ⁻¹ᵁ V) := by
    intro u w h hw
    subst h
    exact hw
  have conv : ∀ (u : (Over.mk (spMap g ≫ b)).left ⟶ (G ⊗ G).left) (w : (Over.mk (spMap g ≫ b)).left ⟶ G.left)
      (h : u ≫ (μ : G ⊗ G ⟶ G).left = w) (hw : ⊤ ≤ w ⁻¹ᵁ V)
      (hu : ⊤ ≤ u ⁻¹ᵁ ((μ : G ⊗ G ⟶ G).left ⁻¹ᵁ V)),
      (w.appLE V ⊤ hw).hom f =
        (u.appLE ((μ : G ⊗ G ⟶ G).left ⁻¹ᵁ V) ⊤ hu).hom
          (((μ : G ⊗ G ⟶ G).left.appLE V ((μ : G ⊗ G ⟶ G).left ⁻¹ᵁ V) le_rfl).hom f) := by
    intro u w h hw hu
    subst h
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
  have o1 := oo _ _ m1 hxy
  have o2 := oo _ _ m2 hx
  have o3 := oo _ _ m3 hy
  have o4 := oo _ _ m4 h1
  rw [conv _ _ m1 hxy o1, conv _ _ m2 hx o2, conv _ _ m3 hy o3, conv _ _ m4 h1 o4]
  exact isPair_and_isPair_of_isTriple (fst G G).left (snd G G).left hmono A J hJ (lift x y).left (lift x 1).left (lift 1 y).left
    (lift (1 : Over.mk (spMap g ≫ b) ⟶ G) 1).left
    (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst])
    (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst])
    (by rw [← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd])
    (by rw [← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd])
    (eq_of x y hx1 hy1) (eq_of x 1 hx1 rfl) (eq_of 1 y rfl hy1)
    ((μ : G ⊗ G ⟶ G).left ⁻¹ᵁ V) o1 o2 o3 o4 _

end GlobalTheory.CompanionTheory.Ar
