import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CharAtOfMultiplicativeSeries
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCharactersBoundedMinorsOfHodgeTateChartBou
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenOfRangeGenericSubset
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HodgeTateInclusionChartCharacters
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AddOfPtPt

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompHt.FormalChar

open GlobalTheory.KernelNoTorsion GlobalTheory.TorsionCharacter GlobalTheory.TangentPow GlobalTheory.GmPoints

theorem exists_character_of_rel {N F : Type} [CommGroup N] [Field F] [IsAlgClosed F]
    (Rel : N → F → Prop) (h1 : Rel 1 1)
    (hmul : ∀ g g' c c', Rel g c → Rel g' c' → Rel (g * g') (c * c'))
    (huniq : ∀ g c c', Rel g c → Rel g c' → c = c') :
    ∃ κ : N →* Fˣ, ∀ g c (n : ℕ), n ≠ 0 → g ^ n = 1 → Rel g c → (κ g : F) = c := by
  have hpow : ∀ g c (n : ℕ), Rel g c → Rel (g ^ n) (c ^ n) := fun g c n h => by
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ, pow_succ]; exact hmul _ _ _ _ ih h
  let H : Subgroup N :=
    { carrier := {g | (∃ n : ℕ, n ≠ 0 ∧ g ^ n = 1) ∧ ∃ c, Rel g c}
      mul_mem' := by
        rintro a b ⟨⟨m, hm, ha⟩, c, hc⟩ ⟨⟨n, hn, hb⟩, c', hc'⟩
        exact ⟨⟨m * n, mul_ne_zero hm hn, by
          rw [mul_pow, pow_mul, ha, mul_comm m, pow_mul, hb, one_pow, one_pow, _root_.mul_one]⟩,
          _, hmul _ _ _ _ hc hc'⟩
      one_mem' := ⟨⟨1, one_ne_zero, one_pow _⟩, 1, h1⟩
      inv_mem' := by
        rintro a ⟨⟨n, hn, ha⟩, c, hc⟩
        have : a⁻¹ = a ^ (n - 1) := by
          rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hn), ha]
        exact ⟨⟨n, hn, by rw [inv_pow, ha, inv_one]⟩, _, this ▸ hpow _ _ _ hc⟩ }
  choose c hc using fun h : H => h.2.2
  have hc0 : ∀ h, c h ≠ 0 := fun h h0 => by
    obtain ⟨n, hn, e⟩ := h.2.1
    have := hpow _ _ n (hc h)
    rw [e, h0, zero_pow hn] at this
    exact zero_ne_one (huniq _ _ _ this h1)
  let χ : H →* Fˣ := MonoidHom.mk' (fun h => Units.mk0 (c h) (hc0 h)) fun a b =>
    Units.ext (huniq _ _ _ (hc (a * b)) (hmul _ _ _ _ (hc a) (hc b)))
  obtain ⟨κ, hκ⟩ := exists_extend_character H.subtype Subtype.val_injective χ
  refine ⟨κ, fun g k n hn hg hk => ?_⟩
  rw [show κ g = χ ⟨g, ⟨n, hn, hg⟩, k, hk⟩ from hκ ⟨g, ⟨n, hn, hg⟩, k, hk⟩]
  exact huniq _ _ _ (hc ⟨g, ⟨n, hn, hg⟩, k, hk⟩) hk

section Integers

variable {p : ℕ} {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]

theorem exists_pow_mem (hv : v.Integers O) {a b : O} (ha : ¬ IsUnit a) (hb : b ≠ 0) :
    ∃ n : ℕ, a ^ n ∈ Ideal.span {b} := by
  have h1 : v (algebraMap O C a) < 1 := lt_of_le_of_ne (hv.map_le_one a) fun e => ha (hv.isUnit_of_one' e)
  have h2 : 0 < v (algebraMap O C b) :=
    pos_iff_ne_zero.2 ((Valuation.ne_zero_iff v).2 ((map_ne_zero_iff _ hv.hom_inj).2 hb))
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one h2 h1
  exact ⟨n, Ideal.mem_span_singleton.2 (hv.le_iff_dvd.1 (by rw [map_pow, map_pow]; exact hn.le))⟩

theorem exists_localisation [IsAlgClosed C] [CharZero C] (hv : v.Integers O) (hp : p ≠ 0) (A : Type) [CommRing A]
    [Algebra O A] [Module.Finite O A] (aug : A →ₐ[O] O) :
    ∃ s : A, Function.Surjective (algebraMap A (Localization.Away s)) ∧
      (∃ m : ℕ, ((RingHom.ker aug).map (algebraMap A (Localization.Away s))) ^ m ≤
        Ideal.span {(p : Localization.Away s)}) ∧
      ∀ (R : Type) [CommRing R] [Algebra O R] (w : A →ₐ[O] R), (∀ t ∈ RingHom.ker aug, IsNilpotent (w t)) →
        IsUnit (w s) := by
  let W := v.valuationSubring
  have hW : v.Integers W := Valuation.valuationSubring.integers v
  let f : O →+* W := (algebraMap O C).codRestrict W hv.map_le_one
  have hf : Function.Bijective f := ⟨fun a b h => hv.hom_inj (congrArg Subtype.val h), fun w => by
    obtain ⟨a, ha⟩ := hv.exists_of_le_one (r := (w : C)) w.2
    exact ⟨a, Subtype.ext ha⟩⟩
  let e := RingEquiv.ofBijective f hf
  letI : Algebra W O := e.symm.toRingHom.toAlgebra
  letI : Algebra W A := ((algebraMap O A).comp e.symm.toRingHom).toAlgebra
  haveI : IsScalarTower W O A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite W O := Module.Finite.of_surjective (Algebra.linearMap W O) e.symm.surjective
  haveI : Module.Finite W A := Module.Finite.trans O A
  let aug' : A →ₐ[W] W := ⟨e.toRingHom.comp aug.toRingHom, fun w => by
    show e (aug (algebraMap O A (e.symm w))) = w
    rw [aug.commutes]
    exact e.apply_symm_apply w⟩
  have hk : RingHom.ker aug' = RingHom.ker aug := Ideal.ext fun a => map_eq_zero_iff e e.injective
  obtain ⟨s, h1, h2, h3⟩ := GlobalTheory.finite_augmented_connected_part_localisation C W (p : W)
    (fun a ha => exists_pow_mem hW ha (Nat.cast_ne_zero.2 hp)) A aug'
  rw [hk, map_natCast] at h2
  refine ⟨s, h1, h2, fun R _ _ w hw => ?_⟩
  letI : Algebra W R := ((algebraMap O R).comp e.symm.toRingHom).toAlgebra
  exact h3 R ⟨w.toRingHom, fun a => w.commutes _⟩ (hk ▸ hw)

theorem exists_connected_part [IsAlgClosed C] [CharZero C] (hv : v.Integers O) (hp : p ≠ 0)
    (G : Over (Sp O)) [GrpObj G] [IsCommMonObj G] (N : ℕ) (hN : N ≠ 0) [hfi : IsFinite (torsion G N).hom]
    [Flat (torsion G N).hom] :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A) (X : specO O A ⟶ torsion G N) (I : Ideal A) (m : ℕ),
      Module.Finite O A ∧ Module.Flat O A ∧ (∀ a b : A, (∀ φ : A →ₐ[O] O, φ a = φ b) → a = b) ∧
      ptMap (Ideal.Quotient.mkₐ O I) ≫ X ≫ torsion.ι G N = 1 ∧ I ^ m ≤ Ideal.span {(p : A)} ∧
      ∀ (R : Type) [CommRing R] [Algebra O R] (w : specO O (DualNumber R) ⟶ torsion G N),
        ptMap (TrivSqZeroExt.fstHom O R R) ≫ w ≫ torsion.ι G N = 1 →
          ∃ ψ : A →ₐ[O] DualNumber R, w = ptMap ψ ≫ X := by
  have hinj := hv.hom_inj
  have : IsDomain O := hinj.isDomain _
  have := ValuationRing.of_integers v hv
  have hred := isReduced_torsion_geometric_fibre O C G N (Nat.cast_ne_zero.2 hN) hfi
  obtain ⟨A, _, _, hfin, hfree, ⟨i⟩⟩ := exists_finite_free (torsion G N)
  obtain ⟨aug, haug⟩ := exists_ptMap (torsionLift (1 : specO O O ⟶ G) (one_pow N) ≫ i.inv)
  have haug' : ptMap aug ≫ i.hom ≫ torsion.ι G N = 1 := by
    rw [← haug, Category.assoc, Iso.inv_hom_id_assoc, torsionLift_ι]
  obtain ⟨s, hs, ⟨m, hm⟩, hu⟩ := exists_localisation hv hp A aug
  let loc := IsScalarTower.toAlgHom O A (Localization.Away s)
  have lift : ∀ (R : Type) [CommRing R] [Algebra O R] (w : A →ₐ[O] R), (∀ t ∈ RingHom.ker aug, IsNilpotent (w t)) →
      ∃ w' : Localization.Away s →ₐ[O] R, w'.comp loc = w := fun R _ _ w hw =>
    ⟨IsLocalization.Away.liftAlgHom s (hu R w hw), AlgHom.ext fun a => IsLocalization.Away.lift_eq s (hu R w hw) a⟩
  have : Module.Finite O (Localization.Away s) := Module.Finite.of_surjective loc.toLinearMap hs
  have : Module.Flat A (Localization.Away s) := IsLocalization.flat _ (Submonoid.powers s)
  have : Module.Flat O (Localization.Away s) := Module.Flat.trans O A _
  refine ⟨Localization.Away s, inferInstance, inferInstance, ptMap loc ≫ i.hom, _, m, inferInstance,
    inferInstance, fun a b h => ?_, ?_, hm, fun R _ _ w hw => ?_⟩
  · have : IsIso i.hom.left := inferInstanceAs (IsIso ((Over.forget _).map i.hom))
    have : IsOpenImmersion (ptMap loc).left :=
      inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away s)))))
    have : IsOpenImmersion (ptMap loc ≫ i.hom).left := by rw [Over.comp_left]; infer_instance
    have : IsOpenImmersion (specO O C ◁ (ptMap loc ≫ i.hom)).left := by
      rw [Over.whiskerLeft_left]
      exact MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance this (by simp) (Over.w _).symm
    have h3 := isReduced_of_isOpenImmersion (specO O C ◁ (ptMap loc ≫ i.hom)).left
    have h4 : IsReduced (Spec (CommRingCat.of (C ⊗[O] Localization.Away s))) :=
      @isReduced_of_isOpenImmersion _ _ (pullbackSpecIso O C _).inv _ h3
    have hA : _root_.IsReduced (C ⊗[O] Localization.Away s) := (affine_isReduced_iff _).mp h4
    refine sub_eq_zero.1 (FlatPoints.eq_zero_of_forall_point O C hinj _ _ fun x => ?_)
    choose g hg using fun a => hv.exists_of_le_one
      (hv.isIntegral_iff_v_le_one.1 ((Algebra.IsIntegral.isIntegral (R := O) a).map x))
    have := h
      { toFun := g
        map_one' := hinj (by simp [hg])
        map_mul' := fun a b => hinj (by simp [hg])
        map_zero' := hinj (by simp [hg])
        map_add' := fun a b => hinj (by simp [hg])
        commutes' := fun r => hinj (by simp [hg]) }
    rw [map_sub, ← hg, ← hg, show g a = g b from this, sub_self]
  · have e : (Ideal.Quotient.mkₐ O ((RingHom.ker aug).map (algebraMap A (Localization.Away s)))).comp loc =
        (Algebra.ofId O _).comp aug := AlgHom.ext fun a => by
      show Ideal.Quotient.mk _ (algebraMap A _ a) = Ideal.Quotient.mk _ (algebraMap O _ (aug a))
      rw [Ideal.Quotient.eq, IsScalarTower.algebraMap_apply O A, ← map_sub]
      refine Ideal.mem_map_of_mem _ ?_
      show aug _ = 0
      rw [map_sub, AlgHom.commutes]
      exact sub_self _
    rw [Category.assoc, ← Category.assoc, ptMap_comp_ptMap, e, ← ptMap_comp_ptMap, Category.assoc, haug',
      MonObj.comp_one]
  · obtain ⟨ψ, hψ⟩ := exists_ptMap (w ≫ i.inv)
    have e : (TrivSqZeroExt.fstHom O R R).comp ψ = (Algebra.ofId O R).comp aug := by
      apply SeriesCharacter.ptMap_injective
      rw [← cancel_mono i.hom]
      apply torsion_hom_ext
      rw [← ptMap_comp_ptMap, ← ptMap_comp_ptMap, ← hψ]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [hw, haug', MonObj.comp_one]
    obtain ⟨ψ', hψ'⟩ := lift _ ψ fun t ht => by
      rw [TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst, show (ψ t).fst = 0 from
        (AlgHom.congr_fun e t).trans (by rw [AlgHom.comp_apply, show aug t = 0 from ht, map_zero])]
      exact IsNilpotent.zero
    refine ⟨ψ', ?_⟩
    rw [← Category.assoc, ptMap_comp_ptMap, hψ', ← hψ, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem exists_tv [IsAlgClosed C] [CharZero C] (hv : v.Integers O) (hp : p ≠ 0)
    (G : Over (Sp O)) [GrpObj G] [IsCommMonObj G]
    (hG : ∀ N, 1 ≤ N → IsFinite (torsion G N).hom ∧ Flat (torsion G N).hom) (κ : (specO O O ⟶ G) →* Cˣ) :
    ∃ χ : Tv G p, ∀ (n : ℕ) (w : specO O O ⟶ torsion G (p ^ n)),
      algebraMap O C (unitOf (w ≫ χ.χ n) : O) = (κ (w ≫ torsion.ι G (p ^ n)) : C) := by
  have h1 : ∀ n, 1 ≤ p ^ n := fun n => Nat.pos_of_ne_zero (pow_ne_zero n hp)
  have H := fun n : ℕ => torsionCharacter_ext_and_exists_of_integral_points C v O hv G
    (p ^ n) (h1 n) (hG _ (h1 n)).1 (hG _ (h1 n)).2
  choose g hg hgκ using fun n => (H n).2 κ fun x y _ _ => map_mul κ x y
  refine ⟨⟨g, hg, fun m T x y hxy => ?_⟩, hgκ⟩
  have hι : torsion.ι G (p ^ m) ^ (p ^ (m + 1)) = 1 := by
    rw [pow_succ, pow_mul, torsionι_pow, one_pow]
  have hy : y = x ≫ torsionLift _ hι :=
    torsion_hom_ext (by rw [Category.assoc, torsionLift_ι, hxy])
  have : g m = torsionLift _ hι ≫ g (m + 1) := (H m).1 _ _ fun w =>
    unitOf_bijective.1 (Units.ext (hv.hom_inj (by
      rw [← Category.assoc, hgκ, hgκ, Category.assoc, torsionLift_ι])))
  rw [hy, this, Category.assoc]

end Integers

section Values

variable {p : ℕ} {O : Type} [CommRing O] {G : Over (Sp O)}
  (Val : ∀ (R : Type) [CommRing R] [Algebra O R], (specO O R ⟶ G) → R → Prop)

variable (p) in

def LimOf {A : Type} [CommRing A] [Algebra O A] (g : specO O A ⟶ G) (k : A) : Prop :=
  ∀ (R : Type) [CommRing R] [Algebra O R] (θ : A →ₐ[O] R), IsNilpotent (p : R) → Val R (ptMap θ ≫ g) (θ k)

variable {Val}

theorem LimOf.map {A B : Type} [CommRing A] [Algebra O A] [CommRing B] [Algebra O B] {g : specO O A ⟶ G} {k : A}
    (h : LimOf p Val g k) (θ : A →ₐ[O] B) : LimOf p Val (ptMap θ ≫ g) (θ k) := fun R _ _ θ' hp => by
  rw [← Category.assoc, ptMap_comp_ptMap]
  exact h R (θ'.comp θ) hp

theorem nilpotent_quot {A : Type} [CommRing A] (n : ℕ) : IsNilpotent (p : A ⧸ Ideal.span {(p : A)} ^ n) :=
  ⟨n, by
    rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) n)⟩

variable [GrpObj G]
  (hmap : ∀ (R R' : Type) [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R'] (θ : R →ₐ[O] R') g k,
    Val R g k → Val R' (ptMap θ ≫ g) (θ k))
  (huniq : ∀ (R : Type) [CommRing R] [Algebra O R] g k k', Val R g k → Val R g k' → k = k')
  (hone : ∀ (R : Type) [CommRing R] [Algebra O R], IsNilpotent (p : R) → Val R 1 1)
  (hmul : ∀ (R : Type) [CommRing R] [Algebra O R] g g' k k', Val R g k → Val R g' k' → Val R (g * g') (k * k'))
  (hex : ∀ (R : Type) [CommRing R] [Algebra O R], IsNilpotent (p : R) → ∀ I : Ideal R, IsNilpotent I →
    ∀ g, ptMap (Ideal.Quotient.mkₐ O I) ≫ g = 1 → ∃ k, Val R g k)

include hmap huniq hex in
theorem exists_limOf {A : Type} [CommRing A] [Algebra O A] [IsPrecomplete (Ideal.span {(p : A)}) A] (I : Ideal A)
    {m : ℕ} (hI : I ^ m ≤ Ideal.span {(p : A)}) (g : specO O A ⟶ G)
    (hg : ptMap (Ideal.Quotient.mkₐ O I) ≫ g = 1) : ∃ k, LimOf p Val g k := by
  let P : Ideal A := Ideal.span {(p : A)}
  have ex : ∀ e : ℕ, ∃ k, Val _ (ptMap (Ideal.Quotient.mkₐ O (P ^ (e + 1))) ≫ g) k := fun e => by
    let θ := Ideal.Quotient.mkₐ O (P ^ (e + 1))
    refine hex _ (nilpotent_quot _) (I.map θ) ⟨m * (e + 1), eq_bot_iff.2 ?_⟩ _ ?_
    · rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap, pow_mul]
      exact (Ideal.pow_right_mono hI _).trans fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
    · have e1 : (Ideal.Quotient.mkₐ O (I.map θ)).comp θ =
          (Ideal.quotientMapₐ (I.map θ) θ Ideal.le_comap_map).comp (Ideal.Quotient.mkₐ O I) := rfl
      rw [← Category.assoc, ptMap_comp_ptMap, e1, ← ptMap_comp_ptMap, Category.assoc, hg, MonObj.comp_one]
  choose k hk using ex
  obtain ⟨k₀, hk₀⟩ := SeriesValue.exists_lim P k fun e => by
    have := hmap _ _ (Ideal.Quotient.factorₐ O (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))) _ _ (hk (e + 1))
    rw [← Category.assoc, ptMap_comp_ptMap] at this
    exact huniq _ _ _ _ this (hk e)
  refine ⟨k₀, fun R _ _ θ ⟨n, hn⟩ => ?_⟩
  let θ' : (A ⧸ P ^ (n + 1)) →ₐ[O] R := Ideal.Quotient.liftₐ _ θ fun a ha => by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, map_pow, map_natCast, pow_succ, hn, zero_mul, mul_zero]
  have := hmap _ _ θ' _ _ (hk n)
  rw [← Category.assoc, ptMap_comp_ptMap, ← hk₀] at this
  exact this

include hmap huniq hone hmul hex in

theorem exists_tv_of_values {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} [Algebra O C]
    (hv : v.Integers O) (hp : p ≠ 0) [hc : IsAdicComplete (Ideal.span {(p : O)}) O] [IsCommMonObj G]
    (hG : ∀ N, 1 ≤ N → IsFinite (torsion G N).hom ∧ Flat (torsion G N).hom) :
    ∃ χ : Tv G p, ∀ (n : ℕ) (R : Type) [CommRing R] [Algebra O R], (p : R) ^ n = 0 →
      ∀ w : specO O (DualNumber R) ⟶ torsion G (p ^ n),
        ptMap (TrivSqZeroExt.fstHom O R R) ≫ w ≫ torsion.ι G (p ^ n) = 1 →
        ∀ k, Val _ (w ≫ torsion.ι G (p ^ n)) k → (unitOf (w ≫ χ.χ n) : DualNumber R) = k := by
  have : IsDomain O := hv.hom_inj.isDomain _
  have := ValuationRing.of_integers v hv
  obtain ⟨κ, hκ⟩ := exists_character_of_rel (N := specO O O ⟶ G) (F := C)
    (fun g c => ∃ k : O, LimOf p Val g k ∧ c = algebraMap O C k)
    ⟨1, fun R _ _ θ hR => by rw [MonObj.comp_one, map_one]; exact hone R hR, (map_one _).symm⟩
    (by
      rintro g g' _ _ ⟨k, hk, rfl⟩ ⟨k', hk', rfl⟩
      refine ⟨k * k', fun R _ _ θ hR => ?_, (map_mul _ _ _).symm⟩
      rw [MonObj.comp_mul, map_mul]
      exact hmul _ _ _ _ _ (hk R θ hR) (hk' R θ hR))
    (by
      rintro g _ _ ⟨k, hk, rfl⟩ ⟨k', hk', rfl⟩
      refine congrArg _ (sub_eq_zero.1 (IsHausdorff.haus' (I := Ideal.span {(p : O)}) _ fun n => ?_))
      rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
      exact Ideal.Quotient.eq.1 (huniq _ _ _ _ (hk _ (Ideal.Quotient.mkₐ O _) (nilpotent_quot n))
        (hk' _ (Ideal.Quotient.mkₐ O _) (nilpotent_quot n))))
  obtain ⟨χ, hχ⟩ := exists_tv hv hp G hG κ
  refine ⟨χ, fun n R _ _ hR w hw k hk => ?_⟩
  obtain ⟨h1, h2⟩ := hG (p ^ n) (Nat.pos_of_ne_zero (pow_ne_zero n hp))
  obtain ⟨A, _, _, X, I, m, _, _, hsep, hX, hI, hl⟩ := exists_connected_part hv hp G (p ^ n) (pow_ne_zero n hp)
  have hAc : IsAdicComplete (Ideal.span {(p : A)}) A := by
    have := FlatComplete.isAdicComplete_of_finite_flat _ _ hc A
    rwa [Ideal.map_span, Set.image_singleton, map_natCast] at this
  obtain ⟨a, ha⟩ := exists_limOf hmap huniq hex I hI _ hX
  have e : (unitOf (X ≫ χ.χ n) : A) = a := hsep _ _ fun φ => hv.hom_inj (by
    rw [← unitOf_ptMap, ← Category.assoc, hχ, Category.assoc]
    refine hκ _ _ (p ^ n) (pow_ne_zero n hp) ?_ ⟨_, ha.map φ, rfl⟩
    rw [← MonObj.comp_pow, ← MonObj.comp_pow, torsionι_pow, MonObj.comp_one, MonObj.comp_one])
  obtain ⟨ψ, rfl⟩ := hl R w hw
  rw [Category.assoc, unitOf_ptMap, e]
  rw [Category.assoc] at hk
  refine huniq _ _ _ _ (ha _ ψ ⟨n, ?_⟩) hk
  rw [← map_natCast (algebraMap R (DualNumber R)), ← map_pow, hR, map_zero]

end Values

section Push

open GlobalTheory.ChartBaseChange

variable {V O : Type} [CommRing V] [CommRing O] [Algebra V O] {G : Over (Sp V)} [GrpObj G] {G' : Over (Sp O)} [GrpObj G']
  {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (spMap (algebraMap V O)) π) {R : Type} [CommRing R] [Algebra O R]

def pushV (y : specO O R ⟶ G') : specV (algebraMap V O) R ⟶ G :=
  letI : Algebra V R := ((algebraMap O R).comp (algebraMap V O)).toAlgebra
  haveI : IsScalarTower V O R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  push hπ y

theorem pushV_left (y : specO O R ⟶ G') : (pushV hπ y).left = y.left ≫ π := rfl

theorem pushV_mul (y z : specO O R ⟶ G') : pushV hπ (y * z) = pushV hπ y * pushV hπ z :=
  letI : Algebra V R := ((algebraMap O R).comp (algebraMap V O)).toAlgebra
  haveI : IsScalarTower V O R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  push_mul hπ y z

theorem pushV_one : pushV hπ (1 : specO O R ⟶ G') = 1 :=
  letI : Algebra V R := ((algebraMap O R).comp (algebraMap V O)).toAlgebra
  haveI : IsScalarTower V O R := IsScalarTower.of_algebraMap_eq fun _ => rfl
  push_one hπ

end Push

section Point

open GlobalTheory.HTLat.OmegaRank GlobalTheory.ChartBaseChange GlobalTheory.SeriesValue GlobalTheory.HodgeTateImage
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FGLaw)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (IsCh dl)

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem cmp_of_corr {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    {x : specO O R ⟶ P.Gt} {y : specO O R ⟶ P.G} (h : Corr P x y) (θ : R →ₐ[O] R') (hR : IsNilpotent (p : R')) :
    P.cmp R' hR (ptMap θ ≫ x) = ptMap θ ≫ y := by
  obtain ⟨m, hm⟩ := id hR
  let θ' : (R ⧸ Ideal.span {(p : R) ^ m}) →ₐ[O] R' := Ideal.Quotient.liftₐ _ θ fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [map_mul, map_pow, map_natCast, hm, mul_zero]
  have e : ptMap θ = ptMap θ' ≫ ptMap (redR p O R m) := by
    rw [ptMap_comp_ptMap]
    rfl
  rw [e, Category.assoc, Category.assoc, h m, P.cmp_nat _ _ (nilpR m)]

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem exists_tangent_param {d : ℕ} {x : JetSer.Fam P.G (Fin d)} (hx : Chart.IsUnivChart P.G d x) :
    ∃ (tv : (Fin d → O) → LieG P.Gt) (co : LieG P.Gt → Fin d → O), (∀ w, tv (co w) = w) ∧
      (∀ b, Corr P (tv b).1 (Chart.tvec (x := x) b)) ∧
      ∀ f ∈ omega P.Gt, ∀ b, f (tv b) = ∑ j, f (tv (Pi.single j 1)) * b j := by
  haveI := P.isLocalRing
  haveI := HodgeTateCompare.isLocalRing_dualNumber (O := O)
  have hp₀ : ¬ IsUnit (p : O) := Fact.out
  have hp : ¬ IsUnit (p : DualNumber O) := fun h => hp₀ (by
    simpa using h.map (TrivSqZeroExt.fstHom O O O))
  have hc := isAdicComplete_dualNumber (O := O) p
  have hl := existsUnique_left (P := P) hp hc
  have hr := existsUnique_right (P := P) hp hc
  let tv : (Fin d → O) → LieG P.Gt := fun b => ⟨(hl (Chart.tvec (x := x) b)).choose,
    (existsUnique_left (P := P) hp₀ inferInstance 1).unique
      (by
        have h := (hl (Chart.tvec (x := x) b)).choose_spec.1.comp (TrivSqZeroExt.fstHom O O O)
        rw [show ptMap (TrivSqZeroExt.fstHom O O O) ≫ Chart.tvec (x := x) b = 1 from Chart.isTan_tvec hx b] at h
        exact h) Corr.one⟩
  have htv : ∀ b, Corr P (tv b).1 (Chart.tvec (x := x) b) := fun b => (hl _).choose_spec.1
  have hsurj : ∀ w, ∃ b, tv b = w := fun w => by
    obtain ⟨y, hy, -⟩ := hr w.1
    have h := hy.comp (TrivSqZeroExt.fstHom O O O)
    rw [w.2] at h
    have ht : Chart.IsTan y := (existsUnique_right (P := P) hp₀ inferInstance 1).unique h Corr.one
    refine ⟨Chart.tcoord hx y ht, Subtype.ext ((hl y).unique ?_ hy)⟩
    have h2 := htv (Chart.tcoord hx y ht)
    rwa [show Chart.tvec (x := x) (Chart.tcoord hx y ht) = y from (Chart.tcoord_spec hx y ht).symm] at h2
  choose co hco using hsurj
  refine ⟨tv, co, hco, htv, fun f hf b => ?_⟩
  let l : (Fin d → O) →ₗ[O] O :=
    { toFun := fun c => f (tv c)
      map_add' := fun c c' => (congrArg f (Subtype.ext ((hl _).unique (htv (c + c'))
        (Chart.tvec_add hx c c' ▸ (htv c).mul (htv c'))))).trans (omega_lieAdd ⟨f, hf⟩ (tv c) (tv c'))
      map_smul' := fun a c => (congrArg f (Subtype.ext ((hl _).unique (htv (a • c))
        (Chart.tvec_smul hx a c ▸ (htv c).comp (dualScale a))))).trans (omega_lieScale ⟨f, hf⟩ a (tv c)) }
  refine (LinearMap.pi_apply_eq_sum_univ l b).trans (Finset.sum_congr rfl fun j _ => ?_)
  rw [smul_eq_mul, mul_comm]
  refine congrArg (fun c => f (tv c) * b j) (funext fun i => ?_)
  rw [Pi.single_apply]
  exact if_congr eq_comm rfl rfl

variable [IsAlgClosed C] [CharZero C] {V : Type} [CommRing V] [IsLocalRing V] [Algebra V O]
  {G : Over (Sp V)} [GrpObj G] {π : P.G.left ⟶ G.left} (hπ : IsGrpPullback P.G G (spMap (algebraMap V O)) π)
  {d : ℕ} {x : JetSer.Fam G (Fin d)} (hx : Chart.IsUnivChart G d x) (L : FGLaw V d) (hL : JetSer.IsLawOf x L.F)

include hπ hx hL in

theorem exists_tv_of_series {u : PS O 1 d} (hu : IsCh (L.mapF (algebraMap V O)) u) :
    ∃ χ : Tv P.Gt p, ∀ (n : ℕ) (R : Type) [CommRing R] [Algebra O R], (p : R) ^ n = 0 →
      ∀ w : specO O (DualNumber R) ⟶ torsion P.Gt (p ^ n),
        ptMap (TrivSqZeroExt.fstHom O R R) ≫ w ≫ torsion.ι P.Gt (p ^ n) = 1 →
        ∀ k, (∃ h, HasVal x u ((P.cmp _ h (w ≫ torsion.ι P.Gt (p ^ n))).left ≫ π) k) →
          (unitOf (w ≫ χ.χ n) : DualNumber R) = k := by
  refine exists_tv_of_values (p := p)
    (Val := fun R _ _ g k => ∃ h, HasVal x u ((P.cmp R h g).left ≫ π) k) ?_ ?_ ?_ ?_ ?_ P.integers
    (Fact.out : p.Prime).ne_zero P.finite_flat
  · rintro R R' _ _ _ _ θ g k ⟨h, hk⟩
    have h' : IsNilpotent (p : R') := by simpa using h.map θ
    refine ⟨h', ?_⟩
    rw [P.cmp_nat _ _ h, Over.comp_left, Category.assoc]
    exact hk.map θ
  · rintro R _ _ g k k' ⟨h, hk⟩ ⟨_, hk'⟩
    exact hk.unique hx hk'
  · intro R _ _ h
    refine ⟨h, ?_⟩
    rw [map_one, ← pushV_left hπ, pushV_one]
    exact hasVal_one hx hu.1
  · rintro R _ _ g g' k k' ⟨h, hk⟩ ⟨_, hk'⟩
    refine ⟨h, ?_⟩
    rw [map_mul, ← pushV_left hπ, pushV_mul]
    have h2 := hu.2
    rw [JetSer.addOf_pt_pt] at h2
    exact HasVal.mul hx hL h2 (g := pushV hπ (P.cmp R h g)) (g' := pushV hπ (P.cmp R h g')) hk hk'
  · intro R _ _ h I hI g hg
    have h' : IsNilpotent (p : R ⧸ I) := by simpa using h.map (Ideal.Quotient.mk I)
    have e : ptMap (Ideal.Quotient.mkₐ O I) ≫ P.cmp R h g = ptMap (Ideal.Quotient.mkₐ O I) ≫ 1 := by
      rw [← P.cmp_nat _ _ h h', hg, map_one, MonObj.comp_one]
    obtain ⟨k, hk⟩ := exists_hasVal hx u I hI (pushV hπ (P.cmp R h g)) (by
      have e1 := congrArg (·.left ≫ π) e
      have e2 : (1 : specO O R ⟶ P.G).left ≫ π = _ := congrArg (·.left) (pushV_one (R := R) hπ)
      simp only [Over.comp_left, Category.assoc] at e1
      rw [e2] at e1
      exact e1)
    exact ⟨k, h, hk⟩

include hπ hx hL in

theorem smul_mem_htSpan {N : ℕ} {u : Fin N → PS O 1 d} (hu : ∀ k, IsCh (L.mapF (algebraMap V O)) (u k)) {c : O}
    (hc : ∀ f : Fin d → O, c • f ∈ Submodule.span O (Set.range fun k => dl (u k))) :
    ∀ f ∈ omega P.Gt, c • f ∈ htSpan P.Gt p := by
  choose x' hx' using fun m => push_surjective hπ (Chart.spMap (jetCoeff V O (Fin d) m) ≫ x m)
  obtain ⟨tv, co, hco, htv, hsum⟩ := exists_tangent_param P (isUnivChart_baseChange hπ hx hx')
  let l : (Fin d → O) →ₗ[O] (LieG P.Gt → O) :=
    { toFun := fun a w => ∑ j, a j * co w j
      map_add' := fun a b => funext fun w => by simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun a b => funext fun w => by simp [Finset.mul_sum, _root_.mul_assoc] }
  intro f hf
  have e : f = l fun j => f (tv (Pi.single j 1)) := funext fun w => by
    rw [← hco w, hsum f hf]
    show _ = ∑ j, _ * co (tv (co w)) j
    rw [hco]
  have h := Submodule.mem_map_of_mem (f := l) (hc fun j => f (tv (Pi.single j 1)))
  rw [map_smul, ← e, Submodule.map_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  obtain ⟨χ, hχ⟩ := exists_tv_of_series P hπ hx L hL (hu k)
  have hal : IsAl χ (l (dl (u k))) := fun n R _ _ hR w z hz => by
    have hn : IsNilpotent (p : DualNumber R) :=
      ⟨n, by rw [← map_natCast (algebraMap R (DualNumber R)), ← map_pow, hR, map_zero]⟩
    refine hχ n R hR z (by rw [hz]; exact fst_bc R w) _ ⟨hn, ?_⟩
    let β := dualBC (Algebra.ofId O R)
    let φ : Chart.JetR V (Fin d) 1 →+* DualNumber R :=
      β.toRingHom.comp ((Chart.dualLift (co w)).toRingHom.comp (jetCoeff V O (Fin d) 1).toRingHom)
    have e6 : ∀ i, φ (Chart.zR 1 i) = TrivSqZeroExt.inr (algebraMap O R (co w i)) := fun i => by
      show β (Chart.dualLift (co w) (jetCoeff V O (Fin d) 1 (Chart.zR 1 i))) = _
      rw [jetCoeff_zR, Chart.dualLift_zR, dualBC_inr]
    have e5 : (pushV hπ (P.cmp _ hn (z ≫ torsion.ι P.Gt (p ^ n)))).left =
        Spec.map (CommRingCat.ofHom φ) ≫ (x 1).left := by
      have h1 : (x' 1).left ≫ π = _ := congrArg (·.left) (hx' 1)
      rw [hz, ← hco w, cmp_of_corr P (htv _), pushV_left, Chart.tvec, Over.comp_left, Over.comp_left, Category.assoc,
        Category.assoc, h1, Over.comp_left, ← Category.assoc, ← Category.assoc, Chart.spMap_left, Chart.spMap_left,
        CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp]
      rfl
    let θ : Chart.JetR O (Fin 1 × Fin d) 1 →ₐ[O] DualNumber O :=
      Chart.jetLift _ (RingHom.ker (Chart.fstD O)) Chart.kerD_sq
        (fun q => TrivSqZeroExt.inr (co w q.2)) (fun q => TrivSqZeroExt.fst_inr _ (co w q.2))
    have hθ : ∀ q, (β.comp θ) (Chart.zR 1 q) = TrivSqZeroExt.inr (algebraMap _ R (co w q.2)) := fun q => by
      have h0 : θ (Chart.zR 1 q) = TrivSqZeroExt.inr (co w q.2) :=
        Chart.jetLift_zR (RingHom.ker (Chart.fstD O)) Chart.kerD_sq _
          (fun q : Fin 1 × Fin d => TrivSqZeroExt.fst_inr _ (co w q.2)) q
      exact (congrArg β h0).trans (dualBC_inr _)
    have v1 := SeriesCharacter.hasVal_of_ringHom x (u k) _ _ e5 (β.comp θ) fun q => (hθ q).trans (e6 q.2).symm
    rw [JetSer.dualNumber_value_toJet V _ (algebraMap V O) d L (co w) (u k) R _ hθ, (hu k).1, map_one,
      JetSer.constantCoeff_dof] at v1
    have e7 : l (dl (u k)) w = ∑ j, co w j * MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (u k) :=
      show ∑ j, dl (u k) j * co w j = ∑ j, co w j * dl (u k) j from Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [e7]
    exact v1
  obtain ⟨g, ⟨hg, hg'⟩, -⟩ := existsUnique_isAl χ
  have e : l (dl (u k)) = g := funext fun w => eq_of_forall (p := p) fun n => by
    rw [(isAl_iff χ _).1 hal w n _ (pow_quot n), (isAl_iff χ g).1 hg' w n _ (pow_quot n)]
  exact ⟨e ▸ hg, χ, hal⟩

end Point

theorem exists_local_extension {p : ℕ} (hp : p ≠ 0) {C : Type} [Field C] [IsAlgClosed C] {v : Valuation C ℝ≥0} {O : Type}
    [CommRing O] [Algebra O C] (hv : v.Integers O) (hO : ¬ IsUnit (p : O)) {V W : Type} [CommRing V] [IsDomain V]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W] (f : V →+* O) (hf : Function.Injective f)
    (φ : V →+* W) (hφ : Function.Injective φ) (hfin : φ.Finite) :
    ∃ g : W →+* O, g.comp φ = f ∧ IsLocalHom g := by
  letI := φ.toAlgebra
  letI := f.toAlgebra
  letI : Algebra V C := ((algebraMap O C).comp f).toAlgebra
  haveI : IsScalarTower V O C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Module.Finite V W := hfin
  haveI : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  haveI : FaithfulSMul V C := (faithfulSMul_iff_algebraMap_injective _ _).2 (hv.hom_inj.comp hf)
  let j : W →ₐ[V] C := IsAlgClosed.lift
  have hinj := hv.hom_inj
  choose g hg using fun a => hv.exists_of_le_one
    (hv.isIntegral_iff_v_le_one.1 (((Algebra.IsIntegral.isIntegral (R := V) a).map j).tower_top (A := O)))
  let g' : W →+* O :=
    { toFun := g
      map_one' := hinj (by simp [hg])
      map_mul' := fun a b => hinj (by simp [hg])
      map_zero' := hinj (by simp [hg])
      map_add' := fun a b => hinj (by simp [hg]) }
  refine ⟨g', RingHom.ext fun a => hinj ((hg _).trans (j.commutes a)), ⟨fun a ha => ?_⟩⟩
  by_contra hn
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (Nat.cast_ne_zero.2 hp : (p : W) ≠ 0) hϖ
  have h1 : ϖ ∣ a := Ideal.mem_span_singleton.1 (hϖ.maximalIdeal_eq ▸ hn)
  have h2 : IsUnit (g' ϖ) := isUnit_of_dvd_unit (map_dvd g' h1) ha
  refine hO ?_
  rw [← map_natCast g', hw, map_mul, map_pow]
  exact (w.isUnit.map g').mul (h2.pow n)

end GlobalTheory.CompHt.FormalChar

namespace GlobalTheory.CompHt

open FormalChar

theorem htChar_of_pointOver : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C ℝ≥0) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] [StarRing (𝓞 E)] (T : CDVR) (io : c.F →+* T.Fr) (y₀ : IntFr Xo c T io), y₀.IsAlg → ∀ (k : T.Fr →+* C) (kO : T.V →+* O) (P : Point p v O (𝓞 E)) (ψ : P.A.A.left ⟶ Xo.univ.t.G.left), (letI := io.toAlgebra; PointOver P y₀.1.x k kO ψ) → HTChar p v P.Gt := by
  intro E _ _ _ H Dw l Xo c p hp C _ _ _ v O _ _ hO _ _ _ _ _ T io y₀ hy k kO P ψ hP
  obtain ⟨hk, G, t', m₁, m₂, π, -, hπ, -⟩ := hP
  obtain ⟨T', φ, t, m, hφ, hfin, -, -, U, -⟩ :=
    UnifAfterExt.exists_finite_ext_uniformised E H Dw l Xo T G t' m₂ _ m₁ hy
  have hkO : Function.Injective kO := fun a b h => IsFractionRing.injective T.V T.Fr (k.injective (by
    rw [← hk, ← hk, h]))
  obtain ⟨g, hg, hloc⟩ := exists_local_extension hp.out.ne_zero P.integers hO.out kO hkO φ hφ hfin
  letI := g.toAlgebra
  have e : spMap g ≫ spMap φ = spMap kO := by rw [spMap_spMap, hg]
  have w : π ≫ G.G.hom = (P.G.hom ≫ spMap g) ≫ spMap φ := by rw [Category.assoc, e, hπ.1.w]
  have hπ' : IsGrpPullback P.G t.G (spMap g) (m.cart.1.lift π _ w) :=
    m.cart.cancel (hπ.congr e.symm (m.cart.1.lift_fst _ _ _).symm) (m.cart.1.lift_snd _ _ _)
  haveI := t.semi.smooth
  obtain ⟨d, x, hx⟩ := Chart.univChartLoc t.G
  obtain ⟨F, hF⟩ := (JetSer.lawSt_of JetSer.jetAlg (JetSer.repSt_of_jetAlgSt JetSer.jetAlg) _ t.G d x hx).1
  obtain ⟨x', hx'⟩ := ChartCharacter.exists_isChartJ t.G x hx F hF
  obtain ⟨N, u, hu, hspan⟩ := ChF.hodgeTate_inclusion_chart p T'.V (fun h => hO.out (by simpa using h.map g)) t.G
    U.D U.A U.U.toUnifPre d F x' hx' C v O P.integers g hloc
  intro a ha
  exact smul_mem_htSpan P hπ' hx F hF hu (hspan a (by rwa [map_natCast]))

end GlobalTheory.CompHt
