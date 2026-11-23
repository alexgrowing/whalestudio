import Mathlib
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsCechNerveQuasiIsoOfSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechNerveBaseChangeIsPullbackStatement

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

private theorem unit_map (q : ℕ) {Y X : Scheme.{0}} (f : Y ⟶ X) (hq : IsUnit (q : Γ(X, ⊤))) : IsUnit (q : Γ(Y, ⊤)) := by
  simpa using hq.map f.appTop.hom

private noncomputable abbrev prj {Y X : Scheme.{0}} (f : Y ⟶ X) (k : SimplexCategoryᵒᵖ) (j : Fin (k.unop.len + 1)) :
    (cech f).obj k ⟶ yoneda.obj Y :=
  WidePullback.π (fun _ : Fin (k.unop.len + 1) => (Arrow.mk (yoneda.map f)).hom) j

private noncomputable abbrev augk {Y X : Scheme.{0}} (f : Y ⟶ X) (k : SimplexCategoryᵒᵖ) : (cech f).obj k ⟶ yoneda.obj X :=
  WidePullback.base (fun _ : Fin (k.unop.len + 1) => (Arrow.mk (yoneda.map f)).hom)

private theorem prj_f {Y X : Scheme.{0}} (f : Y ⟶ X) (k : SimplexCategoryᵒᵖ) (j : Fin (k.unop.len + 1)) :
    prj f k j ≫ yoneda.map f = augk f k :=
  WidePullback.π_arrow _ j

private noncomputable def dgk {Y X : Scheme.{0}} (f : Y ⟶ X) (k : SimplexCategoryᵒᵖ) : yoneda.obj Y ⟶ (cech f).obj k :=
  WidePullback.lift (yoneda.map f) (fun _ => 𝟙 (yoneda.obj Y)) (by simp)

private theorem dgk_prj {Y X : Scheme.{0}} (f : Y ⟶ X) (k : SimplexCategoryᵒᵖ) (j : Fin (k.unop.len + 1)) :
    dgk f k ≫ prj f k j = 𝟙 (yoneda.obj Y) :=
  WidePullback.lift_π _ _ _ _ j

private theorem dgk_aug {Y X : Scheme.{0}} (f : Y ⟶ X) (k : SimplexCategoryᵒᵖ) : dgk f k ≫ augk f k = yoneda.map f :=
  WidePullback.lift_base _ _ _ _

private theorem map_prj {Y X : Scheme.{0}} (f : Y ⟶ X) {k l : SimplexCategoryᵒᵖ} (g : k ⟶ l) (j : Fin (l.unop.len + 1)) :
    (cech f).map g ≫ prj f l j = prj f k (g.unop.toOrderHom j) :=
  WidePullback.lift_π _ _ _ _ j

private theorem map_aug {Y X : Scheme.{0}} (f : Y ⟶ X) {k l : SimplexCategoryᵒᵖ} (g : k ⟶ l) :
    (cech f).map g ≫ augk f l = augk f k :=
  WidePullback.lift_base _ _ _ _

private noncomputable def dg {Y X : Scheme.{0}} (f : Y ⟶ X) : sch.obj Y ⟶ cech f where
  app k := dgk f k
  naturality k l g := by
    change 𝟙 _ ≫ dgk f l = dgk f k ≫ (cech f).map g
    rw [Category.id_comp]
    apply WidePullback.hom_ext
    · intro j
      change dgk f l ≫ prj f l j = (dgk f k ≫ (cech f).map g) ≫ prj f l j
      rw [Category.assoc, map_prj, dgk_prj, dgk_prj]
    · change dgk f l ≫ augk f l = (dgk f k ≫ (cech f).map g) ≫ augk f l
      rw [Category.assoc, map_aug, dgk_aug, dgk_aug]

private theorem dg_aug {Y X : Scheme.{0}} (f : Y ⟶ X) : dg f ≫ cechAug f = sch.map f := by
  ext1 k
  exact dgk_aug f k

private noncomputable abbrev bpt (A : Type) [CommRing A] [IsLocalRing A] :
    Spec (CommRingCat.of (AlgebraicClosure (IsLocalRing.ResidueField A))) ⟶ Sp A :=
  Spec.map (CommRingCat.ofHom (algebraMap (IsLocalRing.ResidueField A) (AlgebraicClosure (IsLocalRing.ResidueField A)))) ≫
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))

private theorem henselianRing_of_le_nilradical {B : Type} [CommRing B] (J : Ideal B) (hJ : J ≤ nilradical B) :
    HenselianRing B J := by
  have hjac : J ≤ Ideal.jacobson ⊥ := hJ.trans Ideal.radical_le_jacobson
  refine ⟨hjac, ?_⟩
  intro f _ a₀ h₁ h₂
  have hloc := isLocalHom_of_le_jacobson_bot J hjac
  have hunit : ∀ c : B, c - a₀ ∈ J → IsUnit (f.derivative.eval c) := by
    intro c hc
    apply IsUnit.of_map (Ideal.Quotient.mk J)
    have hm : Ideal.Quotient.mk J (f.derivative.eval c) = Ideal.Quotient.mk J (f.derivative.eval a₀) := by
      rw [Ideal.Quotient.eq]
      obtain ⟨w, hw⟩ := Polynomial.sub_dvd_eval_sub c a₀ f.derivative
      rw [hw]
      exact J.mul_mem_right _ hc
    rw [hm]
    exact h₂
  have step : ∀ n : ℕ, ∃ c : B, c - a₀ ∈ J ∧ f.eval a₀ ^ (2 ^ n) ∣ f.eval c := by
    intro n
    induction n with
    | zero => exact ⟨a₀, by simp, by simp⟩
    | succ n ih =>
      obtain ⟨c, hc, hd⟩ := ih
      obtain ⟨u, hu⟩ := hunit c hc
      have hfc : f.eval c ∈ J := by
        obtain ⟨w, hw⟩ := hd
        rw [hw]
        exact J.mul_mem_right _ (J.pow_mem_of_mem h₁ _ (by positivity))
      obtain ⟨k, hk⟩ := Polynomial.binomExpansion f c (-(f.eval c * ↑u⁻¹))
      refine ⟨c + -(f.eval c * ↑u⁻¹), ?_, ?_⟩
      · have h3 := J.sub_mem hc (J.mul_mem_right (↑u⁻¹ : B) hfc)
        convert h3 using 1
        ring
      · rw [hk, ← hu]
        have h4 : (↑u : B) * -(f.eval c * ↑u⁻¹) = -f.eval c := by
          rw [mul_neg, mul_left_comm, Units.mul_inv, mul_one]
        rw [h4, add_neg_cancel, zero_add, neg_sq, pow_succ, pow_mul]
        exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd (Dvd.dvd.mul_right hd _) 2) _
  obtain ⟨N, hN⟩ := mem_nilradical.mp (hJ h₁)
  obtain ⟨c, hc, hd⟩ := step N
  have h0 : f.eval a₀ ^ (2 ^ N) = 0 := pow_eq_zero_of_le Nat.lt_two_pow_self.le hN
  rw [h0, zero_dvd_iff] at hd
  exact ⟨c, hd, hc⟩

private theorem eqv_tw_map_closedImmersion_surjective_spec (hE1 : E1) (q : ℕ) (i : ℤ) {A' : Type} [CommRing A'] (hq : IsUnit (q : A'))
    {P : Scheme.{0}} (δ : P ⟶ Spec (CommRingCat.of A')) [IsClosedImmersion δ] [Surjective δ] :
    Eqv (ZMod q) (sch.map δ) (tw q i) := by
  obtain ⟨hiso, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  obtain ⟨I, e, hδ⟩ := (IsClosedImmersion.Spec_iff (R := CommRingCat.of A') (f := δ)).mp inferInstance
  have hs : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
    have h5 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = e.inv ≫ δ := by
      rw [hδ, Iso.inv_hom_id_assoc]
    rw [h5]
    infer_instance
  have hI : I ≤ nilradical A' := by
    intro a ha
    rw [mem_nilradical, nilpotent_iff_mem_prime]
    intro p hp
    obtain ⟨y, hy⟩ := (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).surjective
      (⟨p, hp⟩ : PrimeSpectrum A')
    have hy' : p = Ideal.comap (Ideal.Quotient.mk I) y.asIdeal :=
      (congrArg PrimeSpectrum.asIdeal hy).symm
    rw [hy', Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact y.asIdeal.zero_mem
  haveI := henselianRing_of_le_nilradical I hI
  have h1 : Eqv (ZMod q) (spMap (Ideal.Quotient.mk I)) (tw q i) := hE1 q A' I hq i
  rw [hδ, Functor.map_comp]
  exact (hcomp _ _ _ _ _).1 (hiso _ _ _ inferInstance) h1

private theorem eqv_tw_map_closedImmersion_surjective (hB3 : B3) (hE1 : E1) (q : ℕ) (i : ℤ) {V Z : Scheme.{0}} (δ : V ⟶ Z)
    [IsClosedImmersion δ] [Surjective δ] (hq : IsUnit (q : Γ(Z, ⊤))) :
    Eqv (ZMod q) (sch.map δ) (tw q i) := by
  obtain ⟨hiso, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  refine hB3 q δ (𝟙 Z) hq i ?_
  intro A' _ s _
  have hqA : IsUnit (q : A') := by
    simpa using (unit_map q s hq).map (Scheme.ΓSpecIso (CommRingCat.of A')).hom.hom
  haveI : IsClosedImmersion (pullback.snd (δ ≫ 𝟙 Z) s) := inferInstance
  haveI : Surjective (pullback.snd (δ ≫ 𝟙 Z) s) := inferInstance
  have h1 := eqv_tw_map_closedImmersion_surjective_spec hE1 q i hqA (pullback.snd (δ ≫ 𝟙 Z) s)
  have hM : pullback.map (δ ≫ 𝟙 Z) s (𝟙 Z) s δ (𝟙 _) (𝟙 Z) (by simp) (by simp) ≫ pullback.snd (𝟙 Z) s =
      pullback.snd (δ ≫ 𝟙 Z) s := by
    unfold pullback.map
    exact pullback.lift_snd _ _ _
  rw [← hM, Functor.map_comp] at h1
  exact (hcomp _ _ _ _ _).2.2 (hiso _ _ _ inferInstance) h1

private theorem eqv_tw_map_integral_univInjective_surjective (hA3 : A3) (hB3 : B3) (hB4 : B4) (hE1 : E1) (q : ℕ) (i : ℤ) {V W : Scheme.{0}}
    (h : V ⟶ W) [IsIntegralHom h] [UniversallyInjective h] [Surjective h] (hq : IsUnit (q : Γ(W, ⊤))) :
    Eqv (ZMod q) (sch.map h) (tw q i) := by
  obtain ⟨hiso, hcomp, -, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  have hc := hB4 q h hq i
  have hd : Eqv (ZMod q) (dg h) (tw q i) := by
    apply hA3 (ZMod q) (dg h) (tw q i)
    intro n
    haveI : MorphismProperty.IsStableUnderBaseChange (@IsIntegralHom.{0} ⊓ @UniversallyInjective.{0}) :=
      MorphismProperty.IsStableUnderBaseChange.inf
    haveI : MorphismProperty.IsMultiplicative (@IsIntegralHom.{0} ⊓ @UniversallyInjective.{0}) :=
      MorphismProperty.IsMultiplicative.inf
    obtain ⟨Z, π, e, hπ, he⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable (@IsIntegralHom.{0} ⊓ @UniversallyInjective.{0}) V W h
      ⟨inferInstance, inferInstance⟩ n
    haveI : IsIntegralHom π := hπ.1
    haveI : UniversallyInjective π := hπ.2
    let pr0 : Z ⟶ V := Yoneda.fullyFaithful.preimage (e.hom ≫ prj h n 0)
    let δ : V ⟶ Z := Yoneda.fullyFaithful.preimage (dgk h n ≫ e.inv)
    have hδ : yoneda.map δ = dgk h n ≫ e.inv := Yoneda.fullyFaithful.map_preimage _
    have hpr : yoneda.map pr0 = e.hom ≫ prj h n 0 := Yoneda.fullyFaithful.map_preimage _
    have h1 : δ ≫ pr0 = 𝟙 V := by
      apply Yoneda.fullyFaithful.map_injective
      rw [Functor.map_comp, hδ, hpr, Category.assoc, Iso.inv_hom_id_assoc, dgk_prj, CategoryTheory.Functor.map_id]
    have h2 : pr0 ≫ h = π ≫ h := by
      apply Yoneda.fullyFaithful.map_injective
      rw [Functor.map_comp, hpr, Category.assoc, prj_f, ← he]
      rfl
    haveI : IsSeparated (pr0 ≫ h) := by rw [h2]; infer_instance
    haveI : IsSeparated pr0 := IsSeparated.of_comp pr0 h
    haveI : IsClosedImmersion (δ ≫ pr0) := by rw [h1]; infer_instance
    haveI : IsClosedImmersion δ := IsClosedImmersion.of_comp δ pr0
    have key : δ ≫ π ≫ h = h := by rw [← h2, ← Category.assoc, h1, Category.id_comp]
    haveI : UniversallyInjective (π ≫ h) :=
      MorphismProperty.comp_mem @UniversallyInjective π h ‹_› ‹_›
    haveI : Surjective δ := by
      constructor
      intro z
      refine ⟨pr0 z, (π ≫ h).injective ?_⟩
      rw [← Scheme.Hom.comp_apply, key, ← h2] <;> rfl
    have hN := eqv_tw_map_closedImmersion_surjective hB3 hE1 q i δ (unit_map q (π ≫ h) hq)
    have hdg : disc.map ((dg h).app n) = sch.map δ ≫ disc.map e.hom := by
      change disc.map (dgk h n) = disc.map (yoneda.map δ) ≫ disc.map e.hom
      rw [← Functor.map_comp, hδ, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hdg]
    exact (hcomp _ _ _ _ _).1 hN (hiso _ _ _ (disc.mapIso e).isIso_hom)
  rw [← dg_aug h]
  exact (hcomp _ _ _ _ _).1 hd hc

theorem UpperTheory.cech_descent_twist_of_proper_surjective_strictly_henselian :
    Hyps → ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ {Y : Scheme.{0}} (g : Y ⟶ Sp A) [IsProper g] [Surjective g] (i : ℤ), Eqv _ (cechAug g) (tw q i) := by
  intro hH q _ A _ hA hq Y g _ _ i
  obtain ⟨-, -, hA3, -, -, -, -, -, -, -, -, -, hB3, hB4, -, -, -, -, -, -, -, -, -, -, hE1, hE2, -⟩ := hH
  obtain ⟨hiso, hcomp, hqi, -⟩ := GlobalTheory.T.etaleCohomologyEquivalence_basic_properties (ZMod q) (tw q i)
  obtain ⟨hHL, hsep⟩ := id hA
  haveI := hHL
  haveI := hsep
  let k := IsLocalRing.ResidueField A
  let K := AlgebraicClosure k
  let r : Spec (CommRingCat.of k) ⟶ Sp A := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
  let u : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hb : bpt A = u ≫ r := rfl
  have hqA : IsUnit (q : Γ(Sp A, ⊤)) := by
    simpa using hq.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hqk : IsUnit (q : Γ(Spec (CommRingCat.of k), ⊤)) := unit_map q r hqA
  haveI : IsIntegralHom u := IsIntegralHom.SpecMap_iff.mpr (fun x => Algebra.IsIntegral.isIntegral x)
  haveI : UniversallyInjective u := by
    refine ((tfae_universallyInjective u).out 0 1).mpr ?_
    intro L _ g₁ g₂ hg
    simp only at hg
    rw [← Spec.map_preimage g₁, ← Spec.map_preimage g₂] at hg ⊢
    rw [← Spec.map_comp, ← Spec.map_comp] at hg
    have h3 := Spec.map_injective hg
    congr 1
    exact CommRingCat.hom_ext
      (IsPurelyInseparable.injective_comp_algebraMap k K L (congrArg CommRingCat.Hom.hom h3 :))
  haveI : Surjective u := ⟨fun x => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  have hu := eqv_tw_map_integral_univInjective_surjective hA3 hB3 hB4 hE1 q i u hqk
  have hr : Eqv (ZMod q) (sch.map r) (tw q i) := hE1 q A (IsLocalRing.maximalIdeal A) hq i
  have hbE : Eqv (ZMod q) (sch.map (bpt A)) (tw q i) := by
    rw [hb, Functor.map_comp]
    exact (hcomp _ _ _ _ _).1 hu hr
  have hBC : ∀ {Z : Scheme.{0}} (p : Z ⟶ Sp A) [IsProper p],
      Eqv (ZMod q) (sch.map (pullback.fst p (bpt A))) (tw q i) := by
    intro Z p _
    have s1 := IsPullback.of_hasPullback p r
    have s2 := IsPullback.of_hasPullback (pullback.snd p r) u
    have s12 := s2.paste_horiz s1
    have s0 := IsPullback.of_hasPullback p (bpt A)
    rw [← IsPullback.isoIsPullback_hom_fst _ _ s0 s12, Functor.map_comp, Functor.map_comp]
    have hf1 : Eqv (ZMod q) (sch.map (pullback.fst p r)) (tw q i) := hE2 q A hA hq p i
    haveI : IsIntegralHom (pullback.fst (pullback.snd p r) u) := inferInstance
    haveI : UniversallyInjective (pullback.fst (pullback.snd p r) u) :=
      MorphismProperty.of_isPullback (P := @UniversallyInjective) (IsPullback.of_hasPullback (pullback.snd p r) u).flip inferInstance
    haveI : Surjective (pullback.fst (pullback.snd p r) u) := inferInstance
    have hf2 := eqv_tw_map_integral_univInjective_surjective hA3 hB3 hB4 hE1 q i (pullback.fst (pullback.snd p r) u)
      (unit_map q (pullback.snd p r) hqk)
    exact (hcomp _ _ _ _ _).1 (hiso _ _ _ inferInstance) ((hcomp _ _ _ _ _).1 hf2 hf1)
  haveI : IsProper (pullback.snd g (bpt A)) := inferInstance
  haveI : Surjective (pullback.snd g (bpt A)) := inferInstance
  haveI : CompactSpace ↑(pullback g (bpt A) : Scheme.{0}) := by
    rw [← isCompact_univ_iff]
    simpa using QuasiCompact.isCompact_preimage (f := pullback.snd g (bpt A)) _ isOpen_univ isCompact_univ
  obtain ⟨y0, -⟩ := (pullback.snd g (bpt A)).surjective (IsLocalRing.closedPoint K)
  obtain ⟨y, -, hy⟩ := IsClosed.exists_closed_singleton (isClosed_univ (X := ↑(pullback g (bpt A) : Scheme.{0})))
    ⟨y0, trivial⟩
  let σ := pointOfClosedPoint (pullback.snd g (bpt A)) y hy
  have hσ : σ ≫ pullback.snd g (bpt A) = 𝟙 _ := pointOfClosedPoint_comp _ _ _
  have hcg' : Eqv (ZMod q) (cechAug (pullback.snd g (bpt A))) (tw q i) := by
    apply hqi
    apply GlobalTheory.T.quasiIso_chains_cechNerve_of_surjective (ZMod q) (yoneda.map (pullback.snd g (bpt A)))
    intro U x
    refine ⟨x ≫ σ, ?_⟩
    change (x ≫ σ) ≫ pullback.snd g (bpt A) = x
    rw [Category.assoc, hσ, Category.comp_id]
  obtain ⟨m, hm, -⟩ := GlobalTheory.T.etaleCechNerve_baseChange_isPullback Y (Sp A) (pullback g (bpt A)) (Spec (CommRingCat.of K))
    (pullback.fst g (bpt A)) (pullback.snd g (bpt A)) g (bpt A) (IsPullback.of_hasPullback g (bpt A))
  have hmE : Eqv (ZMod q) m (tw q i) := by
    apply hA3 (ZMod q) m (tw q i)
    intro n
    have hmn := hm.map ((evaluation SimplexCategoryᵒᵖ PSh).obj n)
    obtain ⟨Z, π, e, hπ, he⟩ := GlobalTheory.T.exists_representable_cech_level_of_stable @IsProper Y (Sp A) g inferInstance n
    haveI : IsProper π := hπ
    have sq0 := (IsPullback.of_hasPullback (π ≫ g) (bpt A)).map yoneda
    have sq : IsPullback (yoneda.map (pullback.fst (π ≫ g) (bpt A)) ≫ e.hom)
        (yoneda.map (pullback.snd (π ≫ g) (bpt A))) ((cechAug g).app n) (yoneda.map (bpt A)) :=
      sq0.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _) (Category.id_comp _).symm
        ((Category.comp_id _).trans (Category.id_comp _).symm) (by rw [he]; exact Category.comp_id _)
        ((Category.comp_id _).trans (Category.id_comp _).symm)
    have hmn' : IsPullback (m.app n) ((cechAug (pullback.snd g (bpt A))).app n) ((cechAug g).app n)
        (yoneda.map (bpt A)) := hmn
    have hφ := IsPullback.isoIsPullback_hom_fst _ _ hmn' sq
    change Eqv _ (disc.map (m.app n)) _
    rw [← hφ, Functor.map_comp disc, Functor.map_comp disc]
    exact (hcomp _ _ _ _ _).1 (hiso _ _ _ (disc.mapIso (IsPullback.isoIsPullback _ _ hmn' sq)).isIso_hom)
      ((hcomp _ _ _ _ _).1 (hBC (π ≫ g)) (hiso _ _ _ (disc.mapIso e).isIso_hom))
  have hw := hm.w
  have h1 : Eqv (ZMod q) (m ≫ cechAug g) (tw q i) := by
    rw [hw]
    exact (hcomp _ _ _ _ _).1 hcg' hbE
  exact (hcomp _ _ _ _ _).2.1 hmE h1
