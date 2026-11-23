import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeZeroSectionClassPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyNegativeVanishingDegreeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistSectionsLocallyGeneratedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistResolutionPairingSpecAndCupUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductAssocStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistUnitClassRootClassSpecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupUnitAndPrimitiveRootClassesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerClassOfUnitCocycleNaturalAdditiveStatement
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleCohomologyLocallyAcyclic
import Development.AutomorphicArithmetic.CommutativeAlgebra.CohomologySubsingletonPosOfStrictlyHenselian
import Development.AutomorphicArithmetic.CommutativeAlgebra.NonemptyPrimitiveRootOfStrictlyHenselian
import Development.AutomorphicArithmetic.CommutativeAlgebra.ConnectedSpaceSpecLocalAndLaurent
import Development.AutomorphicArithmetic.CommutativeAlgebra.TwistedSectionEqNsmulGeneratorOfConnected
import Development.AutomorphicArithmetic.CommutativeAlgebra.DvdExponentOfPowEqLaurentMonomial
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsRootOfKummerClassEqZero
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf

section
variable {q : ℕ} [NeZero q]

private theorem cast_zero' {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') :
    ((0 : Ht q E n i).cast hn hi : Ht q E n' i') = 0 := by
  subst hn hi; rfl

private theorem cast_eq_zero' {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E n i)
    (h : (x.cast hn hi : Ht q E n' i') = 0) : x = 0 := by
  subst hn hi; exact h

private theorem cup_cast' {E : Spc} {a a' b b' n i : ℤ} (ha : a = a') (hb : b = b') (y : Ht q E a b) (x : Ht q E n i) :
    cup q (y.cast ha hb : Ht q E a' b') x = (cup q y x).cast (by rw [ha]) (by rw [hb]) := by
  subst ha hb; rfl

private theorem inv_sch {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) : Inv q (sch.obj X) := by
  intro U hU
  obtain ⟨x⟩ := hU
  have x' : U ⟶ X := x
  simpa using ζ.2.1.map x'.appTop.hom

private theorem cupRootInj {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) (j : ℤ) {n i : ℤ} (x : Ht q (sch.obj X) n i)
    (h : cup q (rootClass j ζ) x = 0) : x = 0 := by
  have h1 : cup q (cup q (rootClass (-j) ζ) (rootClass j ζ)) x = 0 := by
    rw [GlobalTheory.T.tateTwistCupProduct_assoc, h, map_zero, cast_zero']
  rw [((GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).2 X ζ (-j) j).1] at h1
  rw [cup_cast'] at h1
  have h2 := cast_eq_zero' _ _ _ h1
  have key : ∀ (k : ℤ), k = 0 → cup q (rootClass k ζ) x = 0 → x = 0 := by
    intro k hk hx
    subst hk
    rw [((GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).2 X ζ 0 0).2, (GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).1 _ (inv_sch ζ)] at hx
    exact cast_eq_zero' _ _ _ hx
  exact key _ (by ring) h2

private theorem kum_pow {X : Scheme.{0}} (w : (Γ(X, ⊤))ˣ) (hq : IsUnit (q : Γ(X, ⊤))) (c : ℕ) :
    c • kum q w = kum q (w ^ c) := by
  induction c with
  | zero =>
    have h := ((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 (1 : (Γ(X, ⊤))ˣ) 1 hq).1
    rw [mul_one] at h
    have h0 : kum q (1 : (Γ(X, ⊤))ˣ) = 0 := by simpa using h
    simp [h0]
  | succ c ih =>
    rw [succ_nsmul, ih, pow_succ, ((GlobalTheory.T.kummerClassOfUnit_cocycle_natural_additive q).2.2 (w ^ c) w hq).1]

private theorem tors {E : Spc} {n i : ℤ} (x : Ht q E n i) {c : ℕ} (h : q ∣ c) : c • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod q), (ZMod.natCast_eq_zero_iff c q).2 h, zero_smul]

private noncomputable def secHom (i : ℤ) (X : Scheme.{0}) : Sec (tw q i) X →+ Ht q (sch.obj X) 0 i :=
  AddMonoidHom.mk' (secClass (tw q i)) (GlobalTheory.T.degreeZeroSectionClass_properties (ZMod q) (tw q i) X).2.2.1

private theorem root_eq (i : ℤ) {X : Scheme.{0}} (ζ : Prim q Γ(X, ⊤)) : rootClass i ζ = secHom i X (twGen i ζ) :=
  (GlobalTheory.T.tateTwistUnitClass_rootClass_spec q).2.2.2 i X ζ

private theorem root_every {X : Scheme.{0}} [ConnectedSpace X] (ζ : Prim q Γ(X, ⊤)) (i : ℤ) (b : Ht q (sch.obj X) 0 i) :
    ∃ c : ℕ, b = c • rootClass i ζ := by
  obtain ⟨s, rfl⟩ := (GlobalTheory.T.degreeZeroSectionClass_properties (ZMod q) (tw q i) X).2.1.2 b
  obtain ⟨c, rfl⟩ := UpperTheory.twisted_section_eq_nsmul_generator_of_connected q i X ζ s
  refine ⟨c, ?_⟩
  rw [root_eq, ← map_nsmul]
  rfl

private theorem root_tors {X : Scheme.{0}} [Nonempty X] (ζ : Prim q Γ(X, ⊤)) (i : ℤ) (c : ℕ) (h : c • rootClass i ζ = 0) :
    q ∣ c := by
  rw [root_eq, ← map_nsmul] at h
  have hinj : Function.Injective (secHom (q := q) i X) := (GlobalTheory.T.degreeZeroSectionClass_properties (ZMod q) (tw q i) X).2.1.1
  have h0 : c • twGen i ζ = 0 := hinj (h.trans (map_zero _).symm)
  exact (GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.1 X ζ c h0

private theorem pull_root {Y X : Scheme.{0}} (f : Y ⟶ X) (ζ : Prim q Γ(X, ⊤)) (i : ℤ) :
    pull _ (sch.map f) _ _ (rootClass i ζ) = rootClass i (ζ.map f.appTop.hom) := by
  rw [root_eq, root_eq]
  refine ((GlobalTheory.T.degreeZeroSectionClass_properties (ZMod q) (tw q i) X).2.2.2.1 f _).trans ?_
  rw [(GlobalTheory.T.tateTwist_sections_locally_generated q i).2.2.2.1 Y X f ζ]
  rfl

private theorem deg0 {X Y : Scheme.{0}} [ConnectedSpace X] [ConnectedSpace Y] (f : Y ⟶ X) (ζ : Prim q Γ(X, ⊤)) (i n : ℤ) (hn : n = 0) :
    Function.Bijective (pull _ (sch.map f) (tw q i) n) := by
  subst hn
  refine ⟨(injective_iff_map_eq_zero _).2 fun b hb => ?_, fun b' => ?_⟩
  · obtain ⟨c, rfl⟩ := root_every ζ i b
    rw [map_nsmul, pull_root] at hb
    exact tors _ (root_tors _ i c hb)
  · obtain ⟨c, rfl⟩ := root_every (ζ.map f.appTop.hom) i b'
    exact ⟨c • rootClass i ζ, by rw [map_nsmul, pull_root]⟩

end

theorem UpperTheory.bijective_etaleCohomology_laurentPolynomial_of_coordinate_unit :
    ∀ (q : ℕ) [NeZero q] (O : Type) [CommRing O], SH O → IsUnit (q : O) →
        ∀ u : (Γ(Spec (CommRingCat.of (LaurentPolynomial O)), ⊤))ˣ,
          (u : Γ(Spec (CommRingCat.of (LaurentPolynomial O)), ⊤)) =
            (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial O))).inv.hom (LaurentPolynomial.T 1) →
          ∀ m j : ℤ, Function.Bijective fun p : Ht q (sp O) (m + 1) (j + 1) × Ht q (sp O) m j =>
            pull _ (spMap (LaurentPolynomial.C : O →+* LaurentPolynomial O)) _ _ p.1 +
              cup q (pull _ (spMap (LaurentPolynomial.C : O →+* LaurentPolynomial O)) _ _ p.2) (kum q u) := by
  intro q _ O _ hSH hq u hu m j
  have hSH' := hSH
  obtain ⟨hh, hsep⟩ := hSH'
  haveI : HenselianLocalRing O := hh
  haveI : ConnectedSpace (Spec (CommRingCat.of O)) := (UpperTheory.connectedSpace_spec_local_and_laurent O).1
  haveI : ConnectedSpace (Spec (CommRingCat.of (LaurentPolynomial O))) := (UpperTheory.connectedSpace_spec_local_and_laurent O).2
  obtain ⟨ζ₀⟩ := UpperTheory.nonempty_primitive_root_of_strictly_henselian q O hSH hq
  let ζ : Prim q Γ(Spec (CommRingCat.of O), ⊤) := ζ₀.map (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
  let f : Spec (CommRingCat.of (LaurentPolynomial O)) ⟶ Spec (CommRingCat.of O) :=
    Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : O →+* LaurentPolynomial O))
  let ζ' := ζ.map f.appTop.hom
  have hqL : IsUnit (q : Γ(Spec (CommRingCat.of (LaurentPolynomial O)), ⊤)) := ζ'.2.1
  have hC5 := UpperTheory.Cb.etale_cohomology_locally_acyclic q O hSH hq
  have hneg : ∀ (E : Spc) (n i : ℤ), n < 0 → Subsingleton (Ht q E n i) := fun E n i hn =>
    (GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q i)).1 E n hn
  have hpos : ∀ (n i : ℤ), 0 < n → Subsingleton (Ht q (sp O) n i) := fun n i hn => UpperTheory.cohomology_subsingleton_pos_of_strictly_henselian (ZMod q) O hSH (tw q i) n hn

  have hinj : Function.Injective fun b : Ht q (sp O) 0 j => cup q (pull _ (sch.map f) _ _ b) (kum q u) := by
    have hadd : ∀ a b : Ht q (sp O) 0 j, cup q (pull _ (sch.map f) _ _ (a + b)) (kum q u) =
        cup q (pull _ (sch.map f) _ _ a) (kum q u) + cup q (pull _ (sch.map f) _ _ b) (kum q u) := by
      intro a b
      rw [map_add, map_add, AddMonoidHom.add_apply]
    refine (injective_iff_map_eq_zero (AddMonoidHom.mk' _ hadd)).2 fun b hb => ?_
    change cup q (pull _ (sch.map f) _ _ b) (kum q u) = 0 at hb
    obtain ⟨c, rfl⟩ := root_every ζ j b
    rw [map_nsmul, pull_root, map_nsmul, AddMonoidHom.nsmul_apply, ← map_nsmul, kum_pow u hqL] at hb
    obtain ⟨v, hv⟩ := UpperTheory.exists_root_of_kummer_class_eq_zero q _ (u ^ c) hqL (cupRootInj ζ' j _ hb)
    refine tors _ (UpperTheory.dvd_exponent_of_pow_eq_laurent_monomial q O c (Units.map (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial O))).hom.hom.toMonoidHom v) ?_)
    have h1 := congrArg (fun w : (Γ(Spec (CommRingCat.of (LaurentPolynomial O)), ⊤))ˣ =>
      (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial O))).hom.hom (w : Γ(Spec (CommRingCat.of (LaurentPolynomial O)), ⊤))) hv
    simp only [Units.val_pow_eq_pow_val, map_pow, hu] at h1
    have h2 : (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial O))).hom.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial O))).inv.hom (LaurentPolynomial.T 1)) = LaurentPolynomial.T 1 := by
      simp
    rw [h2, LaurentPolynomial.T_pow] at h1
    simpa using h1
  have hsurj : Function.Surjective fun b : Ht q (sp O) 0 j => cup q (pull _ (sch.map f) _ _ b) (kum q u) := by
    obtain ⟨e⟩ : Nonempty (Ht q (sch.obj (Spec (CommRingCat.of (LaurentPolynomial O)))) (0 + 1) (j + 1) ≃+ ZMod q) := (hC5 1 (j + 1)).2
    haveI : Finite (Ht q (sch.obj (Spec (CommRingCat.of (LaurentPolynomial O)))) (0 + 1) (j + 1)) := Finite.of_equiv _ e.symm.toEquiv
    have key : ∀ a b : ℕ, b < q → a ≤ b → a • rootClass j ζ = b • rootClass j ζ → a = b := by
      intro a b hb hle h
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [add_nsmul, left_eq_add] at h
      have := Nat.eq_zero_of_dvd_of_lt (root_tors ζ j d h) (by omega)
      omega
    have hfin : Function.Injective fun c : Fin q => (c : ℕ) • rootClass j ζ := by
      intro a b hab
      rcases le_total (a : ℕ) (b : ℕ) with h | h
      · exact Fin.ext (key _ _ b.2 h hab)
      · exact Fin.ext (key _ _ a.2 h hab.symm).symm
    have hcomp := Function.Injective.bijective_of_nat_card_le (hinj.comp hfin) (by
      rw [Nat.card_congr e.toEquiv, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin])
    exact Function.Surjective.of_comp hcomp.2
  rcases lt_trichotomy m 0 with hm | hm | hm
  · rcases eq_or_lt_of_le (show m + 1 ≤ 0 by omega) with h0 | h0
    · have hm' : m = -1 := by omega
      subst hm'
      haveI := hneg (sp O) (-1) j (by norm_num)
      have hb := deg0 f ζ (j + 1) _ h0
      refine ⟨fun p p' h => ?_, fun y => ?_⟩
      · have h2 : p.2 = p'.2 := Subsingleton.elim _ _
        have h3 : pull _ (sch.map f) _ _ p.1 = pull _ (sch.map f) _ _ p'.1 := by
          have h' : pull _ (sch.map f) _ _ p.1 + _ = pull _ (sch.map f) _ _ p'.1 + _ := h
          rw [h2] at h'
          exact add_right_cancel h'
        exact Prod.ext (hb.1 h3) h2
      · obtain ⟨b, rfl⟩ := hb.2 y
        refine ⟨(b, 0), ?_⟩
        simp
        rfl
    · haveI := hneg (sp O) _ (j + 1) h0
      haveI := hneg (sp O) m j hm
      haveI := hneg (sp (LaurentPolynomial O)) _ (j + 1) h0
      exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  · subst hm
    haveI := hpos (0 + 1) (j + 1) (by norm_num)
    refine ⟨fun p p' h => ?_, fun y => ?_⟩
    · have h1 : p.1 = p'.1 := Subsingleton.elim _ _
      have h' : pull _ (sch.map f) _ _ p.1 + _ = pull _ (sch.map f) _ _ p'.1 + _ := h
      rw [h1] at h'
      exact Prod.ext h1 (hinj (add_left_cancel h'))
    · obtain ⟨b, rfl⟩ := hsurj y
      refine ⟨(0, b), ?_⟩
      simp
      rfl
  · haveI := hpos (m + 1) (j + 1) (by omega)
    haveI := hpos m j hm
    haveI := (hC5 (m + 1) (j + 1)).1 (by omega)
    exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
