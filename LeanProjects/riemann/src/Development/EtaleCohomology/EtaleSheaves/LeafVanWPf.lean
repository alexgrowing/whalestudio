import Development.EtaleCohomology.EtaleSheaves.LeafVanStalk

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.LeafVanWPf
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafVan0Pf

section Cone
variable {C : Type*} [Category C] [Preadditive C] {K L M : CochainComplex C ℤ} (φ : K ⟶ L) [HomologicalComplex.HasHomotopyCofiber φ]

theorem desc_δ {n m : ℤ} (α : Cochain K M m) (β : Cochain L M n) (h : m + 1 = n) (n' : ℤ) (hn' : n + 1 = n') :
    δ n n' (mappingCone.descCochain φ α β h) =
      mappingCone.descCochain φ (δ m n α + n'.negOnePow • (Cochain.ofHom φ).comp β (zero_add n)) (δ n n' β) hn' := by
  rw [mappingCone.δ_descCochain φ α β h n' hn']; rfl

theorem desc_eq_zero {n m : ℤ} {α : Cochain K M m} {β : Cochain L M n} {h : m + 1 = n}
    (H : mappingCone.descCochain φ α β h = 0) : α = 0 ∧ β = 0 := by
  constructor
  · have := mappingCone.inl_descCochain φ α β h
    rw [H, Cochain.comp_zero] at this; exact this.symm
  · have := mappingCone.inr_descCochain φ α β h
    rw [H, Cochain.comp_zero] at this; exact this.symm

theorem units_mul_self' (u : ℤˣ) : u * u = 1 := Int.units_mul_self u

theorem cone_zero
    (hinj : ∀ (n : ℤ) (x : Cocycle L M n),
      CohomologyClass.mk (zcomp (Cocycle.ofHom φ) x (zero_add n)) = 0 → CohomologyClass.mk x = 0)
    (hsurj : ∀ (n : ℤ) (y : Cocycle K M n), ∃ x : Cocycle L M n,
      CohomologyClass.mk (zcomp (Cocycle.ofHom φ) x (zero_add n)) = CohomologyClass.mk y)
    (n : ℤ) (z : Cocycle (mappingCone φ) M n) : CohomologyClass.mk z = 0 := by
  set a : Cochain K M (n - 1) := (mappingCone.inl φ).comp z.1 (by omega) with ha
  set b : Cochain L M n := (Cochain.ofHom (mappingCone.inr φ)).comp z.1 (zero_add n) with hb
  have hz : z.1 = mappingCone.descCochain φ a b (by omega) := by
    rw [mappingCone.ext_cochain_from_iff φ (n - 1) n (by omega)]
    simp [ha, hb]
  have h0 := Cocycle.δ_eq_zero z (n + 1)
  rw [hz, desc_δ φ a b _ (n + 1) rfl] at h0
  obtain ⟨h1, h2⟩ := desc_eq_zero φ h0
  have hda : δ (n - 1) n a = -((n + 1).negOnePow • (Cochain.ofHom φ).comp b (zero_add n)) := eq_neg_of_add_eq_zero_left h1
  let bc : Cocycle L M n := Cocycle.mk b (n + 1) rfl h2
  have hb0 : CohomologyClass.mk bc = 0 := by
    apply hinj
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
    refine ⟨-((n + 1).negOnePow • a), ?_⟩
    rw [δ_neg, δ_units_smul, hda, smul_neg, neg_neg, smul_smul, units_mul_self', one_smul]
    simp [zcomp, bc]
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)] at hb0
  obtain ⟨γ, hγ⟩ := hb0
  change δ (n - 1) n γ = b at hγ
  set a' : Cochain K M (n - 1) := a - n.negOnePow • (Cochain.ofHom φ).comp γ (zero_add _) with ha'
  let w : Cochain (mappingCone φ) M (n - 1) := mappingCone.descCochain φ (0 : Cochain K M (n - 1 - 1)) γ (by omega)
  have hw : δ (n - 1) n w = mappingCone.descCochain φ (n.negOnePow • (Cochain.ofHom φ).comp γ (zero_add _)) b (by omega) := by
    simp only [w]; rw [desc_δ φ _ γ _ n (by omega), hγ, δ_zero, zero_add]
  have hda' : δ (n - 1) n a' = 0 := by
    have e : mappingCone.descCochain φ a' (0 : Cochain L M n) (by omega) = z.1 - δ (n - 1) n w := by
      rw [hz, hw, mappingCone.ext_cochain_from_iff φ (n - 1) n (by omega)]
      simp [ha']
    have e2 := congrArg (δ n (n + 1)) e
    rw [δ_sub, δ_δ, sub_zero, Cocycle.δ_eq_zero, desc_δ φ _ _ _ (n + 1) rfl] at e2
    have := (desc_eq_zero φ e2).1
    simpa using this
  obtain ⟨x, hx⟩ := hsurj (n - 1) (Cocycle.mk a' n (by omega) hda')
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1 - 1) (by omega)] at hx
  obtain ⟨γ', hγ'⟩ := hx
  change δ (n - 1 - 1) (n - 1) γ' = (Cochain.ofHom φ).comp x.1 (zero_add _) - a' at hγ'
  have hdx := Cocycle.δ_eq_zero x n
  rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨w + n.negOnePow • mappingCone.descCochain φ (0 : Cochain K M (n - 1 - 1)) x.1 (by omega) -
    mappingCone.descCochain φ γ' (0 : Cochain L M (n - 1)) (by omega), ?_⟩
  rw [δ_sub, δ_add, δ_units_smul, hw, desc_δ φ _ _ _ n (by omega), desc_δ φ _ _ _ n (by omega), hγ', hdx]
  change _ = z.1
  rw [hz, mappingCone.ext_cochain_from_iff φ (n - 1) n (by omega)]
  constructor
  · simp only [mappingCone.inl_descCochain, Cochain.comp_add, Cochain.comp_sub, Cochain.comp_units_smul, δ_zero, zero_add,
      Cochain.comp_zero, smul_zero, add_zero, smul_smul, units_mul_self', one_smul, ha']
    abel
  · simp
end Cone

section Geo
variable {R : Type} [CommRing R] (F : Shv R)

theorem hrel_sub {U E : Spc} (f : U ⟶ E) (h : Eqv R f F) (n : ℤ) : Subsingleton (Hrel R f F n) := by
  have hinj : ∀ (n : ℤ) (x : Cocycle ((chains R).obj E) (res R F) n),
      CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) x (zero_add n)) = 0 → CohomologyClass.mk x = 0 := by
    intro n x hx
    apply (h n).1
    change CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) x (zero_add n)) = pull R f F n 0
    rw [map_zero]; exact hx
  have hsurj : ∀ (n : ℤ) (y : Cocycle ((chains R).obj U) (res R F) n), ∃ x : Cocycle ((chains R).obj E) (res R F) n,
      CohomologyClass.mk (zcomp (Cocycle.ofHom ((chains R).map f)) x (zero_add n)) = CohomologyClass.mk y := by
    intro n y
    obtain ⟨c, hc⟩ := (h n).2 (CohomologyClass.mk y)
    obtain ⟨x, rfl⟩ := c.mk_surjective
    exact ⟨x, hc⟩
  refine ⟨fun y y' => ?_⟩
  obtain ⟨z, rfl⟩ := y.mk_surjective
  obtain ⟨z', rfl⟩ := y'.mk_surjective
  change CohomologyClass.mk z = CohomologyClass.mk z'
  rw [cone_zero _ hinj hsurj n z, cone_zero _ hinj hsurj n z']

theorem eqv_of_iso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] : Eqv R (sch.map f) F := by
  intro n
  refine Function.bijective_iff_has_inverse.2 ⟨pull R (sch.map (inv f)) F n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  · rw [← pull_comp, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]

theorem eqv_of_square {P Q X Y : Scheme.{0}} (a : P ⟶ X) (f : X ⟶ Y) (h : P ⟶ Q) (c : Q ⟶ Y) (w : a ≫ f = h ≫ c)
    (ha : Eqv R (sch.map a) F) (hh : Eqv R (sch.map h) F) (hc : Eqv R (sch.map c) F) : Eqv R (sch.map f) F := by
  intro n
  have key : ∀ y, pull R (sch.map a) F n (pull R (sch.map f) F n y) = pull R (sch.map h) F n (pull R (sch.map c) F n y) := by
    intro y; rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, w]
  constructor
  · intro y y' e
    apply (hc n).1; apply (hh n).1
    rw [← key, ← key, e]
  · intro x
    obtain ⟨u, hu⟩ := (hh n).2 (pull R (sch.map a) F n x)
    obtain ⟨v, rfl⟩ := (hc n).2 u
    refine ⟨v, (ha n).1 ?_⟩
    rw [key, hu]
end Geo

theorem commGroup_inv_eq_conj_twist_identity {B W S X T : Scheme.{0}} (pA : X ⟶ S) (s : S ⟶ B) (ι : W ⟶ B) [Mono ι] (r : T ⟶ S) (w : T ⟶ W)
    (hw : w ≫ ι = r ≫ s) (hc : (pullback.fst (pullback.fst (pA ≫ s) ι ≫ pA) r ≫ pullback.fst (pA ≫ s) ι) ≫ pA =
      pullback.snd (pullback.fst (pA ≫ s) ι ≫ pA) r ≫ r) :
    IsIso (pullback.lift (pullback.fst (pullback.fst (pA ≫ s) ι ≫ pA) r ≫ pullback.fst (pA ≫ s) ι)
      (pullback.snd (pullback.fst (pA ≫ s) ι ≫ pA) r) hc) := by
  have c1 : pullback.fst pA r ≫ pA ≫ s = (pullback.snd pA r ≫ w) ≫ ι := by
    simp only [Category.assoc, hw]; exact pullback.condition_assoc s
  have c2 : pullback.lift (pullback.fst pA r) (pullback.snd pA r ≫ w) c1 ≫ pullback.fst (pA ≫ s) ι ≫ pA =
      pullback.snd pA r ≫ r := by
    rw [← Category.assoc, pullback.lift_fst, pullback.condition]
  refine ⟨⟨pullback.lift (pullback.lift (pullback.fst pA r) (pullback.snd pA r ≫ w) c1) (pullback.snd pA r) c2, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]
      · rw [← cancel_mono ι]
        simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc, hw]
        have e3 : pullback.fst (pA ≫ s) ι ≫ pA ≫ s = pullback.snd (pA ≫ s) ι ≫ ι := pullback.condition
        have e4 := pullback.condition_assoc (f := pullback.fst (pA ≫ s) ι ≫ pA) (g := r) s
        simp only [Category.assoc] at e4
        rw [← e3]
        first | exact e4 | exact e4.symm
    · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]
  · apply pullback.hom_ext
    · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]
    · simp only [Category.assoc, Category.id_comp, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]

theorem closed_eq {A : Type} [CommRing A] [IsLocalRing A] (x : Sp A) (hx : ∀ z : Sp A, z ⤳ x) :
    x = IsLocalRing.closedPoint A :=
  ((IsLocalRing.specializes_closedPoint x).antisymm (hx _)).eq

theorem LeafVanW_of : LeafVanW := by
  intro hH q _ k _ hq i B W Y b ι _ p hp A _ s hA hx m
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hE2, -⟩ := hH
  obtain ⟨hHen, hsep⟩ := hA
  haveI : IsProper p := hp
  have hqA : IsUnit (q : A) := by
    have := hq.map (Spec.preimage (s ≫ b)).hom
    simpa using this

  obtain ⟨x, hx1, w0, hw0⟩ := hx
  have hxc := closed_eq x hx1
  have hrpt : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) =
      IsLocalRing.closedPoint A := IsLocalRing.comap_closedPoint (IsLocalRing.residue A)
  haveI : Surjective (pullback.fst (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s) ι) := by
    constructor
    intro t
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s) (g := ι)
      (IsLocalRing.closedPoint (IsLocalRing.ResidueField A)) w0 (by
        have := congrArg s hrpt
        rw [← hxc, ← hw0] at this
        exact this)
    exact ⟨z, hz.trans (Subsingleton.elim _ _)⟩
  haveI := isIso_of_isClosedImmersion_of_surjective (pullback.fst (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s) ι)
  have hw : (inv (pullback.fst (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s) ι) ≫ pullback.snd _ _) ≫ ι =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) ≫ s := by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]

  have e1 := hE2 q A ⟨hHen, hsep⟩ hqA (pullback.snd p s) i
  have e2 := hE2 q A ⟨hHen, hsep⟩ hqA (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s) i
  have hc : (pullback.fst (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫
      pullback.fst (pullback.snd p s ≫ s) ι) ≫ pullback.snd p s =
      pullback.snd (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)) := by
    rw [Category.assoc, pullback.condition]
  haveI := commGroup_inv_eq_conj_twist_identity (pullback.snd p s) s ι _ _ hw hc
  have heqv : Eqv (ZMod q) (sch.map (prS p ι s)) (tw q i) :=
    eqv_of_square _ _ _ _ _ (pullback.lift_fst _ _ _).symm e2 (eqv_of_iso _ (pullback.lift (pullback.fst (pullback.fst (pullback.snd p s ≫ s) ι ≫ pullback.snd p s)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))) ≫ pullback.fst (pullback.snd p s ≫ s) ι) _ hc)) e1
  exact hrel_sub _ _ heqv m

end LateralTheory.E.LeafVanWPf
