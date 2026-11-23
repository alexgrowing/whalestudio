import Development.EtaleCohomology.CohomologicalPurity.LeafExcLevelPf

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC AlgebraicGeometry CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.EquivalenceOfExcision
variable (R : Type) [CommRing R]
instance i1 : PreservesColimitsOfShape WalkingSpan (ModuleCat.free (ULift.{1, 0} R)) :=
  haveI := (ModuleCat.adj (ULift.{1, 0} R)).leftAdjoint_preservesColimits; inferInstance
instance i2 : PreservesColimitsOfShape WalkingSpan (free R) := by
  unfold free freeP; infer_instance
instance i3 : PreservesColimitsOfShape WalkingSpan (chainsN R) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro n
  have e : chainsN R ⋙ HomologicalComplex.eval _ _ n ≅
      (evaluation SimplexCategoryᵒᵖ PSh).obj (Opposite.op (SimplexCategory.mk n)) ⋙ free R :=
    NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)
  exact preservesColimitsOfShape_of_natIso e.symm
instance i4 : PreservesColimitsOfShape WalkingSpan (ComplexShape.embeddingDownNat.extendFunctor (Shv R)) := by
  apply HomologicalComplex.preservesColimitsOfShape_of_eval
  intro m
  by_cases hm : ∃ k, ComplexShape.embeddingDownNat.f k = m
  · obtain ⟨k, hk⟩ := hm
    have e : ComplexShape.embeddingDownNat.extendFunctor (Shv R) ⋙ HomologicalComplex.eval _ _ m ≅
        HomologicalComplex.eval _ _ k :=
      NatIso.ofComponents (fun K => K.extendXIso _ hk) (by
        intro K L φ
        change (HomologicalComplex.extendMap φ _).f m ≫ (L.extendXIso _ hk).hom = (K.extendXIso _ hk).hom ≫ φ.f k
        rw [HomologicalComplex.extendMap_f φ _ hk]; simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    exact preservesColimitsOfShape_of_natIso e.symm
  · push Not at hm
    have hz : ∀ K : ChainComplex (Shv R) ℕ,
        IsZero ((ComplexShape.embeddingDownNat.extendFunctor (Shv R) ⋙ HomologicalComplex.eval _ _ m).obj K) :=
      fun K => K.isZero_extend_X _ m hm
    exact ⟨fun {K} => ⟨fun {c} _ => ⟨{
      desc := fun s => (hz _).to_ s.pt
      fac := fun s j => (hz _).eq_of_src _ _
      uniq := fun s _ _ => (hz _).eq_of_src _ _ }⟩⟩⟩
instance i5 : PreservesColimitsOfShape WalkingSpan (chains R) := by
  unfold chains; infer_instance

theorem hkc (R : Type) [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  unfold HK.pull HK.pre
  simp only [cpre]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]
theorem hki (R : Type) [CommRing R] {K : Cx R} (F : Shv R) (n : ℤ) (x : HK R K F n) :
    HK.pull R (𝟙 K) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  unfold HK.pull HK.pre
  simp only [cpre]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem hkc' (R : Type) [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := hkc R f g F n x

section
variable {P' P : Arrow Spc} (φ : P' ⟶ P)
open LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut

abbrev jj : P.right ⟶ MM φ := pushout.inr _ _
abbrev ii : P'.right ⟶ MM φ := pushout.inl _ _
def rr : MM φ ⟶ P.right := pushout.desc φ.right (𝟙 _) (by simp)
def hh : dbl P' ⟶ MM φ := pushout.desc (ii φ) (φ.right ≫ jj φ) (by
  exact (pushout.condition).trans (Category.assoc _ _ _))
abbrev Jr : Arrow Spc := Arrow.mk (jj φ)
def ss : dbl (Jr φ) ⟶ MM φ := pushout.desc (𝟙 _) (rr φ ≫ jj φ) (by
  change jj φ ≫ 𝟙 _ = jj φ ≫ rr φ ≫ jj φ
  rw [← Category.assoc, show jj φ ≫ rr φ = 𝟙 _ from pushout.inr_desc _ _ _]; simp)

theorem jr : jj φ ≫ rr φ = 𝟙 _ := pushout.inr_desc _ _ _
theorem j_gM : jj φ ≫ gM φ = dbl.inr P := pushout.inr_desc _ _ _
theorem gM_fold : gM φ ≫ dbl.fold P = rr φ := by
  apply pushout.hom_ext
  · show (pushout.inl _ _ ≫ gM φ) ≫ dbl.fold P = pushout.inl _ _ ≫ rr φ
    erw [pushout.inl_desc, pushout.inl_desc, Category.assoc, pushout.inl_desc, Category.comp_id]
  · show (pushout.inr _ _ ≫ gM φ) ≫ dbl.fold P = pushout.inr _ _ ≫ rr φ
    erw [pushout.inr_desc, pushout.inr_desc, pushout.inr_desc]
theorem h_gM : hh φ ≫ gM φ = dbl.map φ := by
  apply pushout.hom_ext
  · show (pushout.inl _ _ ≫ hh φ) ≫ gM φ = pushout.inl _ _ ≫ dbl.map φ
    erw [pushout.inl_desc, pushout.inl_desc, pushout.inl_desc]; rfl
  · show (pushout.inr _ _ ≫ hh φ) ≫ gM φ = pushout.inr _ _ ≫ dbl.map φ
    erw [pushout.inr_desc, Category.assoc, pushout.inr_desc, pushout.inr_desc]; rfl
theorem inl_h : dbl.inl P' ≫ hh φ = ii φ := pushout.inl_desc _ _ _
theorem inr_h : dbl.inr P' ≫ hh φ = φ.right ≫ jj φ := pushout.inr_desc _ _ _
theorem etale_mapping_cylinder_double_section_inl_comp : dbl.inl (Jr φ) ≫ ss φ = 𝟙 _ := pushout.inl_desc _ _ _
theorem etale_mapping_cylinder_double_section_inr_comp : dbl.inr (Jr φ) ≫ ss φ = rr φ ≫ jj φ := pushout.inr_desc _ _ _

theorem key (hR : LeafRel) (q : ℕ) (i n : ℤ) (y : Ht q (MM φ) n i)
    (h1 : pull _ (jj φ) (tw q i) n y = 0) (h2 : pull _ (hh φ) (tw q i) n y = 0) : y = 0 := by
  obtain ⟨e, he⟩ := hR q i
  have PO : IsPushout ((chains (ZMod q)).map P'.hom) ((chains (ZMod q)).map (P'.hom ≫ φ.right)) ((chains (ZMod q)).map (ii φ)) ((chains (ZMod q)).map (jj φ)) :=
    (IsPushout.of_hasPushout P'.hom (P'.hom ≫ φ.right)).map _
  let pM : (chains (ZMod q)).obj (MM φ) ⟶ cokernel ((chains (ZMod q)).map P'.hom) := PO.desc (cokernel.π ((chains (ZMod q)).map P'.hom)) 0 (by simp)
  have pM1 : (chains (ZMod q)).map (ii φ) ≫ pM = cokernel.π _ := PO.inl_desc _ _ _
  have pM2 : (chains (ZMod q)).map (jj φ) ≫ pM = 0 := PO.inr_desc _ _ _
  have wκ : (chains (ZMod q)).map P'.hom ≫ (chains (ZMod q)).map (ii φ) ≫ cokernel.π ((chains (ZMod q)).map (jj φ)) = 0 := by
    have hc : P'.hom ≫ ii φ = (P'.hom ≫ φ.right) ≫ jj φ := pushout.condition
    rw [← Category.assoc, ← (chains (ZMod q)).map_comp, hc, (chains (ZMod q)).map_comp, Category.assoc, cokernel.condition, comp_zero]
  let κ : cokernel ((chains (ZMod q)).map P'.hom) ⟶ cokernel ((chains (ZMod q)).map (Jr φ).hom) := cokernel.desc _ _ wκ
  let κ' : cokernel ((chains (ZMod q)).map (Jr φ).hom) ⟶ cokernel ((chains (ZMod q)).map P'.hom) := cokernel.desc ((chains (ZMod q)).map (jj φ)) pM pM2
  have hπ : pM ≫ κ = cokernel.π ((chains (ZMod q)).map (Jr φ).hom) := by
    apply PO.hom_ext
    · rw [← Category.assoc, pM1]; exact cokernel.π_desc _ _ _
    · rw [← Category.assoc, pM2, zero_comp]; exact (cokernel.condition _).symm
  have hκ : κ' ≫ κ = 𝟙 _ := by
    apply coequalizer.hom_ext
    rw [Category.comp_id]; exact (cokernel.π_desc_assoc _ _ _ _).trans hπ
  let s : Hs q (Jr φ) n i := ⟨pull _ (ss φ) _ n y, by
    change pull _ (dbl.inr (Jr φ)) _ n (pull _ (ss φ) _ n y) = 0
    rw [← pull_comp, etale_mapping_cylinder_double_section_inr_comp, pull_comp, h1, map_zero]⟩
  let x := (e (Jr φ) n).symm s
  have hx : (e (Jr φ) n x).1 = HK.pull _ ((chains (ZMod q)).map (ss φ) ≫ cokernel.π _) (tw q i) n x := by
    apply he
    · rw [← Category.assoc, ← (chains (ZMod q)).map_comp, etale_mapping_cylinder_double_section_inl_comp, (chains (ZMod q)).map_id, Category.id_comp]
    · rw [← Category.assoc, ← (chains (ZMod q)).map_comp, etale_mapping_cylinder_double_section_inr_comp, (chains (ZMod q)).map_comp, Category.assoc]
      erw [cokernel.condition, comp_zero]
  have hs : (e (Jr φ) n x).1 = pull _ (ss φ) _ n y := by simp [x, s]
  have hy : y = pull _ (dbl.inl (Jr φ)) _ n (pull _ (ss φ) _ n y) := by
    rw [← pull_comp, etale_mapping_cylinder_double_section_inl_comp, pull_id]
  have hp : (e P' n (HK.pull _ κ (tw q i) n x)).1 = HK.pull _ ((chains (ZMod q)).map (hh φ) ≫ pM) (tw q i) n (HK.pull _ κ (tw q i) n x) := by
    apply he
    · rw [← Category.assoc, ← (chains (ZMod q)).map_comp, inl_h, pM1]
    · rw [← Category.assoc, ← (chains (ZMod q)).map_comp, inr_h, (chains (ZMod q)).map_comp, Category.assoc, pM2, comp_zero]
  have hh0 : pull _ (hh φ) _ n y = HK.pull _ ((chains (ZMod q)).map (hh φ) ≫ pM) (tw q i) n (HK.pull _ κ (tw q i) n x) := by
    rw [← hkc', Category.assoc, hπ, hy, ← pull_comp, ← hs, hx]
    change HK.pull _ ((chains (ZMod q)).map _) _ n _ = _
    have hhs : hh φ ≫ dbl.inl (Jr φ) ≫ ss φ = hh φ := by rw [etale_mapping_cylinder_double_section_inl_comp]; exact Category.comp_id _
    rw [← hkc', ← Category.assoc, ← (chains (ZMod q)).map_comp, Category.assoc, hhs]
  have hz : HK.pull _ κ (tw q i) n x = 0 := by
    apply (e P' n).injective
    rw [map_zero]; apply Subtype.ext; rw [hp, ← hh0, h2]; rfl
  have hx0 : x = 0 := by
    rw [← hki _ (tw q i) n x, ← hκ, hkc', hz, map_zero]
  rw [hy, ← hs, hx0, map_zero]; rfl

end

end LateralTheory.CohomologicalPurity.EquivalenceOfExcision

namespace LateralTheory.CohomologicalPurity.TubeCut
open LateralTheory.CohomologicalPurity.EquivalenceOfExcision

theorem LeafEqvOfExc_of (hR : LeafRel) : LeafEqvOfExc := by
  intro q P' P φ hE i n
  open LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut in
  constructor
  · intro a b hab
    rw [← sub_eq_zero] at hab ⊢
    rw [← map_sub] at hab
    set x := a - b
    have h1 : pull _ (dbl.inr P) (tw q i) n x = 0 := by
      rw [← j_gM φ, pull_comp, hab, map_zero]
    have h2 : Hs.pull q φ n i ⟨x, h1⟩ = 0 := by
      apply Subtype.ext
      change pull _ (dbl.map φ) _ n x = 0
      rw [← h_gM φ, pull_comp, hab, map_zero]
    have := (hE n i).1 (h2.trans (map_zero _).symm)
    exact congrArg Subtype.val this
  · intro y
    set y0 := y - pull _ (rr φ) (tw q i) n (pull _ (jj φ) (tw q i) n y)
    have hy0 : pull _ (jj φ) (tw q i) n y0 = 0 := by
      simp only [y0, map_sub]; rw [← pull_comp, jr, pull_id, sub_self]
    let z : Hs q P' n i := ⟨pull _ (hh φ) _ n y0, by
      change pull _ (dbl.inr P') _ n (pull _ (hh φ) _ n y0) = 0
      rw [← pull_comp, inr_h, pull_comp, hy0, map_zero]⟩
    obtain ⟨x, hx⟩ := (hE n i).2 z
    have hd : pull _ (gM φ) (tw q i) n x.1 - y0 = 0 := by
      apply key φ hR q i n
      · rw [map_sub, ← pull_comp, j_gM, hy0, sub_zero]; exact x.2
      · rw [map_sub, ← pull_comp, h_gM, sub_eq_zero]; exact congrArg Subtype.val hx
    refine ⟨x.1 + pull _ (dbl.fold P) (tw q i) n (pull _ (jj φ) (tw q i) n y), ?_⟩
    rw [map_add, ← pull_comp, gM_fold, sub_eq_zero.mp hd]
    simp [y0]

end LateralTheory.CohomologicalPurity.TubeCut
