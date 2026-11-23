import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeHomSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleChainsDiscBiprodDescIsIso
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.SectionRestriction

variable {R : Type} [CommRing R]

private theorem pl_comp {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ) (x : HK R M F n) :
    HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

private theorem pl_id {K : Cx R} (F : Shv R) (n : ℤ) (x : HK R K F n) : HK.pull R (𝟙 K) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

private theorem pl_zero {K L : Cx R} (F : Shv R) (n : ℤ) (x : HK R L F n) :
    HK.pull R (0 : K ⟶ L) F n x = 0 := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [← CohomologyClass.mk_zero]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

private theorem pl_add {K L : Cx R} (f g : K ⟶ L) (F : Shv R) (n : ℤ) (x : HK R L F n) :
    HK.pull R (f + g) F n x = HK.pull R f F n x + HK.pull R g F n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [HK.pull, HK.pull, HK.pull, HK.pre, HK.pre, HK.pre, cpre_mk, cpre_mk, cpre_mk, ← CohomologyClass.mk_add]
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_add]

private theorem split_bij {K₁ K₂ L : Cx R} (c₁ : K₁ ⟶ L) (c₂ : K₂ ⟶ L) (hd : IsIso (biprod.desc c₁ c₂))
    (F : Shv R) (n : ℤ) :
    Function.Bijective fun x : HK R L F n => (HK.pull R c₁ F n x, HK.pull R c₂ F n x) := by
  set d := biprod.desc c₁ c₂ with hdd
  let r₁ : L ⟶ K₁ := inv d ≫ biprod.fst
  let r₂ : L ⟶ K₂ := inv d ≫ biprod.snd
  have e₁ : c₁ = biprod.inl ≫ d := by simp [hdd]
  have e₂ : c₂ = biprod.inr ≫ d := by simp [hdd]
  have h11 : c₁ ≫ r₁ = 𝟙 _ := by simp [r₁, e₁]
  have h12 : c₁ ≫ r₂ = 0 := by simp [r₂, e₁]
  have h21 : c₂ ≫ r₁ = 0 := by simp [r₁, e₂]
  have h22 : c₂ ≫ r₂ = 𝟙 _ := by simp [r₂, e₂]
  have hs : r₁ ≫ c₁ + r₂ ≫ c₂ = 𝟙 _ := by
    have : d = biprod.fst ≫ c₁ + biprod.snd ≫ c₂ := biprod.desc_eq
    calc r₁ ≫ c₁ + r₂ ≫ c₂ = inv d ≫ (biprod.fst ≫ c₁ + biprod.snd ≫ c₂) := by
          simp [r₁, r₂, Preadditive.comp_add]
      _ = 𝟙 _ := by rw [← this]; simp
  have hx : ∀ x : HK R L F n, x = HK.pull R r₁ F n (HK.pull R c₁ F n x) + HK.pull R r₂ F n (HK.pull R c₂ F n x) := by
    intro x
    rw [← pl_comp, ← pl_comp, ← pl_add, hs, pl_id]
  constructor
  · intro x y h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only at h1 h2
    rw [hx x, hx y, h1, h2]
  · rintro ⟨a, b⟩
    refine ⟨HK.pull R r₁ F n a + HK.pull R r₂ F n b, Prod.ext ?_ ?_⟩
    · simp only [map_add]
      rw [← pl_comp, ← pl_comp, h11, h12, pl_id, pl_zero, add_zero]
    · simp only [map_add]
      rw [← pl_comp, ← pl_comp, h21, h22, pl_id, pl_zero, zero_add]

private theorem sec_nat {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  ConcreteCategory.congr_hom (φ.hom.naturality g.op).symm x

private theorem sec_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

private theorem sec_id {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := rfl

private theorem res_comp {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (h ≫ g) x = Sec.res h (Sec.res g x) := by
  simp [Sec.res]

private theorem sec_bij (F : Shv R) (A B : Type) [CommRing A] [CommRing B] :
    Function.Bijective fun s : Sec F (Spec (CommRingCat.of (A × B))) =>
      ((Sec.res (Spec.map (CommRingCat.ofHom (RingHom.fst A B))) s : Sec F (Spec (CommRingCat.of A))),
       (Sec.res (Spec.map (CommRingCat.ofHom (RingHom.snd A B))) s : Sec F (Spec (CommRingCat.of B)))) := by
  let G : Scheme.{0}ᵒᵖ ⥤ Type 1 := F.obj ⋙ forget _
  have hG : Presieve.IsSheaf Scheme.zariskiTopology G :=
    Presieve.isSheaf_of_le _ Scheme.zariskiTopology_le_etaleTopology
      ((isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose _ (forget _)).obj F).cond)
  have : PreservesLimitsOfShape (Discrete WalkingPair) G :=
    preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hG
  let a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of (A × B)) := Spec.map (CommRingCat.ofHom (RingHom.fst A B))
  let b : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (A × B)) := Spec.map (CommRingCat.ofHom (RingHom.snd A B))
  have ea : coprod.inl ≫ coprodSpec A B = a := coprodSpec_inl A B
  have eb : coprod.inr ≫ coprodSpec A B = b := coprodSpec_inr A B
  have hop : IsLimit (BinaryFan.mk a.op b.op) := by
    refine BinaryFan.IsLimit.mk _ (fun f g => (inv (coprodSpec A B) ≫ coprod.desc f.unop g.unop).op) ?_ ?_ ?_
    · intro T f g
      apply Quiver.Hom.unop_inj
      change a ≫ inv (coprodSpec A B) ≫ coprod.desc f.unop g.unop = f.unop
      rw [← ea, Category.assoc, IsIso.hom_inv_id_assoc, coprod.inl_desc]
    · intro T f g
      apply Quiver.Hom.unop_inj
      change b ≫ inv (coprodSpec A B) ≫ coprod.desc f.unop g.unop = g.unop
      rw [← eb, Category.assoc, IsIso.hom_inv_id_assoc, coprod.inr_desc]
    · intro T f g m h₁ h₂
      apply Quiver.Hom.unop_inj
      have h₁' : a ≫ m.unop = f.unop := congrArg Quiver.Hom.unop h₁
      have h₂' : b ≫ m.unop = g.unop := congrArg Quiver.Hom.unop h₂
      rw [Quiver.Hom.unop_op, IsIso.eq_inv_comp]
      apply coprod.hom_ext
      · rw [coprod.inl_desc, reassoc_of% ea]
        exact h₁'
      · rw [coprod.inr_desc, reassoc_of% eb]
        exact h₂'
  have hl := (isLimitMapConeBinaryFanEquiv G a.op b.op) (isLimitOfPreserves G hop)
  let e := hl.conePointUniqueUpToIso (Types.binaryProductLimit _ _)
  have he := (isIso_iff_bijective e.hom).1 inferInstance
  exact he

private theorem free_iso {X Y Z : Scheme.{0}} (a : Y ⟶ X) (b : Z ⟶ X)
    (hb : ∀ F : Shv R, Function.Bijective fun s : Sec F X => ((Sec.res a s : Sec F Y), (Sec.res b s : Sec F Z))) :
    IsIso (biprod.desc ((free R).map (yoneda.map a)) ((free R).map (yoneda.map b))) := by
  let P₁ : PSh := yoneda.obj Y
  let P₂ : PSh := yoneda.obj Z
  let Q : PSh := yoneda.obj X
  let a' : (free R).obj P₁ ⟶ (free R).obj Q := (free R).map (yoneda.map a)
  let b' : (free R).obj P₂ ⟶ (free R).obj Q := (free R).map (yoneda.map b)
  let T : Shv R := (free R).obj P₁ ⊞ (free R).obj P₂
  let g₁ : Sec ((free R).obj P₁) Y := freeGen R P₁ _ (𝟙 _)
  let g₂ : Sec ((free R).obj P₂) Z := freeGen R P₂ _ (𝟙 _)
  let gQ : Sec ((free R).obj Q) X := freeGen R Q _ (𝟙 _)
  obtain ⟨s, hs⟩ := (hb T).2 (Sec.map biprod.inl g₁, Sec.map biprod.inr g₂)
  have hs₁ : Sec.res a s = Sec.map biprod.inl g₁ := congrArg Prod.fst hs
  have hs₂ : Sec.res b s = Sec.map biprod.inr g₂ := congrArg Prod.snd hs
  obtain ⟨hex, hext, hres, hmap⟩ := free_hom_sections R Q T
  obtain ⟨φ, hφ⟩ := hex (fun U x => Sec.res x s) (fun V U g x => (res_comp g x s).symm)
  have gen₁ : ∀ (U : Scheme.{0}) (x : U ⟶ Y), freeGen R P₁ U x = Sec.res x g₁ := by
    intro U x
    refine Eq.trans ?_ ((free_hom_sections R P₁ T).2.2.1 U _ x (𝟙 _)).symm
    congr 1
  have gen₂ : ∀ (U : Scheme.{0}) (x : U ⟶ Z), freeGen R P₂ U x = Sec.res x g₂ := by
    intro U x
    refine Eq.trans ?_ ((free_hom_sections R P₂ T).2.2.1 U _ x (𝟙 _)).symm
    congr 1
  have genQ : ∀ (U : Scheme.{0}) (x : U ⟶ X), freeGen R Q U x = Sec.res x gQ := by
    intro U x
    refine Eq.trans ?_ ((free_hom_sections R Q T).2.2.1 U _ x (𝟙 _)).symm
    congr 1
  have ma : ∀ (U : Scheme.{0}) (x : U ⟶ Y), Sec.map a' (freeGen R P₁ U x) = freeGen R Q U (x ≫ a) :=
    fun U x => (free_hom_sections R P₁ T).2.2.2 Q (yoneda.map a) U x
  have mb : ∀ (U : Scheme.{0}) (x : U ⟶ Z), Sec.map b' (freeGen R P₂ U x) = freeGen R Q U (x ≫ b) :=
    fun U x => (free_hom_sections R P₂ T).2.2.2 Q (yoneda.map b) U x
  have hdφ₁ : a' ≫ φ = biprod.inl := by
    refine (free_hom_sections R P₁ T).2.1 _ _ fun U x => ?_
    rw [sec_comp, ma, hφ, res_comp, hs₁, sec_nat, ← gen₁]
  have hdφ₂ : b' ≫ φ = biprod.inr := by
    refine (free_hom_sections R P₂ T).2.1 _ _ fun U x => ?_
    rw [sec_comp, mb, hφ, res_comp, hs₂, sec_nat, ← gen₂]
  have hsQ : Sec.map (biprod.desc a' b') s = gQ := by
    refine (hb ((free R).obj Q)).1 (Prod.ext ?_ ?_)
    · change Sec.res a (Sec.map (biprod.desc a' b') s) = Sec.res a gQ
      rw [sec_nat, hs₁, ← sec_comp, biprod.inl_desc, ← genQ, ma]
      rfl
    · change Sec.res b (Sec.map (biprod.desc a' b') s) = Sec.res b gQ
      rw [sec_nat, hs₂, ← sec_comp, biprod.inr_desc, ← genQ, mb]
      rfl
  refine ⟨φ, ?_, ?_⟩
  · apply biprod.hom_ext'
    · rw [biprod.inl_desc_assoc, Category.comp_id]
      exact hdφ₁
    · rw [biprod.inr_desc_assoc, Category.comp_id]
      exact hdφ₂
  · refine (free_hom_sections R Q ((free R).obj Q)).2.1 _ _ fun U x => ?_
    change Sec.map (biprod.desc a' b') (Sec.map φ (freeGen R Q U x)) = freeGen R Q U x
    rw [hφ, ← sec_nat, hsQ, genQ]

end UpperTheory.SectionRestriction

theorem UpperTheory.twistedCohomology_specProd_bijective_prod :
    ∀ (q : ℕ) (A B : Type) [CommRing A] [CommRing B] (n i : ℤ), Function.Bijective fun x : Ht q (sp (A × B)) n i => (pull _ (spMap (RingHom.fst A B)) (tw q i) n x, pull _ (spMap (RingHom.snd A B)) (tw q i) n x) := by
  intro q A B _ _ n i
  have h2 := GlobalTheory.EtC.chains_disc_biprod_isIso (ZMod q) _ _ (UpperTheory.SectionRestriction.free_iso _ _ fun F => UpperTheory.SectionRestriction.sec_bij F A B)
  exact UpperTheory.SectionRestriction.split_bij ((chains (ZMod q)).map (spMap (RingHom.fst A B)))
    ((chains (ZMod q)).map (spMap (RingHom.snd A B))) h2 (tw q i) n
