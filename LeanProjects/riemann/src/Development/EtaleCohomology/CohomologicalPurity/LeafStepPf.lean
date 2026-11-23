import Development.EtaleCohomology.CohomologicalPurity.LeafFlqPf
import Development.EtaleCohomology.KummerTheory.GluePf
import Development.EtaleCohomology.KummerTheory.FlasquePf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl.Flq.StepPf

variable {R : Type} [CommRing R]

theorem res_comp {G : Shv R} {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (x : Sec G C) :
    Sec.res (f ≫ g) x = Sec.res f (Sec.res g x) := by
  show (G.obj.map (f ≫ g).op).hom x = (G.obj.map f.op).hom ((G.obj.map g.op).hom x)
  rw [op_comp, Functor.map_comp]; rfl

theorem res_sub {G : Shv R} {A B : Scheme.{0}} (f : A ⟶ B) (x y : Sec G B) :
    Sec.res f (x - y) = Sec.res f x - Sec.res f y := map_sub (G.obj.map f.op).hom x y

theorem map_sub' {F G : Shv R} (φ : F ⟶ G) {A : Scheme.{0}} (x y : Sec F A) :
    Sec.map φ (x - y) = Sec.map φ x - Sec.map φ y := map_sub (φ.hom.app (op A)).hom x y

theorem map_zero' {F G : Shv R} (φ : F ⟶ G) {A : Scheme.{0}} : Sec.map φ (0 : Sec F A) = 0 :=
  map_zero (φ.hom.app (op A)).hom

theorem map_comp' {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {A : Scheme.{0}} (x : Sec F A) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem map_res {F G : Shv R} (φ : F ⟶ G) {A B : Scheme.{0}} (f : A ⟶ B) (x : Sec F B) :
    Sec.map φ (Sec.res f x) = Sec.res f (Sec.map φ x) := by
  show (φ.hom.app (op A)).hom ((F.obj.map f.op).hom x) = (G.obj.map f.op).hom ((φ.hom.app (op B)).hom x)
  exact congrArg (fun m => ModuleCat.Hom.hom m x) (φ.hom.naturality f.op)

theorem van_rs {G : Shv R} {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ W) (b : Sec G W.toScheme)
    (hb : Sec.res (W.ι ⁻¹ᵁ U).ι b = 0) : Sec.res (V.ι ⁻¹ᵁ U).ι (rs h b) = 0 := by
  have e : V.ι ⁻¹ᵁ U ≤ (X.homOfLE h) ⁻¹ᵁ (W.ι ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι]
  have hc : (V.ι ⁻¹ᵁ U).ι ≫ X.homOfLE h = (X.homOfLE h).resLE (W.ι ⁻¹ᵁ U) (V.ι ⁻¹ᵁ U) e ≫ (W.ι ⁻¹ᵁ U).ι :=
    (Scheme.Hom.resLE_comp_ι _ e).symm
  show Sec.res (V.ι ⁻¹ᵁ U).ι (Sec.res (X.homOfLE h) b) = 0
  rw [← res_comp, hc, res_comp, hb]
  exact map_zero _

theorem rs_rs {G : Shv R} {X : Scheme.{0}} {T V W : X.Opens} (h : V ≤ W) (h' : T ≤ V) (a : Sec G W.toScheme) :
    rs h' (rs h a) = rs (h'.trans h) a := (LeafRs_of R G X T V W h h' a a).2

def LeafSep : Prop := ∀ (R : Type) [CommRing R] (G : Shv R) (X : Scheme.{0}) (W : X.Opens) (s : Sec G W.toScheme),
  (∀ x ∈ W, ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ rs h s = 0) → s = 0

def LeafSNloc : Prop := ∀ (R : Type) [CommRing R] (G : Shv R) (X : Scheme.{0}) (U W : X.Opens) (c : Sec G W.toScheme),
  (∀ x ∈ W, ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ Sec.res (V.ι ⁻¹ᵁ U).ι (rs h c) = 0) → Sec.res (W.ι ⁻¹ᵁ U).ι c = 0

def LeafSNext : Prop := ∀ (R : Type) [CommRing R] (G : Shv R) [Injective G] (X : Scheme.{0}) (U V W : X.Opens)
  (h : V ≤ W) (c : Sec G V.toScheme), Sec.res (V.ι ⁻¹ᵁ U).ι c = 0 →
  ∃ c' : Sec G W.toScheme, Sec.res (W.ι ⁻¹ᵁ U).ι c' = 0 ∧ rs h c' = c

end LateralTheory.CohomologicalPurity.Cl.Flq.StepPf

namespace LateralTheory.CohomologicalPurity.Cl.Flq.StepPf

variable {R : Type} [CommRing R]

theorem map_rs {F G : Shv R} (φ : F ⟶ G) {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) (x : Sec F W.toScheme) :
    Sec.map φ (rs h x) = rs h (Sec.map φ x) := map_res _ _ _

theorem rs_sub {G : Shv R} {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) (x y : Sec G W.toScheme) :
    rs h (x - y) = rs h x - rs h y := res_sub _ _ _

def BdG (K : Cx R) {X : Scheme.{0}} (U : X.Opens) (n : ℤ) (W : X.Opens) : AddSubgroup (Sec (K.X n) W.toScheme) :=
  (((K.X (n - 1)).obj.map (W.ι ⁻¹ᵁ U).ι.op).hom.toAddMonoidHom.ker).map
    ((K.d (n - 1) n).hom.app (op W.toScheme)).hom.toAddMonoidHom

theorem mem_BdG {K : Cx R} {X : Scheme.{0}} {U : X.Opens} {n : ℤ} {W : X.Opens} (a : Sec (K.X n) W.toScheme) :
    a ∈ BdG K U n W ↔ Bd K (W.ι ⁻¹ᵁ U) n a := by
  constructor
  · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, rfl⟩

theorem bd_of_BN {K : Cx R} {X : Scheme.{0}} {U : X.Opens} {n : ℤ} {W : X.Opens} {a : Sec (K.X n) W.toScheme}
    (ha : a ∈ BN K U n W) : Bd K (W.ι ⁻¹ᵁ U) n a :=
  (mem_BdG a).1 ((AddSubgroup.closure_le _).2 (fun b hb => (mem_BdG b).2 hb) ha)

theorem BN_of_bd {K : Cx R} {X : Scheme.{0}} {U : X.Opens} {n : ℤ} {W : X.Opens} {a : Sec (K.X n) W.toScheme}
    (ha : Bd K (W.ι ⁻¹ᵁ U) n a) : a ∈ BN K U n W := AddSubgroup.subset_closure ha

theorem bd_rs {K : Cx R} {X : Scheme.{0}} {U V W : X.Opens} {n : ℤ} (h : V ≤ W) {a : Sec (K.X n) W.toScheme}
    (ha : Bd K (W.ι ⁻¹ᵁ U) n a) : Bd K (V.ι ⁻¹ᵁ U) n (rs h a) := by
  obtain ⟨b, hb, rfl⟩ := ha
  exact ⟨rs h b, van_rs h b hb, map_res _ _ _⟩

theorem BN_rs {K : Cx R} {X : Scheme.{0}} {U V W : X.Opens} {n : ℤ} (h : V ≤ W) :
    ∀ a ∈ BN K U n W, rs h a ∈ BN K U n V := by
  intro a ha
  have : BN K U n W ≤ (BN K U n V).comap ((K.X n).obj.map (X.homOfLE h).op).hom.toAddMonoidHom :=
    (AddSubgroup.closure_le _).2 fun b hb => BN_of_bd (bd_rs h hb)
  exact this ha

theorem BN_ext (hE : LeafSNext) {K : Cx R} (hinj : ∀ s, Injective (K.X s)) {X : Scheme.{0}} {U V W : X.Opens} {n : ℤ}
    (h : V ≤ W) : ∀ a ∈ BN K U n V, ∃ b ∈ BN K U n W, rs h b = a := by
  intro a ha
  have := hinj (n - 1)
  have : BN K U n V ≤ (BN K U n W).map ((K.X n).obj.map (X.homOfLE h).op).hom.toAddMonoidHom :=
    (AddSubgroup.closure_le _).2 fun b hb => by
      obtain ⟨c, hc, rfl⟩ := hb
      obtain ⟨c', hc', hrs⟩ := hE R (K.X (n - 1)) X U V W h c hc
      refine ⟨Sec.map (K.d (n - 1) n) c', BN_of_bd ⟨c', hc', rfl⟩, ?_⟩
      show rs h (Sec.map (K.d (n - 1) n) c') = _
      rw [← map_rs, hrs]
  obtain ⟨b, hb, e⟩ := this ha
  exact ⟨b, hb, e⟩

theorem d_shift {K : Cx R} {n : ℤ} {A : Scheme.{0}} (x : Sec (K.X (n - 1)) A) :
    Sec.map (K.d (n - 1) (n - 1 + 1)) x = 0 ↔ Sec.map (K.d (n - 1) n) x = 0 := by
  have e : n - 1 + 1 = n := by ring
  constructor
  · intro h0; rw [← K.d_comp_XIsoOfEq_hom e, map_comp', h0, map_zero']
  · intro h0; rw [← K.d_comp_XIsoOfEq_inv e, map_comp', h0, map_zero']

theorem BN_loc (hZ : LateralTheory.CohomologicalPurity.Cl.LeafZorn) (hSep : LeafSep) (hL : LeafSNloc) {K : Cx R} {X : Scheme.{0}}
    {U : X.Opens} {n : ℤ} (hOK : OK (ZN K U (n - 1))) (W : X.Opens) (a : Sec (K.X n) W.toScheme)
    (H : ∀ x ∈ W, ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ rs h a ∈ BN K U n V) : a ∈ BN K U n W := by
  have H' : ∀ k : {x : X // x ∈ W}, ∃ (V : X.Opens) (h : V ≤ W), k.1 ∈ V ∧ ∃ b : Sec (K.X (n - 1)) V.toScheme,
      Sec.res (V.ι ⁻¹ᵁ U).ι b = 0 ∧ Sec.map (K.d (n - 1) n) b = rs h a := by
    intro k
    obtain ⟨V, h, hx, hb⟩ := H k.1 k.2
    obtain ⟨b, hb0, hbd⟩ := bd_of_BN hb
    exact ⟨V, h, hx, b, hb0, hbd⟩
  choose V h hx b hb0 hbd using H'
  obtain ⟨c, hc⟩ := hZ R (K.X (n - 1)) X (ZN K U (n - 1)) hOK.1 hOK.2.1 hOK.2.2 W _ V h b
    (fun x hxW => ⟨⟨x, hxW⟩, hx _⟩) (fun k l => by
      refine (mem_Zc _).2 ⟨?_, ?_⟩
      · rw [res_sub, van_rs _ _ (hb0 k), van_rs _ _ (hb0 l), sub_zero]
      · rw [d_shift, map_sub', map_rs, map_rs, hbd, hbd, rs_rs, rs_rs]
        exact sub_self _)
  have hvan : Sec.res (W.ι ⁻¹ᵁ U).ι c = 0 := hL R (K.X (n - 1)) X U W c fun x hxW => ⟨V ⟨x, hxW⟩, h _, hx _, by
      have := ((mem_Zc _).1 (hc ⟨x, hxW⟩)).1
      rw [res_sub, hb0, sub_zero] at this
      exact this⟩
  have hd : Sec.map (K.d (n - 1) n) c = a := by
    rw [← sub_eq_zero]
    apply hSep R (K.X n) X W
    intro x hxW
    refine ⟨V ⟨x, hxW⟩, h _, hx _, ?_⟩
    have hz := (d_shift _).1 ((mem_Zc _).1 (hc ⟨x, hxW⟩)).2
    rw [map_sub', map_rs, hbd] at hz
    rw [rs_sub]
    exact hz
  exact BN_of_bd ⟨c, hvan, hd⟩

theorem LeafStep_of_parts (hSep : LeafSep) (hL : LeafSNloc) (hE : LeafSNext) : LateralTheory.CohomologicalPurity.Cl.Flq.LeafStep := by
  intro R _ K hZ hinj X U n hOK
  exact ⟨fun V W h a ha => BN_rs h a ha, fun W a H => BN_loc hZ hSep hL hOK W a H,
    fun V W h a ha => BN_ext hE hinj h a ha⟩

end LateralTheory.CohomologicalPurity.Cl.Flq.StepPf

namespace LateralTheory.CohomologicalPurity.Cl.Flq.StepPf

variable {R : Type} [CommRing R]

theorem sep_cover (G : Shv R) {Y : Scheme.{0}} {A : Type} (P : A → Scheme.{0}) (f : ∀ i, P i ⟶ Y)
    [∀ i, IsOpenImmersion (f i)] (hcov : ∀ y, ∃ i, y ∈ Set.range (f i)) (s : Sec G Y)
    (hs : ∀ i, Sec.res (f i) s = 0) : s = 0 := by
  have hG : Presheaf.IsSheaf (Scheme.etaleTopology) (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) :=
    (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget (ModuleCat.{1} (ULift.{1} R)))).1 G.cond
  have hmem : Sieve.generate (Presieve.ofArrows P f) ∈ Scheme.etaleTopology Y := by
    apply Precoverage.generate_mem_toGrothendieck
    refine (Scheme.ofArrows_mem_precoverage_iff (P := (@Etale : MorphismProperty Scheme.{0}))).2
      ⟨fun y => ?_, fun i => ?_⟩
    · obtain ⟨i, hi⟩ := hcov y; exact ⟨i, hi⟩
    · exact (inferInstance : Etale (f i))
  have hS := hG.isSheafFor _ hmem
  rw [← Presieve.isSheafFor_iff_generate, Presieve.isSheafFor_arrows_iff] at hS
  have hc : Presieve.Arrows.Compatible (G.obj ⋙ forget (ModuleCat.{1} (ULift.{1} R))) f
      (fun _ => (0 : Sec G _)) := by
    intro i j Z gi gj _
    change (G.obj.map gi.op).hom 0 = (G.obj.map gj.op).hom 0
    simp
  obtain ⟨t, -, ht⟩ := hS _ hc
  rw [ht s (fun i => hs i), ht 0 (fun i => by change (G.obj.map (f i).op).hom 0 = 0; simp)]

theorem LeafSep_of : LeafSep := by
  intro R _ G X W s H
  choose V h hx hs using H
  apply sep_cover G (fun k : {x : X // x ∈ W} => (V k.1 k.2).toScheme) (fun k => X.homOfLE (h k.1 k.2))
  · intro y
    have hy : W.ι y ∈ W := by
      have : W.ι y ∈ Set.range W.ι := ⟨y, rfl⟩
      rwa [Scheme.Opens.range_ι] at this
    refine ⟨⟨W.ι y, hy⟩, ?_⟩
    have : y ∈ (X.homOfLE (h (W.ι y) hy)).opensRange := by
      rw [Scheme.opensRange_homOfLE]; exact hx _ hy
    exact this
  · intro k; exact hs k.1 k.2

end LateralTheory.CohomologicalPurity.Cl.Flq.StepPf

namespace LateralTheory.CohomologicalPurity.Cl.Flq.StepPf

theorem LeafSNloc_of : LeafSNloc := by
  intro R _ G X U W c H
  choose V h hx hs using H
  have e : ∀ k : {x : X // x ∈ W}, (V k.1 k.2).ι ⁻¹ᵁ U ≤ (X.homOfLE (h k.1 k.2)) ⁻¹ᵁ (W.ι ⁻¹ᵁ U) := fun k => by
    rw [← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι]
  have hI : ∀ k : {x : X // x ∈ W}, IsOpenImmersion ((X.homOfLE (h k.1 k.2)).resLE (W.ι ⁻¹ᵁ U) _ (e k)) :=
    fun k => by
      have : IsOpenImmersion ((X.homOfLE (h k.1 k.2)).resLE (W.ι ⁻¹ᵁ U) _ (e k) ≫ (W.ι ⁻¹ᵁ U).ι) := by
        rw [Scheme.Hom.resLE_comp_ι]; infer_instance
      exact IsOpenImmersion.of_comp _ (W.ι ⁻¹ᵁ U).ι
  apply sep_cover G (fun k : {x : X // x ∈ W} => ((V k.1 k.2).ι ⁻¹ᵁ U).toScheme)
    (fun k => (X.homOfLE (h k.1 k.2)).resLE (W.ι ⁻¹ᵁ U) _ (e k))
  · intro y
    obtain ⟨⟨x, hxW⟩, hyU⟩ := y
    refine ⟨⟨x, hxW⟩, ⟨⟨x, hx x hxW⟩, hyU⟩, ?_⟩
    apply Subtype.ext
    rw [Scheme.Hom.coe_resLE_apply]
    apply Subtype.ext
    exact congr($(X.homOfLE_ι (h x hxW)) ⟨x, hx x hxW⟩)
  · intro k
    rw [← res_comp, Scheme.Hom.resLE_comp_ι, res_comp]
    exact hs k.1 k.2

end LateralTheory.CohomologicalPurity.Cl.Flq.StepPf

namespace LateralTheory.CohomologicalPurity.Cl.Flq.StepPf

theorem res_zero {R : Type} [CommRing R] {G : Shv R} {A B : Scheme.{0}} (f : A ⟶ B) :
    Sec.res f (0 : Sec G B) = 0 := map_zero (G.obj.map f.op).hom

theorem mv_opens {X : Scheme.{0}} (A B : X.Opens) :
    LateralTheory.KummerTheory.ContCut.IsMV (X.homOfLE (inf_le_left : A ⊓ B ≤ A)) (X.homOfLE inf_le_right)
      (X.homOfLE (le_sup_left : A ≤ A ⊔ B)) (X.homOfLE le_sup_right) := by
  refine ⟨inferInstance, inferInstance, isPullback_opens_inf_le _ _, fun y => ?_⟩
  have hy : y.1 ∈ A ⊔ B := y.2
  rcases (TopologicalSpace.Opens.mem_sup.1 hy) with h1 | h1
  · left
    have : y ∈ (X.homOfLE (le_sup_left : A ≤ A ⊔ B)).opensRange := by
      rw [Scheme.opensRange_homOfLE]; exact h1
    exact this
  · right
    have : y ∈ (X.homOfLE (le_sup_right : B ≤ A ⊔ B)).opensRange := by
      rw [Scheme.opensRange_homOfLE]; exact h1
    exact this

theorem LeafSNext_of : LeafSNext := by
  intro R _ G _ X U V W h c hc
  have hT : V ⊔ (W ⊓ U) ≤ W := sup_le h inf_le_left
  have H : Set.range (X.homOfLE (inf_le_left : V ⊓ (W ⊓ U) ≤ V)) ⊆ Set.range (V.ι ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨⟨p, hp⟩, rfl⟩
    rw [Scheme.homOfLE_apply']
    exact hp.2.2
  have hst : Sec.res (X.homOfLE (inf_le_left : V ⊓ (W ⊓ U) ≤ V)) c =
      Sec.res (X.homOfLE (inf_le_right : V ⊓ (W ⊓ U) ≤ W ⊓ U)) (0 : Sec G (W ⊓ U).toScheme) := by
    rw [← IsOpenImmersion.lift_fac (V.ι ⁻¹ᵁ U).ι (X.homOfLE _) H, res_comp, hc, res_zero, res_zero]
  obtain ⟨z, hz1, hz2⟩ := (LateralTheory.KummerTheory.GluePf.Glue_of R G _ _ _ _ (mv_opens V (W ⊓ U))).2 c 0 hst
  obtain ⟨c', hc'⟩ := LateralTheory.KummerTheory.FlasquePf.Flasque_of R G (X.homOfLE hT) z
  have hc'' : Sec.res (X.homOfLE hT) c' = z := hc'
  refine ⟨c', ?_, ?_⟩
  · have H2 : Set.range (W.ι ⁻¹ᵁ U).ι ⊆ Set.range (X.homOfLE (inf_le_left : W ⊓ U ≤ W)) := by
      rw [Scheme.Opens.range_ι]
      intro p hp
      have : p ∈ (X.homOfLE (inf_le_left : W ⊓ U ≤ W)).opensRange := by
        rw [Scheme.opensRange_homOfLE]; exact ⟨p.2, hp⟩
      exact this
    obtain ⟨m, hm⟩ : ∃ m, m ≫ X.homOfLE (inf_le_left : W ⊓ U ≤ W) = (W.ι ⁻¹ᵁ U).ι :=
      ⟨_, IsOpenImmersion.lift_fac _ _ H2⟩
    rw [← hm, res_comp, ← Scheme.homOfLE_homOfLE X (le_sup_right : W ⊓ U ≤ V ⊔ (W ⊓ U)) hT, res_comp, hc'',
      hz2, res_zero]
  · show Sec.res (X.homOfLE h) c' = c
    rw [← Scheme.homOfLE_homOfLE X (le_sup_left : V ≤ V ⊔ (W ⊓ U)) hT, res_comp, hc'', hz1]

theorem LeafStep_of : LateralTheory.CohomologicalPurity.Cl.Flq.LeafStep := LeafStep_of_parts LeafSep_of LeafSNloc_of LeafSNext_of

end LateralTheory.CohomologicalPurity.Cl.Flq.StepPf
