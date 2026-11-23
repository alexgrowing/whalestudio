import Development.EtaleCohomology.EtaleSheaves.LeafUnitActPfAug

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafActSheafPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafUnitActPfAug LateralTheory.E.LeafUnitPairPf LateralTheory.E.LeafUnitActPf

section Basic
variable {R : Type} [CommRing R]

theorem res_comp (F : Shv R) {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res k (Sec.res g y) = Sec.res (k ≫ g) y := by
  change (F.obj.map k.op).hom ((F.obj.map g.op).hom y) = (F.obj.map (k ≫ g).op).hom y
  rw [op_comp, Functor.map_comp]
  rfl

theorem res_smul (F : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) (c : ULift.{1} R) (y : Sec F U) :
    Sec.res g (c • y) = c • Sec.res g y := map_smul (F.obj.map g.op).hom c y

theorem res_add (F : Shv R) {V U : Scheme.{0}} (g : V ⟶ U) (y z : Sec F U) :
    Sec.res g (y + z) = Sec.res g y + Sec.res g z := map_add (F.obj.map g.op).hom y z

theorem map_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.res g (Sec.map φ y) = Sec.map φ (Sec.res g y) := by
  have h := congrArg (fun f => f.hom y) (φ.hom.naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

theorem map_smul' {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (c : ULift.{1} R) (y : Sec F U) :
    Sec.map φ (c • y) = c • Sec.map φ y := map_smul (φ.hom.app (op U)).hom c y

theorem sec_res (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)) {V U : Scheme.{0}} (g : V ⟶ U) (x : M.obj Γ(U, ⊤)) :
    Sec.res (F := ofRings R M) g (ofRings.sec M U x) = ofRings.sec M V ((M.map g.appTop).hom x) := by
  have h := congrArg (fun f => f.hom x) ((toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ M)).naturality g.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

theorem loc_and {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (hP : Loc U P) (hQ : Loc U Q) :
    Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, h1⟩ := hP
  obtain ⟨T, hT, h2⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT, fun V g hg => ⟨h1 V g hg.1, h2 V g hg.2⟩⟩

theorem glue (F : Shv R) {U : Scheme.{0}} (S : Sieve U) (hS : S ∈ Scheme.etaleTopology.{0} U)
    (s : ∀ ⦃V : Scheme.{0}⦄ (g : V ⟶ U), S.arrows g → Sec F V)
    (hs : ∀ ⦃V W : Scheme.{0}⦄ (g : V ⟶ U) (hg : S.arrows g) (h : W ⟶ V),
      Sec.res h (s g hg) = s (h ≫ g) (S.downward_closed hg h)) :
    ∃ t : Sec F U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g), Sec.res g t = s g hg := by
  have hsh := F.property (ModuleCat.of (ULift.{1} R) (ULift.{1} R)) S hS
  let x : Presieve.FamilyOfElements (F.obj ⋙ coyoneda.obj (op (ModuleCat.of (ULift.{1} R) (ULift.{1} R)))) S.arrows :=
    fun V g hg => ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ (s g hg))
  have hx : x.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro V W g h hg
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    change (LinearMap.toSpanSingleton _ _ (s (h ≫ g) _)) 1 = (F.obj.map h.op).hom ((LinearMap.toSpanSingleton _ _ (s g hg)) 1)
    simp only [LinearMap.toSpanSingleton_apply, one_smul]
    exact (hs g hg h).symm
  obtain ⟨t, ht, -⟩ := hsh x hx
  refine ⟨t.hom 1, fun V g hg => ?_⟩
  have h1 := congrArg (fun f => f.hom (1 : ULift.{1} R)) (ht g hg)
  change (F.obj.map g.op).hom (t.hom 1) = (LinearMap.toSpanSingleton _ _ (s g hg)) 1 at h1
  simpa [LinearMap.toSpanSingleton_apply] using h1

end Basic

variable {q : ℕ}

theorem etaleTwistZero_sheafifiedSection_of_ring_restrict {V U : Scheme.{0}} (g : V ⟶ U) (x : (twF q 0).obj Γ(U, ⊤)) :
    Sec.res (F := tw q 0) g (ofRings.sec (twF q 0) U x) = ofRings.sec (twF q 0) V (((twF q 0).map g.appTop).hom x) :=
  sec_res (twF q 0) g x

theorem etaleTwistZero_sheafifiedSection_of_ring_add {U : Scheme.{0}} (x y : (twF q 0).obj Γ(U, ⊤)) :
    ofRings.sec (twF q 0) U (x + y) = ofRings.sec (twF q 0) U x + ofRings.sec (twF q 0) U y := by
  unfold ofRings.sec; exact map_add _ x y

theorem sec_smul0 {U : Scheme.{0}} (c : ULift.{1} (ZMod q)) (x : (twF q 0).obj Γ(U, ⊤)) :
    ofRings.sec (twF q 0) U (c • x) = c • ofRings.sec (twF q 0) U x := by
  unfold ofRings.sec; exact map_smul _ c x

theorem etaleTwistZero_augmentation_map_add {V : Scheme.{0}} (x y : (twF q 0).obj Γ(V, ⊤)) :
    aug q Γ(V, ⊤) (x + y) = aug q Γ(V, ⊤) x + aug q Γ(V, ⊤) y := map_add _ _ _

theorem aug_smul0 {V : Scheme.{0}} (c : ULift.{1} (ZMod q)) (x : (twF q 0).obj Γ(V, ⊤)) :
    aug q Γ(V, ⊤) (c • x) = c • aug q Γ(V, ⊤) x := map_smul _ _ _

theorem aug_smul_eq (F : Shv (ZMod q)) {W : Scheme.{0}} (x y : (twF q 0).obj Γ(W, ⊤))
    (h : ofRings.sec (twF q 0) W x = ofRings.sec (twF q 0) W y) (z : Sec F W) :
    aug q Γ(W, ⊤) x • z = aug q Γ(W, ⊤) y • z := by
  apply sec_eq_of_loc
  obtain ⟨S, hS, hP⟩ := etale_tate_twist_zero_sections_eq_locally_of_sheafified_eq q x y h
  refine ⟨S, hS, fun V g hg => ?_⟩
  beta_reduce
  rw [res_smul, res_smul, ← aug_map q g.appTop x, ← aug_map q g.appTop y, hP V g hg]

def Good (F : Shv (ZMod q)) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b t : Sec F U) : Prop :=
  ∀ (V : Scheme.{0}) (g : V ⟶ U) (x : (twF q 0).obj Γ(V, ⊤)), Sec.res g a = ofRings.sec (twF q 0) V x →
    Sec.res g t = aug q Γ(V, ⊤) x • Sec.res g b

theorem good_of_loc (F : Shv (ZMod q)) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b t : Sec F U)
    (h : Loc U fun V g => ∃ x : (twF q 0).obj Γ(V, ⊤), Sec.res g a = ofRings.sec (twF q 0) V x ∧
      Sec.res g t = aug q Γ(V, ⊤) x • Sec.res g b) : Good F a b t := by
  intro V g x hx
  obtain ⟨S, hS, hP⟩ := h
  refine sec_eq_of_loc F _ _ ⟨S.pullback g, Scheme.etaleTopology.pullback_stable g hS, fun W k hk => ?_⟩
  obtain ⟨x', hx', ht⟩ := hP W (k ≫ g) hk
  rw [res_comp, ht, res_smul, res_comp, ← aug_map q k.appTop x]
  apply aug_smul_eq
  rw [← hx', ← res_comp, hx, etaleTwistZero_sheafifiedSection_of_ring_restrict]

theorem good_unique (F : Shv (ZMod q)) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b t₁ t₂ : Sec F U)
    (h₁ : Good F a b t₁) (h₂ : Good F a b t₂) : t₁ = t₂ := by
  obtain ⟨S, hS, hP⟩ := etale_tate_twist_zero_section_locally_lifts_to_ring_value q a
  refine sec_eq_of_loc F t₁ t₂ ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := hP V g hg
  rw [h₁ V g x hx, h₂ V g x hx]

theorem good_exists (F : Shv (ZMod q)) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b : Sec F U) : ∃ t, Good F a b t := by
  obtain ⟨S, hS, hP⟩ := etale_tate_twist_zero_section_locally_lifts_to_ring_value q a
  have key : ∀ {V W : Scheme.{0}} (g : V ⟶ U) (h : W ⟶ V) (x : (twF q 0).obj Γ(V, ⊤)) (x' : (twF q 0).obj Γ(W, ⊤)),
      Sec.res g a = ofRings.sec (twF q 0) V x → Sec.res (h ≫ g) a = ofRings.sec (twF q 0) W x' →
      Sec.res h (aug q Γ(V, ⊤) x • Sec.res g b) = aug q Γ(W, ⊤) x' • Sec.res (h ≫ g) b := by
    intro V W g h x x' e1 e2
    rw [res_smul, res_comp, ← aug_map q h.appTop x]
    apply aug_smul_eq
    rw [← etaleTwistZero_sheafifiedSection_of_ring_restrict, ← e1, res_comp, e2]
  obtain ⟨t, ht⟩ := glue F S hS (fun V g hg => aug q Γ(V, ⊤) (hP V g hg).choose • Sec.res g b)
    (fun V W g hg h => key g h _ _ (hP V g hg).choose_spec (hP W (h ≫ g) (S.downward_closed hg h)).choose_spec)
  exact ⟨t, good_of_loc F a b t ⟨S, hS, fun V g hg => ⟨_, (hP V g hg).choose_spec, ht V g hg⟩⟩⟩

def act (F : Shv (ZMod q)) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b : Sec F U) : Sec F U := (good_exists F a b).choose

theorem act_good (F : Shv (ZMod q)) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b : Sec F U) : Good F a b (act F a b) :=
  (good_exists F a b).choose_spec

theorem act_add_left (F : Shv (ZMod q)) {U : Scheme.{0}} (a₁ a₂ : Sec (tw q 0) U) (b : Sec F U) :
    act F (a₁ + a₂) b = act F a₁ b + act F a₂ b := by
  refine good_unique F _ b _ _ (act_good F _ b) (good_of_loc F _ b _ ?_)
  obtain ⟨S, hS, hP⟩ := loc_and (etale_tate_twist_zero_section_locally_lifts_to_ring_value q a₁) (etale_tate_twist_zero_section_locally_lifts_to_ring_value q a₂)
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨⟨x₁, h₁⟩, ⟨x₂, h₂⟩⟩ := hP V g hg
  refine ⟨x₁ + x₂, by rw [res_add, h₁, h₂]; exact (etaleTwistZero_sheafifiedSection_of_ring_add x₁ x₂).symm, ?_⟩
  rw [res_add, act_good F a₁ b V g x₁ h₁, act_good F a₂ b V g x₂ h₂, etaleTwistZero_augmentation_map_add, add_smul]

theorem act_smul_left (F : Shv (ZMod q)) {U : Scheme.{0}} (c : ULift.{1} (ZMod q)) (a : Sec (tw q 0) U) (b : Sec F U) :
    act F (c • a) b = c • act F a b := by
  refine good_unique F _ b _ _ (act_good F _ b) (good_of_loc F _ b _ ?_)
  obtain ⟨S, hS, hP⟩ := etale_tate_twist_zero_section_locally_lifts_to_ring_value q a
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨x, h⟩ := hP V g hg
  refine ⟨c • x, by rw [res_smul, h]; exact (sec_smul0 c x).symm, ?_⟩
  rw [res_smul, act_good F a b V g x h, aug_smul0, smul_eq_mul, mul_smul]

theorem act_add_right (F : Shv (ZMod q)) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b₁ b₂ : Sec F U) :
    act F a (b₁ + b₂) = act F a b₁ + act F a b₂ := by
  refine good_unique F a _ _ _ (act_good F a _) (fun V g x hx => ?_)
  rw [res_add, res_add, act_good F a b₁ V g x hx, act_good F a b₂ V g x hx, smul_add]

theorem act_smul_right (F : Shv (ZMod q)) {U : Scheme.{0}} (c : ULift.{1} (ZMod q)) (a : Sec (tw q 0) U) (b : Sec F U) :
    act F a (c • b) = c • act F a b := by
  refine good_unique F a _ _ _ (act_good F a _) (fun V g x hx => ?_)
  rw [res_smul, res_smul, act_good F a b V g x hx, smul_comm]

theorem act_res (F : Shv (ZMod q)) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec (tw q 0) U) (b : Sec F U) :
    Sec.res g (act F a b) = act F (Sec.res g a) (Sec.res g b) := by
  refine good_unique F _ _ _ _ (fun W k x hx => ?_) (act_good F _ _)
  rw [res_comp, res_comp]
  exact act_good F a b W (k ≫ g) x (by rw [← res_comp]; exact hx)

theorem act_map {F G : Shv (ZMod q)} (φ : F ⟶ G) {U : Scheme.{0}} (a : Sec (tw q 0) U) (b : Sec F U) :
    Sec.map φ (act F a b) = act G a (Sec.map φ b) := by
  refine good_unique G a _ _ _ (fun V g x hx => ?_) (act_good G a _)
  rw [map_res, act_good F a b V g x hx, map_smul', map_res]

theorem act_gen (F : Shv (ZMod q)) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (b : Sec F U) : act F (twGen 0 ζ) b = b := by
  refine good_unique F _ b _ _ (act_good F _ b) (fun V g x hx => ?_)
  let y : (twF q 0).obj Γ(U, ⊤) := Submodule.Quotient.mk (Finsupp.single ζ 1)
  have e : aug q Γ(V, ⊤) (((twF q 0).map g.appTop).hom y) = 1 := (aug_map q g.appTop y).trans (aug_mk_single q ζ)
  have hs : ofRings.sec (twF q 0) V (((twF q 0).map g.appTop).hom y) = ofRings.sec (twF q 0) V x := by
    rw [← hx]; exact (etaleTwistZero_sheafifiedSection_of_ring_restrict g y).symm
  exact (one_smul _ _).symm.trans ((congrArg (· • Sec.res g b) e).symm.trans (aug_smul_eq F _ x hs _))

theorem LeafActSheaf_of : LeafActSheaf := by
  intro q _
  refine ⟨fun F U => LinearMap.mk₂ (ULift.{1} (ZMod q)) (fun a b => act F a b)
    (act_add_left F) (act_smul_left F) (act_add_right F) (act_smul_right F), ?_, ?_, ?_⟩
  · intro F V U g a b
    exact act_res F g a b
  · intro F G φ U a b
    exact act_map φ a b
  · intro F U ζ b
    exact act_gen F ζ b

end LateralTheory.E.LeafActSheafPf
