import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsTo

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
open GlobalTheory.VB GlobalTheory.FlagLocal
open GlobalTheory.QCoh (pullbackSections res_pullbackSections pullbackSections_res pullback_map_app_pullbackSections app_app)
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)

namespace GlobalTheory.TwoSeq

local notation "pb" => Scheme.Modules.pullback
local notation "pf" => Scheme.Modules.pushforward
local notation "adj" => Scheme.Modules.pullbackPushforwardAdjunction

section Star

variable {X : Scheme.{0}} {ι : Type} {P : X.Modules} {P' Q : ι → X.Modules} (p : ∀ i, P ⟶ Q i) (q : ∀ i, P' i ⟶ Q i)

theorem pi_sections (V : X.Opens) :
    Function.Bijective fun (s : Γ(∏ᶜ P', V)) (i : ι) => (Pi.π P' i).app V s := by
  let E : X.Modules ⥤ Type := Scheme.Modules.toPresheaf X ⋙ (evaluation _ _).obj (Opposite.op V) ⋙ forget Ab
  haveI : PreservesLimit (Discrete.functor P') E := by
    haveI : PreservesLimitsOfShape (Discrete ι) ((evaluation _ _).obj (Opposite.op V) :
      TopCat.Presheaf Ab X ⥤ Ab) := evaluation_preservesLimitsOfShape _
    haveI : PreservesLimitsOfShape (Discrete ι) (forget Ab.{0}) := inferInstance
    haveI : PreservesLimitsOfShape (Discrete ι) (Scheme.Modules.toPresheaf X) := inferInstance
    exact comp_preservesLimit (F := Scheme.Modules.toPresheaf X) (G := (evaluation _ _).obj (Opposite.op V) ⋙ forget Ab)
  have h := isLimitFanMkObjOfIsLimit E P' _ (productIsProduct P')
  let e := h.conePointUniqueUpToIso (Types.productLimitCone fun i => E.obj (P' i)).isLimit
  have hb : Function.Bijective e.hom := (isIso_iff_bijective _).1 inferInstance
  have e' : (fun (s : Γ(∏ᶜ P', V)) (i : ι) => (Pi.π P' i).app V s) = fun s => e.hom s := by
    funext s i
    have := h.conePointUniqueUpToIso_hom_comp (Types.productLimitCone fun i => E.obj (P' i)).isLimit ⟨i⟩
    exact congr($this s).symm
  rw [e']
  exact hb

def star : X.Modules :=
  kernel (biprod.fst ≫ Pi.lift p - biprod.snd ≫ Limits.Pi.map q : P ⊞ ∏ᶜ P' ⟶ ∏ᶜ Q)

def starπ : star p q ⟶ P := kernel.ι _ ≫ biprod.fst

def starπ' (i : ι) : star p q ⟶ P' i := kernel.ι _ ≫ biprod.snd ≫ Pi.π P' i

theorem star_comm (i : ι) : starπ p q ≫ p i = starπ' p q i ≫ q i := by
  have := kernel.condition (biprod.fst ≫ Pi.lift p - biprod.snd ≫ Limits.Pi.map q : P ⊞ ∏ᶜ P' ⟶ ∏ᶜ Q) =≫ Pi.π Q i
  simpa [starπ, starπ', sub_eq_zero] using this

theorem exists_star_lift {F : X.Modules} (f : F ⟶ P) (g : ∀ i, F ⟶ P' i) (h : ∀ i, f ≫ p i = g i ≫ q i) :
    ∃ l : F ⟶ star p q, l ≫ starπ p q = f ∧ ∀ i, l ≫ starπ' p q i = g i :=
  ⟨kernel.lift _ (biprod.lift f (Pi.lift g)) (Pi.hom_ext _ _ fun i => by simp [h i]), by simp [starπ],
    fun i => by simp [starπ']⟩

theorem star_sec_ext {V : X.Opens} {s t : Γ(star p q, V)} (h : (starπ p q).app V s = (starπ p q).app V t)
    (h' : ∀ i, (starπ' p q i).app V s = (starπ' p q i).app V t) : s = t := by
  let κ : star p q ⟶ P ⊞ ∏ᶜ P' := kernel.ι _
  haveI : Mono κ := inferInstanceAs (Mono (kernel.ι _))
  let σ : star p q ⟶ ∏ᶜ P' := κ ≫ biprod.snd
  refine QCoh.injective_app_of_mono κ V ?_
  have h2 : σ.app V s = σ.app V t := (pi_sections V).1 (funext h')
  have e : κ = starπ p q ≫ biprod.inl + σ ≫ biprod.inr := by
    change κ = (κ ≫ biprod.fst) ≫ biprod.inl + (κ ≫ biprod.snd) ≫ biprod.inr
    rw [Category.assoc, Category.assoc, ← Preadditive.comp_add, biprod.total, Category.comp_id]
  have e' : ∀ z, κ.app V z = (biprod.inl : P ⟶ P ⊞ ∏ᶜ P').app V ((starπ p q).app V z) +
      (biprod.inr : _ ⟶ P ⊞ ∏ᶜ P').app V (σ.app V z) := fun z => congr(($e).app V z)
  rw [e', e', h, h2]

theorem exists_star_sec {V : X.Opens} (s : Γ(P, V)) (t : ∀ i, Γ(P' i, V))
    (h : ∀ i, (p i).app V s = (q i).app V (t i)) :
    ∃ z : Γ(star p q, V), (starπ p q).app V z = s ∧ ∀ i, (starπ' p q i).app V z = t i := by
  obtain ⟨t', ht'⟩ := (pi_sections (P' := P') V).2 t
  let y : Γ(P ⊞ ∏ᶜ P', V) := (biprod.inl : P ⟶ _).app V s + (biprod.inr : _ ⟶ P ⊞ _).app V t'
  have h1 : (biprod.fst : _ ⟶ P).app V y = s := by
    simp only [y, map_add, app_app, biprod.inl_fst, biprod.inr_fst]
    exact add_zero s
  have h2 : (biprod.snd : P ⊞ _ ⟶ _).app V y = t' := by
    simp only [y, map_add, app_app, biprod.inl_snd, biprod.inr_snd]
    exact zero_add t'
  have hy : (biprod.fst ≫ Pi.lift p - biprod.snd ≫ Limits.Pi.map q : P ⊞ ∏ᶜ P' ⟶ ∏ᶜ Q).app V y = 0 := by
    refine (pi_sections V).1 (funext fun i => ?_)
    beta_reduce
    rw [map_zero, app_app, Preadditive.sub_comp, Category.assoc, Category.assoc, Pi.lift_π, Limits.Pi.map_π]
    change (p i).app V ((biprod.fst : _ ⟶ P).app V y) -
      (q i).app V ((Pi.π P' i).app V ((biprod.snd : P ⊞ _ ⟶ _).app V y)) = 0
    rw [h1, h2, h i, ← ht', sub_self]
  obtain ⟨z, hz⟩ := (QCoh.exact_app_of_exact_of_mono (ShortComplex.exact_kernel _) V y).1 hy
  refine ⟨z, ?_, fun i => ?_⟩
  · rw [← h1, ← hz]; rfl
  · rw [← ht', ← h2, ← hz]; rfl

theorem bijective_starπ {V : X.Opens} (h : ∀ i, Function.Bijective ((q i).app V)) :
    Function.Bijective ((starπ p q).app V) := by
  refine ⟨fun s t e => star_sec_ext p q e fun i => (h i).1 ?_, fun s => ?_⟩
  · rw [app_app, app_app, ← star_comm, ← app_app, ← app_app, e]
  · choose t ht using fun i => (h i).2 ((p i).app V s)
    obtain ⟨z, hz, -⟩ := exists_star_sec p q s t fun i => (ht i).symm
    exact ⟨z, hz⟩

theorem bijective_starπ' {V : X.Opens} (j : ι) (hj : Function.Bijective ((p j).app V))
    (h : ∀ i, i ≠ j → Function.Bijective ((q i).app V)) : Function.Bijective ((starπ' p q j).app V) := by
  classical
  refine ⟨fun s t e => ?_, fun t => ?_⟩
  · have e' : (starπ p q).app V s = (starπ p q).app V t := hj.1 (by
      rw [app_app, app_app, star_comm, ← app_app, ← app_app, e])
    refine star_sec_ext p q e' fun i => ?_
    by_cases hi : i = j
    · subst hi; exact e
    · refine (h i hi).1 ?_
      rw [app_app, app_app, ← star_comm, ← app_app, ← app_app, e']
  · obtain ⟨s, hs⟩ := hj.2 ((q j).app V t)
    have : ∀ i, ∃ t' : Γ(P' i, V), (q i).app V t' = (p i).app V s ∧ ∀ e : i = j, e ▸ t' = t := fun i => by
      by_cases hi : i = j
      · subst hi; exact ⟨t, hs.symm, fun _ => rfl⟩
      · obtain ⟨t', ht'⟩ := (h i hi).2 ((p i).app V s)
        exact ⟨t', ht', fun e => absurd e hi⟩
    choose t' ht' ht'' using this
    obtain ⟨z, -, hz⟩ := exists_star_sec p q s t' fun i => (ht' i).symm
    exact ⟨z, (hz j).trans (ht'' j rfl)⟩

end Star

section Square

variable {X T T' S : Scheme.{0}} {a : T ⟶ X} {a' : T' ⟶ X} {b : S ⟶ T'} {c : S ⟶ T}

def tr {F : X.Modules} {M : T.Modules} (f : (pb a).obj F ⟶ M) : F ⟶ (pf a).obj M :=
  (adj a).unit.app F ≫ (pf a).map f

theorem tr_injective {F : X.Modules} {M : T.Modules} {f g : (pb a).obj F ⟶ M} (h : tr f = tr g) : f = g :=
  ((adj a).homEquiv _ _).injective (by rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]; exact h)

theorem tr_surjective {F : X.Modules} {M : T.Modules} (g : F ⟶ (pf a).obj M) : ∃ f, tr f = g :=
  ⟨((adj a).homEquiv _ _).symm g, by
    rw [tr, ← Adjunction.homEquiv_unit]; exact Equiv.apply_symm_apply _ _⟩

theorem tr_comp {F : X.Modules} {M M' : T.Modules} (f : (pb a).obj F ⟶ M) (g : M ⟶ M') :
    tr (f ≫ g) = tr f ≫ (pf a).map g := by
  rw [tr, tr, Functor.map_comp, Category.assoc]

theorem comp_tr {F F' : X.Modules} {M : T.Modules} (g : F' ⟶ F) (f : (pb a).obj F ⟶ M) :
    g ≫ tr f = tr ((pb a).map g ≫ f) := by
  rw [tr, tr, Functor.map_comp, ← Category.assoc, ← Category.assoc]
  congr 1
  exact (adj a).unit.naturality g

theorem unit_app (F : X.Modules) (V : X.Opens) (s : Γ(F, V)) :
    ((adj a).unit.app F).app V s = pullbackSections a F le_rfl s :=
  (resM_self (F := (pb a).obj F) (U := a ⁻¹ᵁ V) le_rfl _).symm

theorem tr_app {F : X.Modules} {M : T.Modules} (f : (pb a).obj F ⟶ M) (V : X.Opens) (s : Γ(F, V)) :
    (tr f).app V s = f.app (a ⁻¹ᵁ V) (pullbackSections a F le_rfl s) :=
  congrArg (f.app (a ⁻¹ᵁ V)) (resM_self _ _).symm

theorem isIso_of_tr [IsOpenImmersion a] {F : X.Modules} {M : T.Modules} (f : (pb a).obj F ⟶ M)
    (h : ∀ V ≤ a.opensRange, Function.Bijective ((tr f).app V)) : IsIso f := by
  refine Twist.isIso_of_bijective _ fun W => ?_
  have hV := a.image_le_opensRange W
  rw [← a.preimage_image_eq W]
  refine (Function.Bijective.of_comp_iff _ (bijective_pullbackSections a F hV rfl)).1 ?_
  have := h _ hV
  rwa [show ((tr f).app (a ''ᵁ W) : _ → _) = _ from funext (tr_app f _)] at this

theorem bijective_tr [IsOpenImmersion a] {F : X.Modules} {M : T.Modules} (f : (pb a).obj F ⟶ M) [IsIso f]
    {V : X.Opens} (hV : V ≤ a.opensRange) : Function.Bijective ((tr f).app V) := by
  rw [show ((tr f).app V : _ → _) = _ from funext (tr_app f _)]
  exact (ConcreteCategory.bijective_of_isIso (f.app _)).comp (bijective_pullbackSections a F hV rfl)

variable (a c) in

def resP (M : T.Modules) : (pf a).obj M ⟶ (pf a).obj ((pf c).obj ((pb c).obj M)) :=
  (pf a).map ((adj c).unit.app M)

def resQ (w : b ≫ a' = c ≫ a) {N : T'.Modules} {M : S.Modules} (φ : (pb b).obj N ⟶ M) :
    (pf a').obj N ⟶ (pf a).obj ((pf c).obj M) :=
  (pf a').map (tr φ) ≫ (Scheme.Modules.pushforwardComp b a' ≪≫ Scheme.Modules.pushforwardCongr w ≪≫
    (Scheme.Modules.pushforwardComp c a).symm).hom.app M

theorem sq_le (w : b ≫ a' = c ≫ a) (V : X.Opens) : c ⁻¹ᵁ a ⁻¹ᵁ V ≤ b ⁻¹ᵁ a' ⁻¹ᵁ V := by
  rw [← Scheme.Hom.comp_preimage, ← w, Scheme.Hom.comp_preimage]

theorem pushforwardUnit_app (M : T.Modules) (V : X.Opens) (s : Γ(M, a ⁻¹ᵁ V)) :
    (resP a c M).app V s = pullbackSections c M (le_rfl : c ⁻¹ᵁ a ⁻¹ᵁ V ≤ _) s :=
  unit_app M _ s

theorem resQ_app (w : b ≫ a' = c ≫ a) {N : T'.Modules} {M : S.Modules} (φ : (pb b).obj N ⟶ M) (V : X.Opens)
    (s : Γ(N, a' ⁻¹ᵁ V)) :
    (resQ w φ).app V s = φ.app (c ⁻¹ᵁ a ⁻¹ᵁ V) (pullbackSections b N (sq_le w V) s) := by
  have : (resQ w φ).app V s = resM M (sq_le w V) ((tr φ).app (a' ⁻¹ᵁ V) s) := rfl
  rw [this, tr_app, ← app_resM]
  exact congrArg _ (res_pullbackSections _ _ _ _ _)

theorem pushforwardUnit_naturality {M M' : T.Modules} (f : M ⟶ M') :
    (pf a).map f ≫ resP a c M' = resP a c M ≫ (pf a).map ((pf c).map ((pb c).map f)) := by
  rw [resP, resP, ← Functor.map_comp, ← Functor.map_comp]
  exact congrArg _ ((adj c).unit.naturality f)

theorem map_resQ (w : b ≫ a' = c ≫ a) {N N' : T'.Modules} {M : S.Modules} (g : N' ⟶ N) (φ : (pb b).obj N ⟶ M) :
    (pf a').map g ≫ resQ w φ = resQ w ((pb b).map g ≫ φ) := by
  rw [resQ, resQ, ← comp_tr, Functor.map_comp, Category.assoc]

theorem resQ_map (w : b ≫ a' = c ≫ a) {N : T'.Modules} {M M' : S.Modules} (φ : (pb b).obj N ⟶ M) (f : M ⟶ M') :
    resQ w φ ≫ (pf a).map ((pf c).map f) = resQ w (φ ≫ f) := by
  rw [resQ, resQ, tr_comp, Functor.map_comp, Category.assoc, Category.assoc]
  congr 1
  exact ((Scheme.Modules.pushforwardComp b a' ≪≫ Scheme.Modules.pushforwardCongr w ≪≫
    (Scheme.Modules.pushforwardComp c a).symm).hom.naturality f).symm

theorem unit_resP (w : b ≫ a' = c ≫ a) (F : X.Modules) :
    (adj a).unit.app F ≫ resP a c _ = (adj a').unit.app F ≫ resQ w ((sqIso w).hom.app F) := by
  have key (V : X.Opens) (s : Γ(F, V)) : (resP a c _).app V (((adj a).unit.app F).app V s) =
      (resQ w ((sqIso w).hom.app F)).app V (((adj a').unit.app F).app V s) := by
    refine (pushforwardUnit_app _ V _).trans (Eq.trans ?_ (resQ_app w _ V _).symm)
    rw [unit_app, unit_app]
    exact (Vert.DivPull.pullbackSquare_app w F le_rfl (sq_le w V) le_rfl le_rfl s).symm
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext s
  exact (app_app _ _ V s).symm.trans ((key V s).trans (app_app _ _ V s))

theorem transpose_comp_restriction_eq_iff (w : b ≫ a' = c ≫ a) {F : X.Modules} {M : T.Modules} {N : T'.Modules}
    (φ : (pb b).obj N ⟶ (pb c).obj M) (f : (pb a).obj F ⟶ M) (g : (pb a').obj F ⟶ N) :
    tr f ≫ resP a c M = tr g ≫ resQ w φ ↔ (pb b).map g ≫ φ = (sqIso w).hom.app F ≫ (pb c).map f := by
  have h1 : ∀ ψ : (pb c).obj ((pb a).obj F) ⟶ (pb c).obj M,
      tr (tr ψ) = (adj a').unit.app F ≫ resQ w ((sqIso w).hom.app F ≫ ψ) := fun ψ => by
    rw [← resQ_map, ← Category.assoc, ← unit_resP, tr, tr, resP, Functor.map_comp, Category.assoc]
  have h2 : tr f ≫ resP a c M = tr (tr ((pb c).map f)) := by
    rw [tr, Category.assoc, pushforwardUnit_naturality, tr, tr, resP, Functor.map_comp]
  have h3 : tr g ≫ resQ w φ = tr (tr ((sqIso w).inv.app F ≫ (pb b).map g ≫ φ)) := by
    rw [h1, Iso.hom_inv_id_app_assoc, tr, Category.assoc, map_resQ]
  rw [h2, h3]
  constructor
  · intro h
    rw [tr_injective (tr_injective h), Iso.hom_inv_id_app_assoc]
  · intro h
    rw [h, Iso.inv_hom_id_app_assoc]

theorem bijective_resP [IsOpenImmersion c] (M : T.Modules) {V : X.Opens} (hV : a ⁻¹ᵁ V ≤ c.opensRange) :
    Function.Bijective ((resP a c M).app V) := by
  rw [show ((resP a c M).app V : _ → _) = _ from funext (pushforwardUnit_app M V)]
  exact bijective_pullbackSections c M hV rfl

theorem bijective_resQ [IsOpenImmersion b] (w : b ≫ a' = c ≫ a) {N : T'.Modules} {M : S.Modules}
    (φ : (pb b).obj N ⟶ M) [IsIso φ] {V : X.Opens} (hV : a' ⁻¹ᵁ V ≤ b.opensRange) :
    Function.Bijective ((resQ w φ).app V) := by
  rw [show ((resQ w φ).app V : _ → _) = _ from funext (resQ_app w φ V)]
  refine (ConcreteCategory.bijective_of_isIso (φ.app _)).comp (bijective_pullbackSections b N hV ?_)
  rw [← Scheme.Hom.comp_preimage, ← w, Scheme.Hom.comp_preimage]

end Square

section Glue

variable {X T : Scheme.{0}} {ι : Type} {T' S : ι → Scheme.{0}} {a : T ⟶ X} {a' : ∀ i, T' i ⟶ X}
  {b : ∀ i, S i ⟶ T' i} {c : ∀ i, S i ⟶ T} [IsOpenImmersion a] [∀ i, IsOpenImmersion (a' i)]
  [∀ i, IsOpenImmersion (b i)] [∀ i, IsOpenImmersion (c i)] (w : ∀ i, b i ≫ a' i = c i ≫ a)
  (hS : ∀ i, a.opensRange ⊓ (a' i).opensRange ≤ (c i ≫ a).opensRange)
  (hd : ∀ i j, i ≠ j → (a' i).opensRange ⊓ (a' j).opensRange ≤ a.opensRange)
  (hc : ∀ x : X, x ∈ a.opensRange ∨ ∃ i, x ∈ (a' i).opensRange)

include hc in

theorem hom_ext_cover {F G : X.Modules} {f g : F ⟶ G} (h : (pb a).map f = (pb a).map g)
    (h' : ∀ i, (pb (a' i)).map f = (pb (a' i)).map g) : f = g := by
  have key : ∀ {Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j], (pb j).map f = (pb j).map g →
      ∀ V ≤ j.opensRange, ∀ s, f.app V s = g.app V s := fun j _ e V hV s =>
    (bijective_pullbackSections j G hV rfl).1 (by
      rw [← pullback_map_app_pullbackSections, ← pullback_map_app_pullbackSections, e])
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext s
  change f.app V s = g.app V s
  refine Twist.sec_ext_of_cover
    (fun k : Option ι => V ⊓ k.elim a.opensRange fun i => (a' i).opensRange) (fun _ => inf_le_left)
    (fun x hx => Opens.mem_iSup.2 ?_) fun k => ?_
  · rcases hc x with h | ⟨i, h⟩
    exacts [⟨none, hx, h⟩, ⟨some i, hx, h⟩]
  · rw [← app_resM, ← app_resM]
    cases k with
    | none => exact key a h _ inf_le_right _
    | some i => exact key (a' i) (h' i) _ inf_le_right _

include hc in

theorem shortExact_of_cover (K : ShortComplex X.Modules) (h : (K.map (pb a)).ShortExact)
    (h' : ∀ i, (K.map (pb (a' i))).ShortExact) : K.ShortExact := by
  have z : ∀ {F G : X.Modules} (f : F ⟶ G), (pb a).map f = 0 → (∀ i, (pb (a' i)).map f = 0) → f = 0 :=
    fun f e e' => hom_ext_cover hc (by rw [e, Functor.map_zero]) fun i => by rw [e', Functor.map_zero]
  have m : ∀ {Y : Scheme.{0}} (j : Y ⟶ X), (K.map (pb j)).ShortExact → ∀ {F : X.Modules} (g : F ⟶ K.X₁),
      g ≫ K.f = 0 → (pb j).map g = 0 := fun j hj F g e => by
    haveI : Mono ((pb j).map K.f) := hj.mono_f
    rw [← cancel_mono ((pb j).map K.f), ← Functor.map_comp, e, Functor.map_zero, zero_comp]
  have ep : ∀ {Y : Scheme.{0}} (j : Y ⟶ X), (K.map (pb j)).ShortExact → ∀ {F : X.Modules} (g : K.X₃ ⟶ F),
      K.g ≫ g = 0 → (pb j).map g = 0 := fun j hj F g e => by
    haveI : Epi ((pb j).map K.g) := hj.epi_g
    rw [← cancel_epi ((pb j).map K.g), ← Functor.map_comp, e, Functor.map_zero, comp_zero]
  have ex : ∀ {Y : Scheme.{0}} (j : Y ⟶ X), (K.map (pb j)).ShortExact →
      (pb j).map (kernel.ι K.g ≫ cokernel.π K.f) = 0 := fun j hj => by
    rw [Functor.map_comp]
    exact hj.exact.comp_eq_zero (by rw [ShortComplex.map_g, ← Functor.map_comp, kernel.condition, Functor.map_zero])
      (by rw [ShortComplex.map_f, ← Functor.map_comp, cokernel.condition, Functor.map_zero])
  exact ShortComplex.ShortExact.mk'
    ((ShortComplex.exact_iff_kernel_ι_comp_cokernel_π_zero K).2 (z _ (ex a h) fun i => ex _ (h' i)))
    (Preadditive.mono_of_cancel_zero _ fun g e => z _ (m a h g e) fun i => m _ (h' i) g e)
    (Preadditive.epi_of_cancel_zero _ fun g e => z _ (ep a h g e) fun i => ep _ (h' i) g e)

include hc in

theorem isVB_of_cover {F : X.Modules} {r : ℕ} (h : IsVB ((pb a).obj F) r) (h' : ∀ i, IsVB ((pb (a' i)).obj F) r) :
    IsVB F r := fun x => by
  have key : ∀ {Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j], IsVB ((pb j).obj F) r → x ∈ j.opensRange →
      ∃ (U : X.Opens) (e : Fin r → Γ(F, U)), x ∈ U ∧ IsFrame e := by
    rintro Y j _ hj ⟨y, rfl⟩
    obtain ⟨W, e, hy, he⟩ := hj.of_iso ((Scheme.Modules.restrictFunctorIsoPullback j).app F).symm y
    exact ⟨j ''ᵁ W, e, ⟨y, hy, rfl⟩, (isFrame_restrict_iff j e).1 he⟩
  rcases hc x with hx | ⟨i, hx⟩
  exacts [key a h hx, key _ (h' i) hx]

variable {M : T.Modules} {N : ∀ i, (T' i).Modules} (φ : ∀ i, (pb (b i)).obj (N i) ⟶ (pb (c i)).obj M)

include w hS in
theorem preimage_le_b (i : ι) {V : X.Opens} (hV : V ⊓ (a' i).opensRange ≤ a.opensRange) :
    a' i ⁻¹ᵁ V ≤ (b i).opensRange := fun y hy => by
  obtain ⟨s, hs⟩ := hS i (x := a' i y) ⟨hV ⟨hy, y, rfl⟩, y, rfl⟩
  refine ⟨s, (a' i).isOpenEmbedding.injective ?_⟩
  rw [← hs, ← w, Scheme.Hom.comp_apply]

include hS in
theorem preimage_le_c (i : ι) {V : X.Opens} (hV : V ≤ (a' i).opensRange) :
    a ⁻¹ᵁ V ≤ (c i).opensRange := fun y hy => by
  obtain ⟨s, hs⟩ := hS i (x := a y) ⟨⟨y, rfl⟩, hV hy⟩
  refine ⟨s, a.isOpenEmbedding.injective ?_⟩
  rw [← hs, Scheme.Hom.comp_apply]

include hS in
theorem bijective_π [∀ i, IsIso (φ i)] {V : X.Opens} (hV : V ≤ a.opensRange) :
    Function.Bijective ((starπ (fun i => resP a (c i) M) fun i => resQ (w i) (φ i)).app V) :=
  bijective_starπ _ _ fun i => bijective_resQ _ _ (preimage_le_b w hS i (inf_le_left.trans hV))

include hS hd in
theorem bijective_π' [∀ i, IsIso (φ i)] (j : ι) {V : X.Opens} (hV : V ≤ (a' j).opensRange) :
    Function.Bijective ((starπ' (fun i => resP a (c i) M) (fun i => resQ (w i) (φ i)) j).app V) :=
  bijective_starπ' _ _ j (bijective_resP _ (preimage_le_c hS j hV)) fun i hi =>
    bijective_resQ _ _ (preimage_le_b w hS i ((inf_le_inf_right _ hV).trans (hd j i hi.symm)))

include hS hd in

theorem exists_glue_obj (ψ : ∀ i, (pb (b i)).obj (N i) ≅ (pb (c i)).obj M) :
    ∃ (D : X.Modules) (e : (pb a).obj D ≅ M) (e' : ∀ i, (pb (a' i)).obj D ≅ N i),
      ∀ i, (pb (b i)).map (e' i).hom ≫ (ψ i).hom = (sqIso (w i)).hom.app D ≫ (pb (c i)).map e.hom := by
  let p := fun i => resP a (c i) M
  let q := fun i => resQ (w i) (ψ i).hom
  obtain ⟨e, he⟩ := tr_surjective (starπ p q)
  choose e' he' using fun i => tr_surjective (starπ' p q i)
  haveI : IsIso e := isIso_of_tr e fun V hV => he ▸ bijective_π w hS (fun i => (ψ i).hom) hV
  haveI : ∀ i, IsIso (e' i) := fun i => isIso_of_tr _ fun V hV =>
    he' i ▸ bijective_π' w hS hd (fun i => (ψ i).hom) i hV
  refine ⟨star p q, asIso e, fun i => asIso (e' i), fun i => (transpose_comp_restriction_eq_iff (w i) _ _ _).1 ?_⟩
  rw [asIso_hom, asIso_hom, he, he']
  exact star_comm p q i

include hS hd hc in

theorem exists_glue_hom {F G : X.Modules} (f : (pb a).obj F ⟶ (pb a).obj G)
    (f' : ∀ i, (pb (a' i)).obj F ⟶ (pb (a' i)).obj G)
    (h : ∀ i, (pb (b i)).map (f' i) ≫ (sqIso (w i)).hom.app G = (sqIso (w i)).hom.app F ≫ (pb (c i)).map f) :
    ∃ g : F ⟶ G, (pb a).map g = f ∧ ∀ i, (pb (a' i)).map g = f' i := by
  let p := fun i => resP a (c i) ((pb a).obj G)
  let q := fun i => resQ (w i) ((sqIso (w i)).hom.app G)
  obtain ⟨η, hη, hη'⟩ := exists_star_lift p q (tr (𝟙 _)) (fun i => tr (𝟙 _)) fun i =>
    (transpose_comp_restriction_eq_iff (w i) _ _ _).2 (by simp)
  obtain ⟨l, hl, hl'⟩ := exists_star_lift p q (tr f) (fun i => tr (f' i)) fun i => (transpose_comp_restriction_eq_iff (w i) _ _ _).2 (h i)
  haveI : IsIso η := by
    refine Twist.isIso_of_cover η (U := fun k : Option ι => k.elim a.opensRange fun i => (a' i).opensRange)
      (eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ?_) fun k V hV => ?_
    · rcases hc x with h | ⟨i, h⟩
      exacts [⟨none, h⟩, ⟨some i, h⟩]
    · cases k with
      | none =>
        refine (Function.Bijective.of_comp_iff' (bijective_π w hS (fun i => (sqIso (w i)).hom.app G) hV) _).1 ?_
        have := bijective_tr (𝟙 ((pb a).obj G)) hV
        rw [← hη] at this
        exact this
      | some i =>
        refine (Function.Bijective.of_comp_iff'
          (bijective_π' w hS hd (fun i => (sqIso (w i)).hom.app G) i hV) _).1 ?_
        have := bijective_tr (𝟙 ((pb (a' i)).obj G)) hV
        rw [← hη'] at this
        exact this
  refine ⟨l ≫ inv η, tr_injective ?_, fun i => tr_injective ?_⟩
  · rw [← Category.comp_id ((pb a).map _), ← comp_tr, ← hη, ← hl]; simp
  · rw [← Category.comp_id ((pb (a' i)).map _), ← comp_tr, ← hη', ← hl']; simp

end Glue

end GlobalTheory.TwoSeq
