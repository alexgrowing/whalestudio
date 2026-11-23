import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortExactOfCover

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.IndefiniteRowSideFullHecke.FrobeniusTwistEigen GlobalTheory.CurveRootGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoSeq

local notation "pb" => Scheme.Modules.pullback

section General

variable {O : Type} [CommRing O] {X : Scheme.{0}} {A B A' B' : X.Modules}
  {α : O →+* End A} {β : O →+* End B} {α' : O →+* End A'} {β' : O →+* End B'} {r : ℕ}

theorem shortExact_map_of_iso {T : Scheme.{0}} (j : T ⟶ X) {D : X.Modules} {D' : T.Modules} {f : A ⟶ D} {g : D ⟶ B}
    (w : f ≫ g = 0) {f' : (pb j).obj A ⟶ D'} {g' : D' ⟶ (pb j).obj B} {w' : f' ≫ g' = 0}
    (h : (ShortComplex.mk f' g' w').ShortExact) (e : (pb j).obj D ≅ D') (hf : (pb j).map f ≫ e.hom = f')
    (hg : e.hom ≫ g' = (pb j).map g) : ((ShortComplex.mk f g w).map (pb j)).ShortExact :=
  ShortComplex.shortExact_of_iso (ShortComplex.isoMk (S₁ := ShortComplex.mk f' g' w') (Iso.refl _) e.symm (Iso.refl _)
    (by simp [← hf]) (by simp [← hg])) h

theorem shortExact_map_open {T : Scheme.{0}} (f : T ⟶ X) [IsOpenImmersion f] {K : ShortComplex X.Modules}
    (h : K.ShortExact) : (K.map (pb f)).ShortExact := by
  haveI := h.mono_f
  haveI := h.epi_g
  exact ShortComplex.ShortExact.mk' (QCoh.exact_map_pullback f h.exact).1
    (FlagLocal.mono_pullback_of_isOpenImmersion f K.f) (QCoh.exact_map_pullback f h.exact).2

def InducesIso {T T' S : Scheme.{0}} {a : T ⟶ X} {a' : T' ⟶ X} {b : S ⟶ T'} {c : S ⟶ T} (w : b ≫ a' = c ≫ a)
    {D : X.Modules} {M : T.Modules} {N : T'.Modules} (e' : (pb a').obj D ≅ N) (e : (pb a).obj D ≅ M)
    (φ : (pb b).obj N ≅ (pb c).obj M) : Prop :=
  (pb b).map e'.hom ≫ φ.hom = (sqIso w).hom.app D ≫ (pb c).map e.hom

theorem exists_glue {T : Scheme.{0}} {ι : Type} {T' S : ι → Scheme.{0}} {a : T ⟶ X} {a' : ∀ i, T' i ⟶ X}
    {b : ∀ i, S i ⟶ T' i} {c : ∀ i, S i ⟶ T} [IsOpenImmersion a] [∀ i, IsOpenImmersion (a' i)]
    [∀ i, IsOpenImmersion (b i)] [∀ i, IsOpenImmersion (c i)] (w : ∀ i, b i ≫ a' i = c i ≫ a)
    (hS : ∀ i, a.opensRange ⊓ (a' i).opensRange ≤ (c i ≫ a).opensRange)
    (hd : ∀ i j, i ≠ j → (a' i).opensRange ⊓ (a' j).opensRange ≤ a.opensRange)
    (hc : ∀ x : X, x ∈ a.opensRange ∨ ∃ i, x ∈ (a' i).opensRange)
    (d₀ : DatumOn α β α' β' r a) (d' : ∀ i, DatumOn α β α' β' r (a' i))
    (φ : ∀ i, (pb (b i)).obj (d' i).D ≅ (pb (c i)).obj d₀.D) (hφ : ∀ i, Agree (d' i) d₀ (w i) (φ i)) :
    ∃ (d : Datum α β α' β' r) (e : (pb a).obj d.D ≅ d₀.D) (e' : ∀ i, (pb (a' i)).obj d.D ≅ (d' i).D),
      RestrictsTo d d₀ e ∧ (∀ i, RestrictsTo d (d' i) (e' i)) ∧
      ∀ i, InducesIso (w i) (e' i) e (φ i) := by
  obtain ⟨D, e, e', he⟩ := exists_glue_obj w hS hd φ
  have he₁ : ∀ i, (pb (b i)).map (e' i).inv ≫ (sqIso (w i)).hom.app D = (φ i).hom ≫ (pb (c i)).map e.inv := fun i => by
    rw [← cancel_epi ((pb (b i)).map (e' i).hom), reassoc_of% he i]
    simp [← Functor.map_comp, ← Functor.map_comp_assoc]
  have hin : ∀ {F : X.Modules} (f : (pb a).obj F ⟶ d₀.D) (f' : ∀ i, (pb (a' i)).obj F ⟶ (d' i).D),
      (∀ i, (pb (b i)).map (f' i) ≫ (φ i).hom = (sqIso (w i)).hom.app F ≫ (pb (c i)).map f) →
      ∃ g : F ⟶ D, (pb a).map g ≫ e.hom = f ∧ ∀ i, (pb (a' i)).map g ≫ (e' i).hom = f' i := fun f f' h => by
    obtain ⟨g, hg, hg'⟩ := exists_glue_hom w hS hd hc (f ≫ e.inv) (fun i => f' i ≫ (e' i).inv) fun i => by
      rw [Functor.map_comp, Category.assoc, he₁, reassoc_of% h i, Functor.map_comp]
    exact ⟨g, by simp [hg], fun i => by simp [hg']⟩
  have hout : ∀ {F : X.Modules} (f : d₀.D ⟶ (pb a).obj F) (f' : ∀ i, (d' i).D ⟶ (pb (a' i)).obj F),
      (∀ i, (φ i).hom ≫ (pb (c i)).map f = (pb (b i)).map (f' i) ≫ (sqIso (w i)).hom.app F) →
      ∃ g : D ⟶ F, e.hom ≫ f = (pb a).map g ∧ ∀ i, (e' i).hom ≫ f' i = (pb (a' i)).map g := fun f f' h => by
    obtain ⟨g, hg, hg'⟩ := exists_glue_hom w hS hd hc (e.hom ≫ f) (fun i => (e' i).hom ≫ f' i) fun i => by
      rw [Functor.map_comp, Category.assoc, ← h, reassoc_of% he i, Functor.map_comp]
    exact ⟨g, hg.symm, fun i => (hg' i).symm⟩
  obtain ⟨a₀, ha, ha'⟩ := hin d₀.a (fun i => (d' i).a) fun i => (hφ i).2.1
  obtain ⟨b₀, hb, hb'⟩ := hout d₀.b (fun i => (d' i).b) fun i => (hφ i).2.2.1
  obtain ⟨u₀, hu, hu'⟩ := hin d₀.u (fun i => (d' i).u) fun i => (hφ i).2.2.2.1
  obtain ⟨v₀, hv, hv'⟩ := hout d₀.v (fun i => (d' i).v) fun i => (hφ i).2.2.2.2
  choose ρ hρ hρ' using fun x : O => hin (e.hom ≫ act d₀.ρ x) (fun i => (e' i).hom ≫ act (d' i).ρ x) fun i => by
    have := (hφ i).1 x
    rw [act_pullAct, act_pullAct] at this
    rw [Functor.map_comp, Category.assoc, this, reassoc_of% he i, Functor.map_comp]
  have ext : ∀ {F : X.Modules} {g g' : F ⟶ D}, (pb a).map g ≫ e.hom = (pb a).map g' ≫ e.hom →
      (∀ i, (pb (a' i)).map g ≫ (e' i).hom = (pb (a' i)).map g' ≫ (e' i).hom) → g = g' := fun h h' =>
    hom_ext_cover hc ((cancel_mono _).1 h) fun i => (cancel_mono _).1 (h' i)
  have m1 : ∀ {Y : Scheme.{0}} {F : Y.Modules} (σ : O →+* End F), act σ 1 = 𝟙 F := fun σ => map_one σ
  have m0 : ∀ {Y : Scheme.{0}} {F : Y.Modules} (σ : O →+* End F), act σ 0 = 0 := fun σ => map_zero σ
  have mm : ∀ {Y : Scheme.{0}} {F : Y.Modules} (σ : O →+* End F) x y, act σ (x * y) = act σ y ≫ act σ x :=
    fun σ => map_mul σ
  have ma : ∀ {Y : Scheme.{0}} {F : Y.Modules} (σ : O →+* End F) x y, act σ (x + y) = act σ x + act σ y :=
    fun σ => map_add σ
  let ρ₀ : O →+* End D :=
    { toFun := ρ
      map_one' := show ρ 1 = 𝟙 D from ext (by rw [hρ, m1]; simp) fun i => by rw [hρ', m1]; simp
      map_mul' := fun x y => show ρ (x * y) = ρ y ≫ ρ x from
        ext (by rw [hρ, mm, Functor.map_comp, Category.assoc, hρ, reassoc_of% hρ y]) fun i => by
          rw [hρ', mm, Functor.map_comp, Category.assoc, hρ', reassoc_of% hρ' y i]
      map_zero' := show ρ 0 = (0 : D ⟶ D) from ext (by rw [hρ, m0]; simp) fun i => by rw [hρ', m0]; simp
      map_add' := fun x y => show ρ (x + y) = (ρ x + ρ y : D ⟶ D) from
        ext (by rw [hρ, ma, Functor.map_add, Preadditive.add_comp, hρ, hρ, Preadditive.comp_add]) fun i => by
          rw [hρ', ma, Functor.map_add, Preadditive.add_comp, hρ', hρ', Preadditive.comp_add] }
  have ein : ∀ {F : X.Modules} {σ : O →+* End F} {g : F ⟶ D}, IsEquivariant (pullAct σ a) d₀.ρ ((pb a).map g ≫ e.hom) →
      (∀ i, IsEquivariant (pullAct σ (a' i)) (d' i).ρ ((pb (a' i)).map g ≫ (e' i).hom)) → IsEquivariant σ ρ₀ g :=
    fun {F σ g} h h' x => show act σ x ≫ g = g ≫ ρ x from
      ext (by rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hρ, ← Category.assoc _ e.hom, ← h x,
        act_pullAct]) fun i => by
        rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hρ', ← Category.assoc _ (e' i).hom,
          ← h' i x, act_pullAct]
  have eout : ∀ {F : X.Modules} {σ : O →+* End F} {g : D ⟶ F} {f : d₀.D ⟶ (pb a).obj F}
      {f' : ∀ i, (d' i).D ⟶ (pb (a' i)).obj F}, e.hom ≫ f = (pb a).map g → (∀ i, (e' i).hom ≫ f' i = (pb (a' i)).map g) →
      IsEquivariant d₀.ρ (pullAct σ a) f → (∀ i, IsEquivariant (d' i).ρ (pullAct σ (a' i)) (f' i)) →
      IsEquivariant ρ₀ σ g :=
    fun {F σ g f f'} hf hf' h h' x => show ρ x ≫ g = g ≫ act σ x from
      hom_ext_cover hc (by rw [Functor.map_comp, Functor.map_comp, ← hf, reassoc_of% hρ x, h x, act_pullAct,
        Category.assoc]) fun i => by
        rw [Functor.map_comp, Functor.map_comp, ← hf', reassoc_of% hρ' x i, h' i x, act_pullAct, Category.assoc]
  have w₁ : a₀ ≫ b₀ = 0 := hom_ext_cover hc
    (by rw [Functor.map_comp, ← hb, reassoc_of% ha, d₀.w₁, Functor.map_zero]) fun i => by
      rw [Functor.map_comp, ← hb', reassoc_of% ha' i, (d' i).w₁, Functor.map_zero]
  have w₂ : u₀ ≫ v₀ = 0 := hom_ext_cover hc
    (by rw [Functor.map_comp, ← hv, reassoc_of% hu, d₀.w₂, Functor.map_zero]) fun i => by
      rw [Functor.map_comp, ← hv', reassoc_of% hu' i, (d' i).w₂, Functor.map_zero]
  refine ⟨{ D := D, ρ := ρ₀, a := a₀, b := b₀, u := u₀, v := v₀, w₁ := w₁, w₂ := w₂
            isVB := isVB_of_cover hc (d₀.isVB.of_iso e.symm) fun i => (d' i).isVB.of_iso (e' i).symm
            exact₁ := shortExact_of_cover hc _ (shortExact_map_of_iso a w₁ d₀.exact₁ e ha hb) fun i =>
              shortExact_map_of_iso _ w₁ (d' i).exact₁ (e' i) (ha' i) (hb' i)
            exact₂ := shortExact_of_cover hc _ (shortExact_map_of_iso a w₂ d₀.exact₂ e hu hv) fun i =>
              shortExact_map_of_iso _ w₂ (d' i).exact₂ (e' i) (hu' i) (hv' i)
            equiv_a := ein (ha ▸ d₀.equiv_a) fun i => ha' i ▸ (d' i).equiv_a
            equiv_b := eout hb hb' d₀.equiv_b fun i => (d' i).equiv_b
            equiv_u := ein (hu ▸ d₀.equiv_u) fun i => hu' i ▸ (d' i).equiv_u
            equiv_v := eout hv hv' d₀.equiv_v fun i => (d' i).equiv_v }, e, e',
    ⟨hρ, ha, hb, hu, hv⟩, fun i => ⟨fun x => hρ' x i, ha' i, hb' i, hu' i, hv' i⟩, he⟩

theorem inf_square (V U : X.Opens) :
    X.homOfLE (inf_le_left : V ⊓ U ≤ V) ≫ V.ι = X.homOfLE (inf_le_right : V ⊓ U ≤ U) ≫ U.ι := by
  rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]

theorem range_inf_le (V U : X.Opens) :
    U.ι.opensRange ⊓ V.ι.opensRange ≤ (X.homOfLE (inf_le_right : V ⊓ U ≤ U) ≫ U.ι).opensRange := by
  rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
  intro x hx
  exact ⟨⟨x, hx.2, hx.1⟩, by rw [Scheme.homOfLE_ι]; rfl⟩

def AgreeOnInf {V U : X.Opens} (d : DatumOn α β α' β' r V.ι) (d₀ : DatumOn α β α' β' r U.ι) : Prop :=
  ∃ φ, Agree d d₀ (inf_square V U) φ

theorem exists_glue_opens {ι : Type} (U : X.Opens) (V : ι → X.Opens) (hd : ∀ i j, i ≠ j → V i ⊓ V j ≤ U)
    (hc : U ⊔ ⨆ i, V i = ⊤) (d₀ : DatumOn α β α' β' r U.ι) (d' : ∀ i, DatumOn α β α' β' r (V i).ι)
    (φ : ∀ i, (pb (X.homOfLE (inf_le_left : V i ⊓ U ≤ V i))).obj (d' i).D ≅
      (pb (X.homOfLE (inf_le_right : V i ⊓ U ≤ U))).obj d₀.D)
    (hφ : ∀ i, Agree (d' i) d₀ (inf_square (V i) U) (φ i)) :
    ∃ (d : Datum α β α' β' r) (e : (pb U.ι).obj d.D ≅ d₀.D) (e' : ∀ i, (pb (V i).ι).obj d.D ≅ (d' i).D),
      RestrictsTo d d₀ e ∧ (∀ i, RestrictsTo d (d' i) (e' i)) ∧
      ∀ i, InducesIso (inf_square (V i) U) (e' i) e (φ i) := by
  have h₁ : ∀ i, U.ι.opensRange ⊓ (V i).ι.opensRange ≤
      (X.homOfLE (inf_le_right : V i ⊓ U ≤ U) ≫ U.ι).opensRange := fun i => range_inf_le (V i) U
  have h₂ : ∀ i j, i ≠ j → (V i).ι.opensRange ⊓ (V j).ι.opensRange ≤ U.ι.opensRange := fun i j h => by
    rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
    exact hd i j h
  have h₃ : ∀ x : X, x ∈ U.ι.opensRange ∨ ∃ i, x ∈ (V i).ι.opensRange := fun x => by
    have : x ∈ U ⊔ ⨆ i, V i := by rw [hc]; trivial
    rcases Opens.mem_sup.1 this with h | h
    · exact .inl (by rwa [Scheme.Opens.opensRange_ι])
    · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 h
      exact .inr ⟨i, by rwa [Scheme.Opens.opensRange_ι]⟩
  exact exists_glue (T := U) (T' := fun i => V i) (S := fun i => (V i ⊓ U : X.Opens)) (a := U.ι)
    (a' := fun i => (V i).ι) (b := fun i => X.homOfLE (inf_le_left : V i ⊓ U ≤ V i))
    (c := fun i => X.homOfLE (inf_le_right : V i ⊓ U ≤ U)) (fun i => inf_square (V i) U) h₁ h₂ h₃ d₀ d' φ hφ

theorem exists_glue_points (U : X.Opens) (d₀ : DatumOn α β α' β' r U.ι)
    (h : ∀ x : X, x ∉ U → ∃ V : X.Opens, x ∈ V ∧ (∀ y ∈ V, y ≠ x → y ∈ U) ∧
      ∃ d : DatumOn α β α' β' r V.ι, AgreeOnInf d d₀) :
    ∃ (d : Datum α β α' β' r) (e : (pb U.ι).obj d.D ≅ d₀.D), RestrictsTo d d₀ e := by
  choose V hx hV d φ hφ using h
  obtain ⟨d, e, -, he, -⟩ := exists_glue_opens (ι := {x : X // x ∉ U}) U (fun x => V x.1 x.2)
    (fun x y hxy z hz => by
      by_cases e : z = x.1
      · exact hV _ _ z hz.2 fun e' => hxy (Subtype.ext (e.symm.trans e'))
      · exact hV _ _ z hz.1 e)
    (eq_top_iff.2 fun z _ => by
      by_cases hz : z ∈ U
      · exact Opens.mem_sup.2 (.inl hz)
      · exact Opens.mem_sup.2 (.inr (Opens.mem_iSup.2 ⟨⟨z, hz⟩, hx z hz⟩)))
    d₀ (fun x => d x.1 x.2) (fun x => φ x.1 x.2) fun x => hφ x.1 x.2
  exact ⟨d, e, he⟩

def Datum.restrict (d : Datum α β α' β' r) {T : Scheme.{0}} (f : T ⟶ X) [IsOpenImmersion f] : DatumOn α β α' β' r f where
  D := (pb f).obj d.D
  ρ := pullAct d.ρ f
  a := (pb f).map d.a
  b := (pb f).map d.b
  u := (pb f).map d.u
  v := (pb f).map d.v
  w₁ := by rw [← Functor.map_comp, d.w₁, Functor.map_zero]
  w₂ := by rw [← Functor.map_comp, d.w₂, Functor.map_zero]
  isVB := d.isVB.pullback f
  exact₁ := shortExact_map_open f d.exact₁
  exact₂ := shortExact_map_open f d.exact₂
  equiv_a := d.equiv_a.pullback f
  equiv_b := d.equiv_b.pullback f
  equiv_u := d.equiv_u.pullback f
  equiv_v := d.equiv_v.pullback f

theorem Datum.restrictsTo_restrict (d : Datum α β α' β' r) {T : Scheme.{0}} (f : T ⟶ X) [IsOpenImmersion f] :
    RestrictsTo d (d.restrict f) (Iso.refl _) :=
  ⟨fun _ => (Category.comp_id _).trans (Category.id_comp _).symm, Category.comp_id _, Category.id_comp _,
    Category.comp_id _, Category.id_comp _⟩

theorem Datum.agree_restrict (d : Datum α β α' β' r) {T T' S : Scheme.{0}} {a : T ⟶ X} {a' : T' ⟶ X} [IsOpenImmersion a]
    [IsOpenImmersion a'] {b : S ⟶ T'} {c : S ⟶ T} (w : b ≫ a' = c ≫ a) :
    Agree (d.restrict a') (d.restrict a) w ((sqIso w).app d.D) :=
  ⟨fun x => (sqIso w).hom.naturality (act d.ρ x), (sqIso w).hom.naturality d.a, ((sqIso w).hom.naturality d.b).symm,
    (sqIso w).hom.naturality d.u, ((sqIso w).hom.naturality d.v).symm⟩

end General

theorem hasDieu_of_opens {O : Type} [CommRing O] (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (c : O →+* O)
    {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] {G : Over C} [GrpObj G] [QuasiSeparated G.hom] (i : OAct O G) (g : ℕ)
    (hg : IsVB (omega G) g) {ι : Type} (U : C.Opens) (V : ι → C.Opens) (hd : ∀ j l, j ≠ l → V j ⊓ V l ≤ U)
    (hc : U ⊔ ⨆ j, V j = ⊤) (d₀ : DieuDatumOn q k c i g U.ι) (d' : ∀ j, DieuDatumOn q k c i g (V j).ι)
    (h : ∀ j, AgreeOnInf (d' j) d₀) : HasDieu q k c i := by
  choose φ hφ using h
  obtain ⟨d, -⟩ := exists_glue_opens U V hd hc d₀ d' φ hφ
  exact (hasDieu_iff q k c i).2 ⟨g, hg, ⟨d⟩⟩

theorem hasDieu_of_points {O : Type} [CommRing O] (q : ℕ) [Fact q.Prime] (k : Type) [Field k] [CharP k q] (c : O →+* O)
    {C : Scheme.{0}} [Algebra k Γ(C, ⊤)] {G : Over C} [GrpObj G] [QuasiSeparated G.hom] (i : OAct O G) (g : ℕ)
    (hg : IsVB (omega G) g) (U : C.Opens) (d₀ : DieuDatumOn q k c i g U.ι)
    (h : ∀ x : C, x ∉ U → ∃ V : C.Opens, x ∈ V ∧ (∀ y ∈ V, y ≠ x → y ∈ U) ∧
      ∃ d : DieuDatumOn q k c i g V.ι, AgreeOnInf d d₀) : HasDieu q k c i := by
  obtain ⟨d, -⟩ := exists_glue_points U d₀ h
  exact (hasDieu_iff q k c i).2 ⟨g, hg, ⟨d⟩⟩

end GlobalTheory.TwoSeq
