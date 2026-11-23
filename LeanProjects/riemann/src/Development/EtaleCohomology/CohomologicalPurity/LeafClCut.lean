import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Cl

def Zc {R : Type} [CommRing R] (K : Cx R) {X : Scheme.{0}} (U : X.Opens) (n : ℤ) : AddSubgroup (Sec (K.X n) X) :=
  ((K.X n).obj.map U.ι.op).hom.toAddMonoidHom.ker ⊓ ((K.d n (n + 1)).hom.app (op X)).hom.toAddMonoidHom.ker

theorem mem_Zc {R : Type} [CommRing R] {K : Cx R} {X : Scheme.{0}} {U : X.Opens} {n : ℤ} (a : Sec (K.X n) X) :
    a ∈ Zc K U n ↔ Sec.res U.ι a = 0 ∧ Sec.map (K.d n (n + 1)) a = 0 := Iff.rfl

def Bd {R : Type} [CommRing R] (K : Cx R) {X : Scheme.{0}} (U : X.Opens) (n : ℤ) (a : Sec (K.X n) X) : Prop :=
  ∃ b : Sec (K.X (n - 1)) X, Sec.res U.ι b = 0 ∧ Sec.map (K.d (n - 1) n) b = a

abbrev rs {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}} {V W : X.Opens} (h : V ≤ W) (a : Sec G W.toScheme) :
    Sec G V.toScheme := Sec.res (X.homOfLE h) a

structure Pc {X : Scheme.{0}} (U : X.Opens) where
  Y : Scheme.{0}
  j : Y ⟶ X
  op : IsOpenImmersion j
  V : Y.Opens
  hV : V = j ⁻¹ᵁ U

abbrev Pc.res {X : Scheme.{0}} {U : X.Opens} (p : Pc U) (q : ℕ) (n i : ℤ) : Hs q (opn U) n i →+ Hs q (opn p.V) n i :=
  Hs.pull q (opnMap p.j p.V U p.hV.le) n i

def LocVan (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ) : Prop := ∀ (x : X) (W : X.Opens), x ∈ W →
  ∃ p : Pc U, x ∈ Set.range p.j ∧ Set.range p.j ⊆ W ∧ ∀ n < m, Subsingleton (Hs q (opn p.V) n i)

def Sep (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ) : Prop := ∀ s : Hs q (opn U) m i,
  (∀ x : X, x ∉ U → ∃ p : Pc U, x ∈ Set.range p.j ∧ p.res q m i s = 0) → s = 0

def Glue (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ) : Prop :=
  ∀ (A : Type) (p : A → Pc U) (s : ∀ a, Hs q (opn (p a).V) m i), (∀ x : X, x ∉ U → ∃ a, x ∈ Set.range (p a).j) →
  (∀ a b (y : (p a).Y), (p a).j y ∉ U → (p a).j y ∈ Set.range (p b).j →
    ∃ (t : Pc (p a).V) (u : t.Y ⟶ (p b).Y) (h : t.V ≤ u ⁻¹ᵁ (p b).V), t.j ≫ (p a).j = u ≫ (p b).j ∧ y ∈ Set.range t.j ∧
      t.res q m i (s a) = Hs.pull q (opnMap u t.V (p b).V h) m i (s b)) →
  ∃ c, ∀ a, (p a).res q m i c = s a

structure Frame {d : ℕ} (P : SP d) where
  B : Type
  [cr : CommRing B]
  I : Ideal B
  x : Fin d → B
  hx : Ideal.span (Set.range x) = I
  w : Spec (CommRingCat.of B) ⟶ P.X
  z : Spec (CommRingCat.of (B ⧸ I)) ⟶ P.Z
  h : off B I ≤ w ⁻¹ᵁ P.U
  cart : IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) z w P.ι

attribute [instance] Frame.cr

def LeafDisc : Prop := ∀ (R : Type) [CommRing R] (K : Cx R) (n : ℤ),
  ∃ cl : ∀ P : PSh, ((free R).obj P ⟶ K.X n) → CohomologyClass ((chains R).obj (disc.obj P)) K n,
    (∀ P a b, a ≫ K.d n (n + 1) = 0 → b ≫ K.d n (n + 1) = 0 → cl P (a + b) = cl P a + cl P b) ∧
    (∀ P x, ∃ a, a ≫ K.d n (n + 1) = 0 ∧ cl P a = x) ∧
    (∀ P a, a ≫ K.d n (n + 1) = 0 → (cl P a = 0 ↔ ∃ b, b ≫ K.d (n - 1) n = a)) ∧
    ∀ (P' P : PSh) (f : P' ⟶ P) (a : (free R).obj P ⟶ K.X n), a ≫ K.d n (n + 1) = 0 →
      cpre (Cocycle.ofHom ((chains R).map (disc.map f))) K n n (zero_add n) (cl P a) = cl P' ((free R).map f ≫ a)

def LeafDict : Prop := ∀ (q : ℕ) (n i : ℤ),
  ∃ cls : ∀ {X : Scheme.{0}} (U : X.Opens), Zc (res _ (tw q i)) U n →+ Hs q (opn U) n i,
    (∀ {X : Scheme.{0}} (U : X.Opens), Function.Surjective (cls U)) ∧
    (∀ {X : Scheme.{0}} (U : X.Opens) (a : Zc (res _ (tw q i)) U n), cls U a = 0 ↔ Bd _ U n a.1) ∧
    ∀ {X' X : Scheme.{0}} (f : X' ⟶ X) (U' : X'.Opens) (U : X.Opens) (h : U' ≤ f ⁻¹ᵁ U) (a : Zc (res _ (tw q i)) U n)
      (a' : Zc (res _ (tw q i)) U' n), a'.1 = Sec.res f a.1 → Hs.pull q (opnMap f U' U h) n i (cls U a) = cls U' a'

def LeafZorn : Prop := ∀ (R : Type) [CommRing R] (G : Shv R) (X : Scheme.{0}) (N : ∀ W : X.Opens, AddSubgroup (Sec G W.toScheme)),
  (∀ (V W : X.Opens) (h : V ≤ W), ∀ a ∈ N W, rs h a ∈ N V) →
  (∀ (W : X.Opens) (a : Sec G W.toScheme), (∀ x ∈ W, ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ rs h a ∈ N V) → a ∈ N W) →
  (∀ (V W : X.Opens) (h : V ≤ W), ∀ a ∈ N V, ∃ b ∈ N W, rs h b = a) →
  ∀ (W : X.Opens) (A : Type) (V : A → X.Opens) (h : ∀ k, V k ≤ W) (a : ∀ k, Sec G (V k).toScheme),
    (∀ x ∈ W, ∃ k, x ∈ V k) → (∀ k l, rs inf_le_left (a k) - rs inf_le_right (a l) ∈ N (V k ⊓ V l)) →
    ∃ c : Sec G W.toScheme, ∀ k, rs (h k) c - a k ∈ N (V k)

def LeafFlq : Prop := ∀ (R : Type) [CommRing R] (K : Cx R), (∀ s, Injective (K.X s)) → (∀ s < 0, IsZero (K.X s)) →
  ∀ (X : Scheme.{0}) (U : X.Opens) (m : ℤ),
  (∀ n < m, ∀ (W : X.Opens), ∀ a ∈ Zc K (W.ι ⁻¹ᵁ U) n, ∀ x ∈ W,
    ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ Bd K (V.ι ⁻¹ᵁ U) n (rs h a)) →
  (∀ (W : X.Opens) (a : Sec (K.X m) W.toScheme),
    (∀ x ∈ W, ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ Bd K (V.ι ⁻¹ᵁ U) m (rs h a)) → Bd K (W.ι ⁻¹ᵁ U) m a) ∧
  ∀ (A : Type) (V : A → X.Opens) (a : ∀ k, Sec (K.X m) (V k).toScheme), (∀ k, a k ∈ Zc K ((V k).ι ⁻¹ᵁ U) m) →
    (∀ x : X, ∃ k, x ∈ V k) →
    (∀ k l, ∀ x ∈ V k, x ∈ V l → ∃ (T : X.Opens) (hk : T ≤ V k) (hl : T ≤ V l), x ∈ T ∧
      Bd K (T.ι ⁻¹ᵁ U) m (rs hk (a k) - rs hl (a l))) →
    ∃ c ∈ Zc K U m, ∀ k, Bd K ((V k).ι ⁻¹ᵁ U) m (Sec.res (V k).ι c - a k)

def LeafDesc : Prop := ∀ (q : ℕ) {X : Scheme.{0}} (U : X.Opens) (m i : ℤ), LocVan q U m i → Sep q U m i ∧ Glue q U m i

def LeafNb : Prop := A1 → ∀ (q : ℕ) {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (J : Ideal B),
  Nbhd φ I → J = I.map φ → ∀ h, Exc q (opnMap (Spec.map (CommRingCat.ofHom φ)) (off B J) (off A I) h)

def LeafVanRing : Prop := Hyp → ∀ (d q : ℕ) [NeZero q] (A : Type) [CommRing A] (I : Ideal A), Chart d A I → IsUnit (q : A) →
  ∀ n i : ℤ, n < 2 * d → Subsingleton (Hs q (opn (off A I)) n i)

def LeafVan : Prop := Hyp → ∀ (d q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) → ∀ i : ℤ, LocVan q P.U (2 * d) i

def LeafVanF : Prop := Hyp → ∀ (d q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) → ∀ F : Frame P, Etale F.w →
  ∀ i : ℤ, LocVan q (off F.B F.I) (2 * d) i

def LeafOff : Prop := ∀ (d : ℕ) (P : SP d) (F : Frame P), off F.B F.I = F.w ⁻¹ᵁ P.U

def LeafGenRing : Prop := ∀ (d : ℕ) (A : Type) [CommRing A] (I : Ideal A), I.FG → Chart d A I →
  ∃ (a : Fin d → A) (r : A), r - 1 ∈ I ∧ (∀ j, a j ∈ I) ∧ ∀ y ∈ I, r * y ∈ Ideal.span (Set.range a)

def LeafGen : Prop := ∀ (d : ℕ) (P : SP d) (x : P.X), x ∉ P.U →
  ∃ F : Frame P, IsOpenImmersion F.w ∧ x ∈ Set.range F.w

def LeafMat : Prop := ∀ (d : ℕ) (A : Type) [CommRing A] (x y : Fin d → A),
  Ideal.span (Set.range x) = Ideal.span (Set.range y) → ∀ p : PrimeSpectrum A,
  ∃ M : Matrix (Fin d) (Fin d) A, M.det ∉ p.asIdeal ∧ y = M.mulVec x

def LeafCmp : Prop := ∀ (d : ℕ) (P : SP d) (F F₀ : Frame P), IsOpenImmersion F₀.w → ∀ y, F.w y ∈ Set.range F₀.w →
  ∃ (C : Type) (_ : CommRing C) (φ : F.B →+* C) (ψ : F₀.B →+* C) (M : Matrix (Fin d) (Fin d) C),
    IsOpenImmersion (Spec.map (CommRingCat.ofHom φ)) ∧ y ∈ Set.range (Spec.map (CommRingCat.ofHom φ)) ∧
    Spec.map (CommRingCat.ofHom φ) ≫ F.w = Spec.map (CommRingCat.ofHom ψ) ≫ F₀.w ∧ F.I.map φ = F₀.I.map ψ ∧
    IsUnit M.det ∧ φ ∘ F.x = M.mulVec (ψ ∘ F₀.x)

theorem off_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) :
    off B (I.map φ) = Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ off A I := by
  ext y
  change ¬ ((I.map φ : Set B) ⊆ (y : PrimeSpectrum B).asIdeal) ↔ ¬ ((I : Set A) ⊆ ((y : PrimeSpectrum B).asIdeal.comap φ))
  exact not_congr Ideal.map_le_iff_le_comap

theorem unit_B {X : Scheme.{0}} {q : ℕ} (hq : IsUnit (q : Γ(X, ⊤))) {B : Type} [CommRing B]
    (w : Spec (CommRingCat.of B) ⟶ X) : IsUnit (q : B) := by
  simpa using (hq.map w.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom

theorem inl_map {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc _ _ _

theorem dbl_comp {P'' P' P : Arrow Spc} (φ : P'' ⟶ P') (ψ : P' ⟶ P) : dbl.map (φ ≫ ψ) = dbl.map φ ≫ dbl.map ψ := by
  apply pushout.hom_ext
  · change dbl.inl _ ≫ _ = dbl.inl _ ≫ _
    rw [inl_map, ← Category.assoc, inl_map, Category.assoc, inl_map, ← Category.assoc]
    rfl
  · change dbl.inr _ ≫ _ = dbl.inr _ ≫ _
    rw [dbl.inr_map, ← Category.assoc, dbl.inr_map, Category.assoc, dbl.inr_map, ← Category.assoc]
    rfl

theorem opnMap_comp {X'' X' X : Scheme.{0}} (f : X'' ⟶ X') (g : X' ⟶ X) (U'' U' U) (h h' h'') :
    opnMap f U'' U' h ≫ opnMap g U' U h' = opnMap (f ≫ g) U'' U h'' := by
  apply Arrow.hom_ext
  · change sch.map _ ≫ sch.map _ = sch.map _
    rw [← Functor.map_comp, Scheme.Hom.resLE_comp_resLE]
  · exact (sch.map_comp f g).symm

theorem pull_pull {q : ℕ} {X'' X' X : Scheme.{0}} (f : X'' ⟶ X') (g : X' ⟶ X) {k : X'' ⟶ X} (e : f ≫ g = k) (U'' U' U)
    (h h' h'') (n i : ℤ) (c : Hs q (opn U) n i) :
    Hs.pull q (opnMap f U'' U' h) n i (Hs.pull q (opnMap g U' U h') n i c) = Hs.pull q (opnMap k U'' U h'') n i c := by
  subst e
  apply Subtype.ext
  rw [← opnMap_comp f g U'' U' U h h' h'']
  change pull _ (dbl.map _) _ n (pull _ (dbl.map _) _ n c.1) = pull _ (dbl.map _) _ n c.1
  rw [dbl_comp, pull_comp]

variable {d q : ℕ}

abbrev Frame.th {P : SP d} (F : Frame P) (q : ℕ) : Hs q (opn (off F.B F.I)) (2 * d) d := thom d q F.B F.I F.x F.hx

abbrev Frame.pl {P : SP d} (F : Frame P) (q : ℕ) : Hs q (opn P.U) (2 * d) d →+ Hs q (opn (off F.B F.I)) (2 * d) d :=
  Hs.pull q (opnMap F.w (off F.B F.I) P.U F.h) _ _

def Fund (q : ℕ) (P : SP d) (c : Hs q (opn P.U) (2 * d) d) : Prop := ∀ x : P.X, x ∉ P.U →
  ∃ F : Frame P, IsOpenImmersion F.w ∧ x ∈ Set.range F.w ∧ F.pl q c = F.th q

theorem span_comp {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (x : Fin d → A) :
    Ideal.span (Set.range (φ ∘ x)) = (Ideal.span (Set.range x)).map φ := by
  rw [Ideal.map_span, Set.range_comp]

theorem agree [NeZero q] (hT : IsThom d (thom d)) (hC : LeafCmp) {P : SP d} (hq : IsUnit (q : Γ(P.X, ⊤))) (F F₀ : Frame P)
    (h₀ : IsOpenImmersion F₀.w) (y) (hy : F.w y ∈ Set.range F₀.w) :
    ∃ (t : Pc (off F.B F.I)) (u : t.Y ⟶ Spec (CommRingCat.of F₀.B)) (h : t.V ≤ u ⁻¹ᵁ off F₀.B F₀.I),
      t.j ≫ F.w = u ≫ F₀.w ∧ y ∈ Set.range t.j ∧
      t.res q _ _ (F.th q) = Hs.pull q (opnMap u t.V _ h) _ _ (F₀.th q) := by
  obtain ⟨C, _, φ, ψ, M, ho, hyr, e, hI, hM, hx⟩ := hC d P F F₀ h₀ y hy
  obtain ⟨h1, h2, -, -⟩ := hT q
  have hB := unit_B hq F.w
  have a1 : Ideal.span (Set.range (φ ∘ F.x)) = F.I.map φ := by rw [span_comp, F.hx]
  have a2 : Ideal.span (Set.range (ψ ∘ F₀.x)) = F.I.map φ := by rw [span_comp, F₀.hx, hI]
  refine ⟨⟨_, _, ho, off C (F.I.map φ), off_map φ F.I⟩, Spec.map (CommRingCat.ofHom ψ),
    (hI ▸ off_map ψ F₀.I).le, e, hyr, ?_⟩
  refine (h1 _ _ φ _ _ _ _ a1 _ hB).trans (Eq.trans ?_ (h1 _ _ ψ _ _ _ _ a2 _ (unit_B hq F₀.w)).symm)
  have := h2 C _ (ψ ∘ F₀.x) M a2 (hx ▸ a1) (by simpa using hB.map φ) hM
  rw [← this]
  congr 1

theorem frame_eq [NeZero q] (hT : IsThom d (thom d)) (hC : LeafCmp) (hO : LeafOff) {P : SP d}
    (hq : IsUnit (q : Γ(P.X, ⊤))) {c} (hc : Fund q P c) (F : Frame P) (hS : Sep q (off F.B F.I) (2 * d) d) :
    F.pl q c = F.th q := by
  refine sub_eq_zero.1 (hS _ fun y hy => ?_)
  rw [hO] at hy
  obtain ⟨F₀, h₀, hy₀, e₀⟩ := hc (F.w y) hy
  obtain ⟨t, u, h, e, hyt, ht⟩ := agree hT hC hq F F₀ h₀ y hy₀
  refine ⟨t, hyt, ?_⟩
  have hle : t.V ≤ (u ≫ F₀.w) ⁻¹ᵁ P.U := fun a ha => by simpa using F₀.h (h ha)
  rw [map_sub, ht, ← e₀, sub_eq_zero]
  exact (pull_pull _ _ e _ _ _ _ _ hle _ _ c).trans (pull_pull _ _ rfl _ _ _ _ _ hle _ _ c).symm

def Frame.pc (hO : LeafOff) {P : SP d} (F : Frame P) (h : IsOpenImmersion F.w) : Pc P.U := ⟨_, F.w, h, off F.B F.I, hO d P F⟩

theorem goal_of (hTh : LeafThom) (hD : LeafDesc) (hV : LeafVan) (hVF : LeafVanF) (hO : LeafOff) (hG : LeafGen)
    (hC : LeafCmp) : LeafCl := by
  intro H d
  have hT : IsThom d (thom d) := @pick_spec _ ⟨fun _ _ _ _ _ _ => 0⟩ _ (hTh H d)
  have ex : ∀ (q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) → ∃ c, Fund q P c := by
    intro q _ P hq
    choose F hF hx using fun x : {x : P.X // x ∉ P.U} => hG d P x.1 x.2
    obtain ⟨c, hc⟩ := (hD q P.U _ _ (hV H d q P hq d)).2 _ (fun a => (F a).pc hO (hF a)) (fun a => (F a).th q)
      (fun x h => ⟨⟨x, h⟩, hx _⟩) (fun a b y _ hy => agree hT hC hq (F a) (F b) (hF b) y hy)
    exact ⟨c, fun x h => ⟨F ⟨x, h⟩, hF _, hx _, hc _⟩⟩
  have et : ∀ (q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) → ∀ c, Fund q P c → ∀ F : Frame P, Etale F.w →
      F.pl q c = F.th q := fun q _ P hq c hc F hF =>
    frame_eq hT hC hO hq hc F (hD q _ _ _ (hVF H d q P hq F hF d)).1
  have un : ∀ (q : ℕ) [NeZero q] (P : SP d), IsUnit (q : Γ(P.X, ⊤)) → ∀ c c', Fund q P c → Fund q P c' → c = c' := by
    intro q _ P hq c c' hc hc'
    refine sub_eq_zero.1 ((hD q P.U _ _ (hV H d q P hq d)).1 _ fun x hx => ?_)
    obtain ⟨F, hF, hxF, e⟩ := hc x hx
    refine ⟨F.pc hO hF, hxF, ?_⟩
    rw [map_sub, sub_eq_zero]
    exact e.trans (et q P hq c' hc' F inferInstance).symm
  refine ⟨fun q P => pick (Fund q P), fun q _ => ⟨?_, ?_, ?_⟩⟩
  · intro P hq B _ I x hx w z h hw hc
    exact et q P hq _ (pick_spec (ex q P hq)) ⟨B, I, x, hx, w, z, h, hc⟩ hw
  · intro P' P φ hq
    have hq' : IsUnit (q : Γ(P'.X, ⊤)) := by simpa using hq.map φ.f.appTop.hom
    refine un q P' hq' _ _ (fun x hx => ?_) (pick_spec (ex q P' hq'))
    obtain ⟨F, hF, hxF⟩ := hG d P' x hx
    have hle : off F.B F.I ≤ (F.w ≫ φ.f) ⁻¹ᵁ P.U := fun a ha => by simpa using φ.le (F.h ha)
    refine ⟨F, hF, hxF, (pull_pull _ _ rfl _ _ _ _ _ hle _ _ _).trans ?_⟩
    exact frame_eq hT hC hO hq (pick_spec (ex q P hq))
      ⟨F.B, F.I, F.x, F.hx, F.w ≫ φ.f, F.z ≫ φ.g, hle, (F.cart.flip.paste_horiz φ.cart.flip).flip⟩
      (hD q _ _ _ (hVF H d q P' hq' F inferInstance d)).1
  · intro r hr P hq
    have : NeZero r := ⟨fun h => NeZero.ne q (zero_dvd_iff.1 (h ▸ hr))⟩
    have hr' : IsUnit (r : Γ(P.X, ⊤)) := isUnit_of_dvd_unit (Nat.cast_dvd_cast hr) hq
    let c := pick (Fund q P)
    have hc0 : pull _ (dbl.inr (opn P.U)) (tw q d) (2 * d) c.1 = 0 := c.2
    let c' : Hs r (opn P.U) (2 * d) d := ⟨red q r _ _ _ c.1, by
      change pull _ (dbl.inr _) _ _ _ = 0
      rw [pull_red, hc0, map_zero]⟩
    refine congrArg Subtype.val (un r P hr' _ c' (pick_spec (ex r P hr')) fun x hx => ?_)
    obtain ⟨F, hF, hxF, e⟩ := pick_spec (ex q P hq) x hx
    refine ⟨F, hF, hxF, Subtype.ext ?_⟩
    rw [(hT q).2.2.2 r hr F.B F.I F.x F.hx (unit_B hq F.w), ← show _ = thom d q F.B F.I F.x F.hx from e]
    exact pull_red q r _ _ _ _

end LateralTheory.CohomologicalPurity.Cl
