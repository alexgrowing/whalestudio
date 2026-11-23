import Development.EtaleCohomology.EtaleSheaves.EtaleChapterETwo

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.t_E2Cut

structure Hyp : Prop where
  a1 : A1
  a2 : A2
  a3 : A3
  a4 : A4
  a5 : A5
  a7 : A7
  a8 : A8
  a9 : A9
  a10 : A10
  b1 : B1
  b2 : B2
  b3 : B3
  b4 : B4
  b5 : B5
  e1 : E1

abbrev cpt (A : Type) [CommRing A] [IsLocalRing A] :
    Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))

def PB (q : ℕ) (i : ℤ) {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)) : Prop :=
  Eqv _ (sch.map (pullback.fst p (cpt A))) (tw q i)

def AICSch (Z : Scheme.{0}) : Prop := IsIntegral Z ∧ ∀ U : Z.Opens, IsAffineOpen U → (U : Set Z).Nonempty → AIC Γ(Z, U)

attribute [local instance] MvPolynomial.gradedAlgebra in

def P1 : Scheme.{0} := Proj (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ)

def IsLine {L S : Scheme.{0}} (l : L ⟶ S) : Prop :=
  IsProper l ∧ ∃ f : L ⟶ P1, IsPullback f l (terminal.from P1) (terminal.from S)

def IL {Z S : Scheme.{0}} (c : Z ⟶ S) : Prop := ∃ (L : Scheme.{0}) (u : Z ⟶ L) (l : L ⟶ S), IsIntegralHom u ∧ IsLine l ∧ u ≫ l = c

inductive IT {S : Scheme.{0}} : ∀ {X : Scheme.{0}}, (X ⟶ S) → Prop
  | int {X : Scheme.{0}} (p : X ⟶ S) : IsIntegralHom p → IT p
  | step {Z T : Scheme.{0}} (c : Z ⟶ T) (k : T ⟶ S) (p : Z ⟶ S) : IT k → IL c → c ≫ k = p → IT p

def MV : Prop := Hyp → ∀ (R : Type) [CommRing R] (F : Shv R),
  ∃ δ : ∀ {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) (n : ℤ), H R (sch.obj (pullback f g)) F n →+ H R (sch.obj X) F (n + 1),
    (∀ {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g],
      Set.range f ∪ Set.range g = Set.univ → ∀ n : ℤ,
      (∀ (a : H R (sch.obj U) F n) (b : H R (sch.obj V) F n),
        pull R (sch.map (pullback.fst f g)) F n a = pull R (sch.map (pullback.snd f g)) F n b →
        ∃ x, pull R (sch.map f) F n x = a ∧ pull R (sch.map g) F n x = b) ∧
      (∀ w, δ f g n w = 0 ↔ ∃ a b, w = pull R (sch.map (pullback.fst f g)) F n a - pull R (sch.map (pullback.snd f g)) F n b) ∧
      ∀ x, (pull R (sch.map f) F (n + 1) x = 0 ∧ pull R (sch.map g) F (n + 1) x = 0) ↔ ∃ w, δ f g n w = x) ∧
    ∀ {U V X U' V' X' : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) (f' : U' ⟶ X') (g' : V' ⟶ X') [IsOpenImmersion f] [IsOpenImmersion g]
      [IsOpenImmersion f'] [IsOpenImmersion g'], Set.range f ∪ Set.range g = Set.univ → Set.range f' ∪ Set.range g' = Set.univ →
      ∀ (u : U ⟶ U') (v : V ⟶ V') (p : X ⟶ X') (hu : f ≫ p = u ≫ f') (hv : g ≫ p = v ≫ g') (n : ℤ) w,
        δ f g n (pull R (sch.map (pullback.map f g f' g' u v p hu hv)) F n w) = pull R (sch.map p) F (n + 1) (δ f' g' n w)

def Cont : Prop := Hyp → ∀ (q : ℕ) {J : Type} [SmallCategory J] [IsCofiltered J] (D : J ⥤ Scheme.{0}) (c : Cone D), IsLimit c →
  (∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)) → (∀ j, CompactSpace (D.obj j)) → (∀ j, QuasiSeparatedSpace (D.obj j)) →
  (∀ j, IsUnit (q : Γ(D.obj j, ⊤))) → ∀ n i : ℤ,
  (∀ x : Ht q (sch.obj c.pt) n i, ∃ j y, pull _ (sch.map (c.π.app j)) _ _ y = x) ∧
  ∀ j (y : Ht q (sch.obj (D.obj j)) n i), pull _ (sch.map (c.π.app j)) _ _ y = 0 →
    ∃ (k : J) (f : k ⟶ j), pull _ (sch.map (D.map f)) _ _ y = 0

def ZLG : Prop := Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S] [QuasiSeparatedSpace S]
  [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f], IsUnit (q : Γ(S, ⊤)) → ∀ i : ℤ,
  (∀ s : S, Eqv _ (sch.map (pullback.map (f ≫ p) (S.fromSpecStalk s) p (S.fromSpecStalk s) f (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i)) →
  Eqv _ (sch.map f) (tw q i)

def HZero : Prop := Hyp → ∀ (q : ℕ) {Y X : Scheme.{0}} (f : Y ⟶ X), AICSch X → ConnectedSpace Y → IsUnit (q : Γ(X, ⊤)) → ∀ i : ℤ,
  Function.Bijective (pull _ (sch.map f) (tw q i) 0)

def AICAcyc : Prop := Hyp → ∀ (q : ℕ) (Z : Scheme.{0}) [CompactSpace Z] [QuasiSeparatedSpace Z], AICSch Z → IsUnit (q : Γ(Z, ⊤)) →
  Acyc q (sch.obj Z)

def QuotAcyc : Prop := Hyp → ∀ (q : ℕ) (B : Type) [CommRing B] [IsDomain B] (I : Ideal B), AIC B → IsUnit (q : B) → Acyc q (sp (B ⧸ I))

def IntPB : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) → ∀ {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of A)), IsIntegralHom p → PB q i p

def Desc : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) → ∀ {P : Scheme.{0}}
  (p : P ⟶ Spec (CommRingCat.of A)),
  (∀ (X : Scheme.{0}) (h : X ⟶ P), IsIntegralHom h → ∃ (Y : Scheme.{0}) (k : Y ⟶ X), IsIntegralHom k ∧ Surjective k ∧ PB q i (k ≫ h ≫ p)) →
  PB q i p

def Cover : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) → ∀ {P : Scheme.{0}}
  [CompactSpace P] [QuasiSeparatedSpace P] (p : P ⟶ Spec (CommRingCat.of A)),
  (∀ (Z : Scheme.{0}) (h : Z ⟶ P), IsIntegralHom h → AICSch Z → PB q i (h ≫ p)) →
  ∃ (Y : Scheme.{0}) (k : Y ⟶ P), IsIntegralHom k ∧ Surjective k ∧ PB q i (k ≫ p)

def Stein : Prop := ∀ {Z S : Scheme.{0}} (g : Z ⟶ S) [QuasiCompact g] [QuasiSeparated g], AICSch Z →
  ∃ (T : Scheme.{0}) (c : Z ⟶ T) (k : T ⟶ S), AICSch T ∧ IsDominant c ∧ IsIntegralHom k ∧ c ≫ k = g

def Fib : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) → ∀ {Z S : Scheme.{0}}
  (c : Z ⟶ S) (p : S ⟶ Spec (CommRingCat.of A)) [QuasiCompact p] [QuasiSeparated p] [QuasiCompact c] [QuasiSeparated c] [IsDominant c],
  AICSch Z → AICSch S →
  (∀ (B : Type) [CommRing B] [IsLocalRing B], SH B → IsUnit (q : B) → ∀ t : Spec (CommRingCat.of B) ⟶ S, PB q i (pullback.snd c t)) →
  (PB q i (c ≫ p) ↔ PB q i p)

def Chow : Prop := ∀ (A : Type) [CommRing A] {Z X : Scheme.{0}} (h : Z ⟶ X) (p : X ⟶ Spec (CommRingCat.of A)) [IsProper p],
  IsIntegralHom h → AICSch Z → ∃ (Z' : Scheme.{0}) (c : Z' ⟶ Z), AICSch Z' ∧ IsDominant c ∧ IT c ∧ IT (c ≫ h ≫ p)

def LineZero : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A], SH A → ∀ {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)),
  IL p → AICSch Z → ConnectedSpace ↑(pullback p (cpt A))

def LineOne : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], SH A → IsUnit (q : A) → ∀ {Z : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z → Subsingleton (Ht q (sch.obj (pullback p (cpt A))) 1 i)

def LineHigh : Prop := Hyp → ∀ (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A], IsUnit (q : A) → ∀ {Z : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)), IL p → AICSch Z → ∀ n : ℤ, 2 ≤ n → Subsingleton (Ht q (sch.obj (pullback p (cpt A))) n i)

theorem IsLine.bc {L S L' S' : Scheme.{0}} {l : L ⟶ S} (h : IsLine l) {a : L' ⟶ L} {l' : L' ⟶ S'} {t : S' ⟶ S}
    (w : IsPullback a l' l t) : IsLine l' := by
  obtain ⟨h1, f, hf⟩ := h
  refine ⟨MorphismProperty.of_isPullback w h1, a ≫ f, ?_⟩
  have := w.paste_horiz hf
  rwa [terminal.comp_from] at this

theorem IL.bc {Z S Z' S' : Scheme.{0}} {c : Z ⟶ S} (h : IL c) {a : Z' ⟶ Z} {c' : Z' ⟶ S'} {t : S' ⟶ S}
    (w : IsPullback a c' c t) : IL c' := by
  obtain ⟨L, u, l, hu, hl, rfl⟩ := h
  have e : (a ≫ u) ≫ l = c' ≫ t := by rw [Category.assoc, w.w]
  refine ⟨pullback l t, pullback.lift (a ≫ u) c' e, pullback.snd l t, ?_, hl.bc (IsPullback.of_hasPullback l t), pullback.lift_snd _ _ _⟩
  have w' : IsPullback a (pullback.lift (a ≫ u) c' e) u (pullback.fst l t) :=
    IsPullback.of_bot (by rw [pullback.lift_snd]; exact w) (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback l t)
  exact MorphismProperty.of_isPullback w' hu

theorem IL.pre {W Z S : Scheme.{0}} {c : Z ⟶ S} (h : IL c) (v : W ⟶ Z) (hv : IsIntegralHom v) : IL (v ≫ c) := by
  obtain ⟨L, u, l, hu, hl, rfl⟩ := h
  exact ⟨L, v ≫ u, l, inferInstance, hl, Category.assoc _ _ _⟩

theorem IL.cancel {W T S : Scheme.{0}} {c : W ⟶ T} {k : T ⟶ S} (hk : IsIntegralHom k) (h : IL (c ≫ k)) : IL c := by
  obtain ⟨L, u, l, hu, hl, e⟩ := h
  refine ⟨pullback l k, pullback.lift u c e, pullback.snd l k, ?_, hl.bc (IsPullback.of_hasPullback l k), pullback.lift_snd _ _ _⟩
  have : IsIntegralHom (pullback.lift u c e ≫ pullback.fst l k) := by rwa [pullback.lift_fst]
  exact IsIntegralHom.of_comp _ (pullback.fst l k)

theorem IL.qc {Z S : Scheme.{0}} {c : Z ⟶ S} (h : IL c) : QuasiCompact c ∧ QuasiSeparated c := by
  obtain ⟨L, u, l, hu, ⟨hl, -⟩, rfl⟩ := h
  exact ⟨inferInstance, inferInstance⟩

theorem IT.qc {X S : Scheme.{0}} {p : X ⟶ S} (h : IT p) : QuasiCompact p ∧ QuasiSeparated p := by
  induction h with
  | int p hp => exact ⟨inferInstance, inferInstance⟩
  | step c k p _ hc e ih =>
    obtain ⟨_, _⟩ := hc.qc
    obtain ⟨_, _⟩ := ih
    subst e
    exact ⟨inferInstance, inferInstance⟩

theorem IT.pre {X S : Scheme.{0}} {p : X ⟶ S} (h : IT p) {W : Scheme.{0}} (v : W ⟶ X) (hv : IsIntegralHom v) : IT (v ≫ p) := by
  cases h with
  | int p hp => exact IT.int _ inferInstance
  | step c k p hk hc e => exact IT.step (v ≫ c) k _ hk (hc.pre v hv) (by rw [Category.assoc, e])

theorem IT.bc {X S : Scheme.{0}} {p : X ⟶ S} (h : IT p) {S' : Scheme.{0}} (t : S' ⟶ S) :
    ∀ {X' : Scheme.{0}} {a : X' ⟶ X} {p' : X' ⟶ S'}, IsPullback a p' p t → IT p' := by
  induction h with
  | int p hp => exact fun w => IT.int _ (MorphismProperty.of_isPullback w hp)
  | step c k p _ hc e ih =>
    intro X' a p' w
    subst e
    have e : (a ≫ c) ≫ k = p' ≫ t := by rw [Category.assoc, w.w]
    have w' : IsPullback a (pullback.lift (a ≫ c) p' e) c (pullback.fst k t) :=
      IsPullback.of_bot (by rw [pullback.lift_snd]; exact w) (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback k t)
    exact IT.step _ _ _ (ih (IsPullback.of_hasPullback k t)) (hc.bc w') (pullback.lift_snd _ _ _)

theorem unit_of {q : ℕ} {A : Type} [CommRing A] (h : IsUnit (q : A)) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)) :
    IsUnit (q : Γ(X, ⊤)) := by
  simpa using h.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ p.appTop).hom

theorem qcqs_of {A : Type} [CommRing A] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)) [QuasiCompact p] [QuasiSeparated p] :
    CompactSpace X ∧ QuasiSeparatedSpace X :=
  ⟨QuasiCompact.compactSpace_of_compactSpace p, quasiSeparatedSpace_of_quasiSeparated p⟩

theorem eqv_of (h9 : A9) {q : ℕ} {i : ℤ} {E E' : Spc} (f : E ⟶ E') (h0 : Function.Bijective (pull _ f (tw q i) 0))
    (h : ∀ n, 0 < n → Subsingleton (Ht q E n i)) (h' : ∀ n, 0 < n → Subsingleton (Ht q E' n i)) : Eqv _ f (tw q i) := by
  intro n
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have := (h9 _ (tw q i)).1 E n hn
    have := (h9 _ (tw q i)).1 E' n hn
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩
  · exact h0
  · have := h n hn
    have := h' n hn
    exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩

theorem reduce (H : Hyp) (hD : Desc) (hC : Cover) (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A] (hq : IsUnit (q : A))
    {P : Scheme.{0}} (p : P ⟶ Spec (CommRingCat.of A)) [QuasiCompact p] [QuasiSeparated p]
    (h : ∀ (Z : Scheme.{0}) (h : Z ⟶ P), IsIntegralHom h → AICSch Z → PB q i (h ≫ p)) : PB q i p := by
  refine hD H q i A hq p fun X g hg => ?_
  obtain ⟨_, _⟩ := qcqs_of (g ≫ p)
  refine hC H q i A hq (g ≫ p) fun Z k hk hZ => ?_
  rw [← Category.assoc]
  exact h Z (k ≫ g) inferInstance hZ

theorem line (H : Hyp) (hD : Desc) (hC : Cover) (h0 : HZero) (hA : AICAcyc) (l0 : LineZero) (l1 : LineOne) (l2 : LineHigh)
    (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A] (hS : SH A) (hq : IsUnit (q : A))
    {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)) (hp : IL p) : PB q i p := by
  obtain ⟨_, _⟩ := hp.qc
  refine reduce H hD hC q i A hq p fun Z h hh hZ => ?_
  have hl := hp.pre h hh
  obtain ⟨_, _⟩ := qcqs_of (h ≫ p)
  refine eqv_of H.a9 _ (h0 H q _ hZ (l0 A hS _ hl hZ) (unit_of hq (h ≫ p)) i) (fun n hn => ?_)
    (fun n hn => hA H q Z hZ (unit_of hq (h ≫ p)) n i hn)
  rcases (show n = 1 ∨ 2 ≤ n by omega) with rfl | h2
  · exact l1 H q i A hS hq _ hl hZ
  · exact l2 H q i A hq _ hl hZ n h2

theorem tower (H : Hyp) (hD : Desc) (hC : Cover) (h0 : HZero) (hA : AICAcyc) (l0 : LineZero) (l1 : LineOne) (l2 : LineHigh)
    (hI : IntPB) (hSt : Stein) (hF : Fib)
    (q : ℕ) (i : ℤ) (A : Type) [CommRing A] [IsLocalRing A] (hS : SH A) (hq : IsUnit (q : A))
    {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of A)) (hp : IT p) :
    ∀ {W : Scheme.{0}} (v : W ⟶ X), IsIntegralHom v → PB q i (v ≫ p) := by
  induction hp with
  | int p hp => exact fun v hv => hI H q i A hS hq _ inferInstance
  | step c k p hk hc e ih =>
    intro W v hv
    subst e
    obtain ⟨_, _⟩ := hc.qc
    obtain ⟨_, _⟩ := hk.qc
    refine reduce H hD hC q i A hq _ fun Z h hh hZ => ?_
    obtain ⟨T, c', k', hT, hd, hk', e⟩ := hSt ((h ≫ v) ≫ c) hZ
    have hl : IL c' := IL.cancel hk' (e ▸ hc.pre (h ≫ v) inferInstance)
    obtain ⟨_, _⟩ := hl.qc
    have e' : h ≫ v ≫ c ≫ k = c' ≫ k' ≫ k := by rw [← Category.assoc c', e]; simp
    rw [e']
    exact (hF H q i A hq c' (k' ≫ k) hZ hT fun B _ _ hB hqB t =>
      line H hD hC h0 hA l0 l1 l2 q i B hB hqB _ (hl.bc (IsPullback.of_hasPullback c' t))).2 (ih k' hk')

theorem goal_of (hD : Desc) (hC : Cover) (h0 : HZero) (hA : AICAcyc) (l0 : LineZero) (l1 : LineOne) (l2 : LineHigh)
    (hI : IntPB) (hSt : Stein) (hF : Fib) (hCh : Chow) : LateralTheory.E.EtaleChapterETwo := by
  intro a1 a2 a3 a4 a5 a7 a8 a9 a10 _ b1 b2 b3 b4 b5 _ _ _ _ _ _ _ _ _ e1 q A _ _ hS hq X p _ i
  have H : Hyp := ⟨a1, a2, a3, a4, a5, a7, a8, a9, a10, b1, b2, b3, b4, b5, e1⟩
  have tw' : ∀ (B : Type) [CommRing B] [IsLocalRing B], SH B → IsUnit (q : B) → ∀ {Y : Scheme.{0}}
      (r : Y ⟶ Spec (CommRingCat.of B)), IT r → PB q i r := fun B _ _ hB hqB Y r hr => by
    have := tower H hD hC h0 hA l0 l1 l2 hI hSt hF q i B hB hqB r hr (𝟙 _) inferInstance
    rwa [Category.id_comp] at this
  refine reduce H hD hC q i A hq p fun Z h hh hZ => ?_
  obtain ⟨Z', c, hZ', hd, hc, hc'⟩ := hCh A h p hh hZ
  obtain ⟨_, _⟩ := hc.qc
  exact (hF H q i A hq c (h ≫ p) hZ' hZ fun B _ _ hB hqB t =>
    tw' B hB hqB _ (hc.bc t (IsPullback.of_hasPullback c t))).1 (tw' A hS hq _ hc')

end LateralTheory.E.t_E2Cut

end
