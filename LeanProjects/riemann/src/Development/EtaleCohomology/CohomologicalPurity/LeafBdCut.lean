import Development.EtaleCohomology.CohomologicalPurity.LeafIndExc

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex.HomComplex

namespace LateralTheory.CohomologicalPurity.Bd

section Defs
variable {R : Type} [CommRing R] {A B D : Cx R}

abbrev pb (f : A ⟶ B) {I : Cx R} {n : ℤ} (c : Cochain B I n) : Cochain A I n := (Cochain.ofHom f).comp c (zero_add n)

abbrev hpb (f : A ⟶ B) (I : Cx R) (n : ℤ) : CohomologyClass B I n →+ CohomologyClass A I n :=
  cpre (Cocycle.ofHom f) I n n (zero_add n)

structure Good (i : A ⟶ B) (l r : B ⟶ D) (I : Cx R) : Prop where
  w : i ≫ l = i ≫ r
  surj : ∀ (n : ℤ) (a : Cochain A I n), ∃ c : Cochain B I n, pb i c = a
  glue : ∀ (n : ℤ) (c c' : Cochain B I n), pb i c = pb i c' → ∃ b : Cochain D I n, pb l b = c ∧ pb r b = c'
  ext : ∀ (n : ℤ) (b b' : Cochain D I n), pb l b = pb l b' → pb r b = pb r b' → b = b'

def Tri (i : A ⟶ B) (l r : B ⟶ D) {I : Cx R} {n : ℤ} (a : Cocycle A I n) (c : Cochain B I n)
    (b : Cocycle D I (n + 1)) : Prop :=
  pb i c = a.1 ∧ pb l b.1 = δ n (n + 1) c ∧ pb r b.1 = 0

def IsDelta (i : A ⟶ B) (l r : B ⟶ D) (I : Cx R) (n : ℤ) (d : CohomologyClass A I n →+ (hpb r I (n + 1)).ker) : Prop :=
  ∀ (a : Cocycle A I n) (c : Cochain B I n) (b : Cocycle D I (n + 1)), Tri i l r a c b →
    (d (CohomologyClass.mk a)).1 = CohomologyClass.mk b

theorem Good.tri {i : A ⟶ B} {l r : B ⟶ D} {I : Cx R} (h : Good i l r I) {n : ℤ} (a : Cocycle A I n) :
    ∃ c b, Tri i l r a c b := by
  obtain ⟨c, hc⟩ := h.surj n a.1
  obtain ⟨b, hl, hr⟩ := h.glue (n + 1) (δ n (n + 1) c) 0 (by
    rw [pb, ← δ_ofHom_comp]
    change δ n (n + 1) (pb i c) = _
    rw [hc]; simp [pb])
  refine ⟨c, Cocycle.mk b (n + 1 + 1) rfl (h.ext _ _ _ ?_ ?_), hc, hl, hr⟩
  · rw [pb, ← δ_ofHom_comp]
    change δ _ _ (pb l b) = _
    rw [hl, δ_δ]; simp [pb]
  · rw [pb, ← δ_ofHom_comp]
    change δ _ _ (pb r b) = _
    rw [hr]; simp [pb]

theorem pb_pb (f : A ⟶ B) (g : B ⟶ D) {I : Cx R} {n : ℤ} (c : Cochain D I n) : pb f (pb g c) = pb (f ≫ g) c := by
  simp [pb, Cochain.ofHom_comp]

end Defs

def LeafMono : Prop := ∀ (R : Type) [CommRing R] {U E : Spc} (f : U ⟶ E), Mono f → ∀ p : ℤ, Mono (((chains R).map f).f p)

def LeafPush : Prop := ∀ (R : Type) [CommRing R] {U E E' D : Spc} (f : U ⟶ E) (g : U ⟶ E') (l : E ⟶ D) (r : E' ⟶ D),
  IsPushout f g l r → ∀ p : ℤ, IsPushout (((chains R).map f).f p) (((chains R).map g).f p) (((chains R).map l).f p)
    (((chains R).map r).f p)

def LeafGood : Prop := ∀ (R : Type) [CommRing R] {A B D : Cx R} (i : A ⟶ B) (l r : B ⟶ D) (I : Cx R),
  (∀ p, Mono (i.f p)) → (∀ p, IsPushout (i.f p) (i.f p) (l.f p) (r.f p)) → (∀ p, Injective (I.X p)) → Good i l r I

def LeafDelta : Prop := ∀ (R : Type) [CommRing R] {A B D : Cx R} (i : A ⟶ B) (l r : B ⟶ D) (I : Cx R),
  Good i l r I → ∀ n : ℤ, ∃ d, IsDelta i l r I n d

def LeafExact : Prop := ∀ (R : Type) [CommRing R] {A B D : Cx R} (i : A ⟶ B) (l r : B ⟶ D) (I : Cx R),
  Good i l r I → ∀ (n : ℤ) d, IsDelta i l r I n d →
    Function.Exact ((hpb l I n).comp (hpb r I n).ker.subtype) (hpb i I n) ∧ Function.Exact (hpb i I n) d ∧
    Function.Exact d ((hpb l I (n + 1)).comp (hpb r I (n + 1)).ker.subtype)

def LeafGen : Prop := ∀ (R : Type) [CommRing R] (P : PSh),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (freeGen R P U x) = freeGen R P V (P.map g.op x)) ∧
  (∀ (P' : PSh) (f : P ⟶ P') (U : Scheme.{0}) (x : P.obj (op U)),
    Sec.map ((free R).map f) (freeGen R P U x) = freeGen R P' U (f.app (op U) x)) ∧
  (∀ (G : Shv R) (φ ψ : (free R).obj P ⟶ G),
    (∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map φ (freeGen R P U x) = Sec.map ψ (freeGen R P U x)) → φ = ψ) ∧
  ∀ (G : Shv R) (t : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U),
    (∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (t U x) = t V (P.map g.op x)) →
    ∃ φ : (free R).obj P ⟶ G, ∀ (U : Scheme.{0}) (x : P.obj (op U)), Sec.map φ (freeGen R P U x) = t U x

def LeafImgHom : Prop := ∀ (S R : Type) [CommRing S] [CommRing R] (I : Cx S) (J : Cx R) (ρ : SemiMap I J),
  ∃ T : ∀ (P : PSh) (s : ℤ), ((free S).obj P ⟶ I.X s) →+ ((free R).obj P ⟶ J.X s),
    (∀ (P : PSh) (s : ℤ) (φ : (free S).obj P ⟶ I.X s) (U : Scheme.{0}) (x : P.obj (op U)),
      Sec.map (T P s φ) (freeGen R P U x) = ρ.app U s (Sec.map φ (freeGen S P U x))) ∧
    (∀ (P : PSh) (s t : ℤ) (φ : (free S).obj P ⟶ I.X s), T P t (φ ≫ I.d s t) = T P s φ ≫ J.d s t) ∧
    ∀ (P P' : PSh) (f : P ⟶ P') (s : ℤ) (φ : (free S).obj P' ⟶ I.X s),
      T P s ((free S).map f ≫ φ) = (free R).map f ≫ T P' s φ

def LeafImg : Prop := ∀ (S R : Type) [CommRing S] [CommRing R] (I : Cx S) (J : Cx R) (ρ : SemiMap I J),
  ∃ T : ∀ (E : Spc) (n : ℤ), Cochain ((chains S).obj E) I n →+ Cochain ((chains R).obj E) J n,
    (∀ (E : Spc) (n : ℤ) (α : Cochain ((chains S).obj E) I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0})
      (x : Sx E p U), ev (T E n α) p s h U x = ρ.app U s (ev α p s h U x)) ∧
    (∀ (E : Spc) (n m : ℤ) (α : Cochain ((chains S).obj E) I n), T E m (δ n m α) = δ n m (T E n α)) ∧
    ∀ (E E' : Spc) (f : E ⟶ E') (n : ℤ) (α : Cochain ((chains S).obj E') I n),
      T E n (pb ((chains S).map f) α) = pb ((chains R).map f) (T E' n α)

theorem good (h1 : LeafMono) (h2 : LeafPush) (h3 : LeafGood) (R : Type) [CommRing R] (F : Shv R) (P : Arrow Spc)
    (hP : Mono P.hom) : Good ((chains R).map P.hom) ((chains R).map (dbl.inl P)) ((chains R).map (dbl.inr P)) (res R F) :=
  h3 R _ _ _ _ (h1 R _ hP) (h2 R _ _ _ _ (IsPushout.of_hasPushout P.hom P.hom)) fun p => by
    unfold res; infer_instance

theorem inl_map {P' P : Arrow Spc} (φ : P' ⟶ P) : dbl.inl P' ≫ dbl.map φ = φ.right ≫ dbl.inl P :=
  pushout.inl_desc _ _ _

theorem goal_of (h1 : LeafMono) (h2 : LeafPush) (h3 : LeafGood) (h4 : LeafDelta) (h5 : LeafExact) (h6 : LeafImg) :
    LeafBd := by
  have G := fun (q : ℕ) (i : ℤ) => good h1 h2 h3 (ZMod q) (tw q i)
  have ex : ∀ (q : ℕ) (P : Arrow Spc) (n i : ℤ), ∃ d : Ht q P.left n i →+ Hs q P (n + 1) i, Mono P.hom →
      IsDelta ((chains _).map P.hom) ((chains _).map (dbl.inl P)) ((chains _).map (dbl.inr P)) (res _ (tw q i)) n d := by
    intro q P n i
    by_cases hP : Mono P.hom
    · obtain ⟨d, hd⟩ := h4 _ _ _ _ _ (G q i P hP) n
      exact ⟨d, fun _ => hd⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose d hd using ex
  refine ⟨d, fun q P hP n i => h5 _ _ _ _ _ (G q i P hP) n _ (hd q P n i hP), ?_, ?_⟩
  · intro q P' P φ hP' hP n i u
    obtain ⟨a, rfl⟩ := u.mk_surjective
    obtain ⟨c, b, ht⟩ := (G q i P hP).tri a
    have e := hd q P n i hP a c b ht
    have e' := hd q P' n i hP' (zcomp (Cocycle.ofHom ((chains _).map φ.left)) a (zero_add n))
      (pb ((chains _).map φ.right) c) (zcomp (Cocycle.ofHom ((chains _).map (dbl.map φ))) b (zero_add _)) (by
        obtain ⟨t1, t2, t3⟩ := ht
        refine ⟨?_, ?_, ?_⟩
        · change _ = pb _ a.1
          rw [← t1, pb_pb, pb_pb, ← Functor.map_comp, ← Functor.map_comp, Arrow.w φ]
        · change pb _ (pb _ b.1) = _
          rw [δ_ofHom_comp, ← t2]
          change _ = pb _ (pb _ b.1)
          rw [pb_pb, pb_pb, ← Functor.map_comp, ← Functor.map_comp, inl_map]
        · change pb _ (pb _ b.1) = _
          rw [pb_pb, ← Functor.map_comp, dbl.inr_map, Functor.map_comp, ← pb_pb, t3]
          exact Cochain.comp_zero _ _)
    apply Subtype.ext
    refine Eq.trans ?_ e'.symm
    exact congrArg (pull _ (dbl.map φ) (tw q i) (n + 1)) e
  · intro Q q _ _ P hP n i u
    obtain ⟨T, hv, hδ, hp⟩ := h6 _ _ _ _ (redMap Q q i)
    let Z : ∀ (E : Spc) (m : ℤ), Cocycle ((chains _).obj E) (res _ (tw Q i)) m → Cocycle ((chains _).obj E) (res _ (tw q i)) m :=
      fun E m α => Cocycle.mk (T E m α.1) (m + 1) rfl (by rw [← hδ, α.δ_eq_zero, map_zero])
    have key : (∀ E m x, red Q q E m i x = 0) ∨
        ∀ E m α, red Q q E m i (CohomologyClass.mk α) = CohomologyClass.mk (Z E m α) := by
      unfold red SemiMap.op pick
      split_ifs with h
      · exact Or.inr fun E m α => h.choose_spec E m α (Z E m α) (hv E m α.1)
      · exact Or.inl fun _ _ _ => rfl
    rcases key with k | k
    · rw [k, k, map_zero]; rfl
    obtain ⟨a, rfl⟩ := u.mk_surjective
    obtain ⟨c, b, ht⟩ := (G Q i P hP).tri a
    have e := hd Q P n i hP a c b ht
    have e' := hd q P n i hP (Z _ _ a) (T _ _ c) (Z _ _ b) (by
      obtain ⟨t1, t2, t3⟩ := ht
      refine ⟨?_, ?_, ?_⟩
      · change _ = T _ _ a.1
        rw [← hp, t1]
      · change pb _ (T _ _ b.1) = _
        rw [← hp, t2, hδ]
      · change pb _ (T _ _ b.1) = _
        rw [← hp, t3, map_zero])
    rw [k]
    refine e'.trans ?_
    rw [← k]
    exact congrArg _ e.symm

end LateralTheory.CohomologicalPurity.Bd
