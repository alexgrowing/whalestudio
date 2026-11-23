import Development.EtaleCohomology.EtaleSheaves.InstCommRingR
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.AlexanderWhitneyCupPullbackNaturality

def pcoc {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (α : Cocycle ((chains R).obj E') I n) :
    Cocycle ((chains R).obj E) I n :=
  zcomp (Cocycle.ofHom ((chains R).map f)) α (zero_add n)

theorem cpull_mk {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') (I : Cx R) {n : ℤ} (α : Cocycle ((chains R).obj E') I n) :
    cpull ((chains R).map f) I n (CohomologyClass.mk α) = CohomologyClass.mk (pcoc f α) := rfl

theorem pull_mk {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') (F : Shv R) {n : ℤ}
    (α : Cocycle ((chains R).obj E') (res R F) n) : pull R f F n (CohomologyClass.mk α) = CohomologyClass.mk (pcoc f α) := rfl

theorem sub_map {E E' : Spc} (f : E ⟶ E') {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    (Sx.map f x).sub j l h = Sx.map f (x.sub j l h) := by
  simp only [Sx.sub, Sx.map]
  rw [← FunctorToTypes.comp, ← FunctorToTypes.comp, NatTrans.naturality]

theorem inv_pull {q : ℕ} {E E' : Spc} (f : E ⟶ E') (h : Inv q E') : Inv q E :=
  fun U ⟨x⟩ => h U ⟨Sx.map f x⟩

def LeafEvPull : Prop := ∀ (R : Type) [CommRing R] {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ}
  (α : Cochain ((chains R).obj E') I n) (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U),
  ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (Sx.map f x)

def LeafCupAW : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)
  (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m),
  ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1

def LeafCupSpec : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k),
  ∃ c : CohomologyClass ((chains R).obj E) I n →+ CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k,
    ∀ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) (γ : Cocycle ((chains R).obj E) K k),
      μ.IsAW hk α.1 β.1 γ.1 → c (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

def OneProp (q : ℕ) (E : Spc) (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0) : Prop :=
  ∀ (U : Scheme.{0}) (x : Sx E 0 U) (ζ : Prim q Γ(U, ⊤)), ev α.1 0 0 (by simp) U x = resGen 0 ζ

def LeafOneEx : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E → ∃ α, OneProp q E α

def LeafOneUniq : Prop := ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E → ∀ α β, OneProp q E α → OneProp q E β →
  CohomologyClass.mk α = CohomologyClass.mk β

def IsChernClassCocycle (q : ℕ) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) : Prop :=
  (∀ (U : Scheme.{0}) (x : Sx E 0 U), ev γ.1 0 2 (by simp) U x = 0) ∧
  (∀ (U : Scheme.{0}) (x : Sx E 1 U) (v : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L x →
    ev γ.1 1 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)) ∧
  ∀ (U : Scheme.{0}) (x : Sx E 2 U) (v w : (Γ(U, ⊤))ˣ), v ^ q = lineUnit L (x.sub 0 1 (by omega)) →
    w ^ q = lineUnit L (x.sub 1 1 (by omega)) →
    ev γ.1 2 0 (by simp) U x = kumT q U v + kumT q U w - kumT q U (v * w)

def ChernClassExists : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E → ∃ γ, IsChernClassCocycle q L γ

def ChernClassUnique : Prop := ∀ (q : ℕ) [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)), Inv q E → ∀ γ δ, IsChernClassCocycle q L γ → IsChernClassCocycle q L δ →
  CohomologyClass.mk γ = CohomologyClass.mk δ

def KumProp (q : ℕ) {X : Scheme.{0}} (u : (Γ(X, ⊤))ˣ) (γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1) : Prop :=
  (∀ (U : Scheme.{0}) (x : U ⟶ X), ev γ.1 1 0 (by simp) U x = 0) ∧
  ∀ (U : Scheme.{0}) (x : U ⟶ X) (v : (Γ(U, ⊤))ˣ), v ^ q = Units.map x.appTop.hom.toMonoidHom u →
    ev γ.1 0 1 (by simp) U x = Sec.map ((res _ (tw q 1)).d 0 1) (kumT q U v)

def LeafKumEx : Prop := ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → ∃ γ, KumProp q u γ

def LeafKumUniq : Prop := ∀ (q : ℕ) [NeZero q] {X : Scheme.{0}} (u : (Γ(X, ⊤))ˣ), IsUnit (q : Γ(X, ⊤)) → ∀ γ δ,
  KumProp q u γ → KumProp q u δ → CohomologyClass.mk γ = CohomologyClass.mk δ

theorem units_map_comp {Y X U : Scheme.{0}} (x : U ⟶ Y) (f : Y ⟶ X) (u : (Γ(X, ⊤))ˣ) :
    Units.map (x ≫ f).appTop.hom.toMonoidHom u = Units.map x.appTop.hom.toMonoidHom (Units.map f.appTop.hom.toMonoidHom u) := by
  ext
  change (x ≫ f).appTop.hom (u : Γ(X, ⊤)) = x.appTop.hom (f.appTop.hom u)
  simp
  rfl

section Glue
variable (hE : LeafEvPull)
include hE

theorem ev_pcoc {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') {I : Cx R} {n : ℤ} (α : Cocycle ((chains R).obj E') I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (pcoc f α).1 p s h U x = ev α.1 p s h U (Sx.map f x) := hE R f α.1 p s h U x

theorem isAW_pull {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E E' : Spc} (f : E ⟶ E') {n m k : ℤ}
    (hk : n + m = k) {α : Cocycle ((chains R).obj E') I n} {β : Cocycle ((chains R).obj E') J m}
    {γ : Cocycle ((chains R).obj E') K k} (h : μ.IsAW hk α.1 β.1 γ.1) :
    μ.IsAW hk (pcoc f α).1 (pcoc f β).1 (pcoc f γ).1 := by
  intro N w hw U x
  refine (hE R f γ.1 N w hw U x).trans ((h N w hw U (Sx.map f x)).trans (Finset.sum_congr rfl fun p _ => ?_))
  rw [sub_map, sub_map, ev_pcoc hE, ev_pcoc hE]

theorem cup_nat (hA : LeafCupAW) (hS : LeafCupSpec) {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E E' : Spc}
    (f : E ⟶ E') {n m k : ℤ} (hk : n + m = k) (a : CohomologyClass ((chains R).obj E') I n)
    (b : CohomologyClass ((chains R).obj E') J m) :
    cpull ((chains R).map f) K k (μ.cup E' hk a b) =
      μ.cup E hk (cpull ((chains R).map f) I n a) (cpull ((chains R).map f) J m b) := by
  obtain ⟨α, rfl⟩ := a.mk_surjective
  obtain ⟨β, rfl⟩ := b.mk_surjective
  obtain ⟨γ, hγ⟩ := hA R μ E' hk α β
  have e1 : μ.cup E' hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ :=
    pick_spec (hS R μ E' hk) α β γ hγ
  have e2 : μ.cup E hk (CohomologyClass.mk (pcoc f α)) (CohomologyClass.mk (pcoc f β)) = CohomologyClass.mk (pcoc f γ) :=
    pick_spec (hS R μ E hk) _ _ _ (isAW_pull hE μ f hk hγ)
  rw [e1, cpull_mk, cpull_mk, cpull_mk, e2]

theorem one_eq (hX : LeafOneEx) (hU : LeafOneUniq) {q : ℕ} [NeZero q] {E : Spc} (h : Inv q E)
    (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0) (hα : OneProp q E α) : one q E = CohomologyClass.mk α := by
  obtain ⟨α0, hα0⟩ := hX q E h
  obtain ⟨β, hβ, hβp⟩ : ∃ β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0, CohomologyClass.mk β = one q E ∧ OneProp q E β :=
    pick_spec (P := fun c => ∃ β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0, CohomologyClass.mk β = c ∧ OneProp q E β)
      ⟨_, α0, rfl, hα0⟩
  rw [← hβ]
  exact hU q E h β α hβp hα

theorem c1_eq (hX : ChernClassExists) (hU : ChernClassUnique) {q : ℕ} [NeZero q] {E : Spc} (L : E ⟶ ofCat (glCat 1)) (h : Inv q E)
    (γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2) (hγ : IsChernClassCocycle q L γ) : c1 q L = CohomologyClass.mk γ := by
  obtain ⟨α0, hα0⟩ := hX q L h
  obtain ⟨β, hβ, hβp⟩ : ∃ β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, CohomologyClass.mk β = c1 q L ∧ IsChernClassCocycle q L β :=
    pick_spec (P := fun c => ∃ β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 1)) 2, CohomologyClass.mk β = c ∧ IsChernClassCocycle q L β)
      ⟨_, α0, rfl, hα0⟩
  rw [← hβ]
  exact hU q L h β γ hβp hγ

theorem kum_eq (hX : LeafKumEx) (hU : LeafKumUniq) {q : ℕ} [NeZero q] {X : Scheme.{0}} (u : (Γ(X, ⊤))ˣ) (h : IsUnit (q : Γ(X, ⊤)))
    (γ : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1) (hγ : KumProp q u γ) : kum q u = CohomologyClass.mk γ := by
  obtain ⟨α0, hα0⟩ := hX q u h
  obtain ⟨β, hβ, hβp⟩ : ∃ β : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      CohomologyClass.mk β = kum q u ∧ KumProp q u β :=
    pick_spec (P := fun c => ∃ β : Cocycle ((chains (ZMod q)).obj (sch.obj X)) (res _ (tw q 1)) 1,
      CohomologyClass.mk β = c ∧ KumProp q u β) ⟨_, α0, rfl, hα0⟩
  rw [← hβ]
  exact hU q u h β γ hβp hγ

end Glue

theorem goal_of (h1 : LeafEvPull) (h2 : LeafCupAW) (h3 : LeafCupSpec) (h4 : LeafOneEx) (h5 : LeafOneUniq) (h6 : ChernClassExists)
    (h7 : ChernClassUnique) (h8 : LeafKumEx) (h9 : LeafKumUniq) : LateralTheory.E.D2.LeafA6nat := by
  intro q _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro E E' f n m i j a b
    exact cup_nat h1 h2 h3 (twPair q i j) f rfl a b
  · intro E E' f h'
    obtain ⟨α, hα⟩ := h4 q E' h'
    rw [one_eq h1 h4 h5 h' α hα, pull_mk, one_eq h1 h4 h5 (inv_pull f h') (pcoc f α)]
    intro U x ζ
    exact (ev_pcoc h1 f α 0 0 _ U x).trans (hα U _ ζ)
  · intro E E' f L h'
    obtain ⟨γ, hγ⟩ := h6 q L h'
    rw [c1_eq h1 h6 h7 L h' γ hγ, pull_mk, c1_eq h1 h6 h7 (f ≫ L) (inv_pull f h') (pcoc f γ)]
    refine ⟨fun U x => ?_, fun U x v hv => ?_, fun U x v w hv hw => ?_⟩
    · exact (ev_pcoc h1 f γ 0 2 _ U x).trans (hγ.1 U _)
    · exact (ev_pcoc h1 f γ 1 1 _ U x).trans (hγ.2.1 U _ v hv)
    · refine (ev_pcoc h1 f γ 2 0 _ U x).trans (hγ.2.2 U _ v w ?_ ?_)
      · rw [sub_map]; exact hv
      · rw [sub_map]; exact hw
  · intro Y X f u hq
    have hq' : IsUnit (q : Γ(Y, ⊤)) := by simpa using hq.map f.appTop.hom
    obtain ⟨γ, hγ⟩ := h8 q u hq
    rw [kum_eq h1 h8 h9 u hq γ hγ, pull_mk, kum_eq h1 h8 h9 _ hq' (pcoc (sch.map f) γ)]
    refine ⟨fun U x => ?_, fun U x v hv => ?_⟩
    · exact (ev_pcoc h1 (sch.map f) γ 1 0 _ U x).trans (hγ.1 U (x ≫ f))
    · exact (ev_pcoc h1 (sch.map f) γ 0 1 _ U x).trans (hγ.2 U (x ≫ f) v (hv.trans (units_map_comp x f u).symm))

end LateralTheory.E.AlexanderWhitneyCupPullbackNaturality
