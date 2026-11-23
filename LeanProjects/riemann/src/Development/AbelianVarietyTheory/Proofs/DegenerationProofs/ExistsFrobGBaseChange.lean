import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.FrobField

def powHom (R : Type) [CommRing R] (p r : ℕ) (hp : p.Prime) (h : (p : R) = 0) : R →+* R where
  toFun x := x ^ p ^ r
  map_one' := one_pow _
  map_mul' x y := mul_pow _ _ _
  map_zero' := zero_pow (pow_ne_zero _ hp.ne_zero)
  map_add' x y := by
    obtain ⟨c, hc⟩ := exists_add_pow_prime_pow_eq hp x y r
    rw [hc, h]; simp

theorem cast_zero {X : Scheme.{0}} {p : ℕ} (h : (p : Γ(X, ⊤)) = 0) (U : X.Opens) : (p : Γ(X, U)) = 0 := by
  have := congrArg (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom h
  rwa [map_natCast, map_zero] at this

theorem cast_zero_of_hom {X Y : Scheme.{0}} (f : X ⟶ Y) {p : ℕ} (h : (p : Γ(Y, ⊤)) = 0) :
    (p : Γ(X, ⊤)) = 0 := by
  have := congrArg f.appTop.hom h
  rwa [map_natCast, map_zero] at this

def absPre (X : Scheme.{0}) (p r : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) :
    X.toPresheafedSpace.Hom X.toPresheafedSpace where
  base := 𝟙 _
  c := { app := fun U => CommRingCat.ofHom (powHom (X.presheaf.obj U) p r hp (cast_zero h U.unop))
         naturality := fun U V i => by
           ext x
           exact (map_pow (X.presheaf.map i).hom x _).symm }

def absFrob (X : Scheme.{0}) (p r : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) : X ⟶ X :=
  ⟨⟨absPre X p r hp h, fun x => ⟨fun a ha => by
    obtain ⟨U, hU, s, rfl⟩ := X.presheaf.exists_germ_eq (x := x) a
    have e := PresheafedSpace.stalkMap_germ_apply (absPre X p r hp h) U x hU s
    erw [e] at ha
    have e2 : (X.presheaf.germ U x hU).hom (s ^ p ^ r) = (X.presheaf.germ U x hU).hom s ^ p ^ r :=
      map_pow _ _ _
    have ha' : IsUnit ((X.presheaf.germ U x hU).hom (s ^ p ^ r)) := ha
    rw [e2] at ha'
    exact (isUnit_pow_iff (pow_ne_zero _ hp.ne_zero)).1 ha'⟩⟩⟩

theorem absFrob_preimage (X : Scheme.{0}) (p r : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) (U : X.Opens) :
    absFrob X p r hp h ⁻¹ᵁ U = U := rfl

theorem absFrob_appLE (X : Scheme.{0}) (p r : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) (U : X.Opens)
    (e : U ≤ absFrob X p r hp h ⁻¹ᵁ U) (f : Γ(X, U)) :
    ((absFrob X p r hp h).appLE U U e).hom f = f ^ p ^ r := by
  have := Scheme.Hom.appLE_eq_app (absFrob X p r hp h) (U := U)
  exact congrArg (fun φ => φ.hom f) this

theorem absFrob_nat {X Y : Scheme.{0}} (f : X ⟶ Y) (p r : ℕ) (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)
    (hY : (p : Γ(Y, ⊤)) = 0) : absFrob X p r hp hX ≫ f = f ≫ absFrob Y p r hp hY := by
  refine Scheme.Hom.ext rfl fun U => ?_
  ext x
  have e : ∀ (V : X.Opens) (i : Opposite.op V ⟶ Opposite.op V) (y : Γ(X, V)),
      (X.presheaf.map i).hom y = y := by
    intro V i y
    rw [Subsingleton.elim i (𝟙 _), CategoryTheory.Functor.map_id]; rfl
  exact (e (f ⁻¹ᵁ U) _ _).trans (map_pow (f.app U).hom x _).symm

theorem absFrob_spec (k : Type) [CommRing k] (p r : ℕ) (hp : p.Prime) (h : (p : Γ(Sp k, ⊤)) = 0)
    (τ : k →+* k) (hτ : ∀ c, τ c = c ^ p ^ r) : absFrob (Sp k) p r hp h = spMap τ := by
  apply ext_of_isAffine
  rw [← cancel_epi (Scheme.ΓSpecIso (.of k)).inv]
  rw [← Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom τ)]
  ext c
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, hτ, map_pow]
  rfl

def Q {X : Scheme.{0}} (φ : X ⟶ X) (n : ℕ) (U : X.Opens) (f : Γ(X, U)) : Prop :=
  ∃ h : U = φ ⁻¹ᵁ U, (φ.appLE U U h.le).hom f = f ^ n

theorem Q.comp {X : Scheme.{0}} {φ ψ : X ⟶ X} {n n' : ℕ} {U : X.Opens} {f : Γ(X, U)}
    (a : Q φ n U f) (b : Q ψ n' U f) : Q (φ ≫ ψ) (n * n') U f := by
  obtain ⟨h, e⟩ := a
  obtain ⟨h', e'⟩ := b
  refine ⟨by rw [Scheme.Hom.comp_preimage, ← h', ← h], ?_⟩
  rw [← Scheme.Hom.appLE_comp_appLE φ ψ U U U h'.le h.le, CommRingCat.hom_comp, RingHom.comp_apply, e',
    map_pow, e, pow_mul]

theorem Q.id {X : Scheme.{0}} (U : X.Opens) (f : Γ(X, U)) : Q (𝟙 X) 1 U f := by
  refine ⟨rfl, ?_⟩
  simp [Scheme.Hom.appLE]
  exact GlobalTheory.AbLaw.rs_self (X := X) le_rfl f

theorem Q.pow {X : Scheme.{0}} {F : End X} {q m : ℕ} {U : X.Opens} {f : Γ(X, U)}
    (a : Q (show X ⟶ X from F ^ m) (q ^ m) U f) (j : ℕ) :
    Q (show X ⟶ X from F ^ (m * j)) (q ^ (m * j)) U f := by
  induction j with
  | zero => simpa using Q.id U f
  | succ j ih =>
    have := a.comp ih
    rw [Nat.mul_succ, pow_add, pow_add, mul_comm (q ^ (m * j))]
    exact this

def Good {X : Scheme.{0}} (F : End X) (q : ℕ) (U : X.Opens) (f : Γ(X, U)) : Prop :=
  ∃ m, 1 ≤ m ∧ Q (show X ⟶ X from F ^ m) (q ^ m) U f

theorem Good.two {X : Scheme.{0}} {F : End X} {q : ℕ} {U V : X.Opens} {f : Γ(X, U)} {g : Γ(X, V)}
    (a : Good F q U f) (b : Good F q V g) :
    ∃ m, 1 ≤ m ∧ Q (show X ⟶ X from F ^ m) (q ^ m) U f ∧ Q (show X ⟶ X from F ^ m) (q ^ m) V g := by
  obtain ⟨m, hm, a⟩ := a
  obtain ⟨n, hn, b⟩ := b
  refine ⟨m * n, Nat.mul_pos hm hn, a.pow n, ?_⟩
  rw [mul_comm]; exact b.pow m

theorem Q.res {X : Scheme.{0}} {φ : X ⟶ X} {n : ℕ} {U V : X.Opens} {f : Γ(X, U)}
    (a : Q φ n U f) (i : V ≤ U) (h : V = φ ⁻¹ᵁ V) : Q φ n V ((X.presheaf.map (homOfLE i).op).hom f) := by
  obtain ⟨h', e⟩ := a
  refine ⟨h, ?_⟩
  rw [← map_pow, ← e, ← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp,
    ← CommRingCat.hom_comp, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem Good.sup {X : Scheme.{0}} {F : End X} {q : ℕ} {U V W : X.Opens} (f : Γ(X, W))
    (hU : U ≤ W) (hV : V ≤ W) (hW : W = U ⊔ V)
    (a : Good F q U ((X.presheaf.map (homOfLE hU).op).hom f))
    (b : Good F q V ((X.presheaf.map (homOfLE hV).op).hom f)) : Good F q W f := by
  obtain ⟨m, hm, ⟨h, e⟩, ⟨h', e'⟩⟩ := a.two b
  have hh : W = (show X ⟶ X from F ^ m) ⁻¹ᵁ W := by
    rw [hW, Scheme.Hom.preimage_sup, ← h, ← h']
  refine ⟨m, hm, hh, ?_⟩
  refine X.sheaf.eq_of_locally_eq₂ (homOfLE hU) (homOfLE hV) hW.le _ _ ?_ ?_
  · change (X.presheaf.map (homOfLE hU).op).hom _ = (X.presheaf.map (homOfLE hU).op).hom _
    rw [map_pow, ← e, ← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp,
      ← CommRingCat.hom_comp, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]
  · change (X.presheaf.map (homOfLE hV).op).hom _ = (X.presheaf.map (homOfLE hV).op).hom _
    rw [map_pow, ← e', ← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp,
      ← CommRingCat.hom_comp, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem good_bot {X : Scheme.{0}} (F : End X) (q : ℕ) (f : Γ(X, ⊥)) : Good F q ⊥ f :=
  ⟨1, le_rfl, rfl, Subsingleton.elim _ _⟩

theorem Good.basic {X : Scheme.{0}} {F : End X} {q : ℕ} (hq : 0 < q) {U : X.Opens} (hU : IsAffineOpen U)
    (H : ∀ f, Good F q U f) (g : Γ(X, U)) (f : Γ(X, X.basicOpen g)) : Good F q (X.basicOpen g) f := by
  have := hU.isLocalization_basicOpen g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g f
  obtain ⟨m, hm, qa, qg⟩ := (H a).two (H g)
  have hb : X.basicOpen g = (show X ⟶ X from F ^ m) ⁻¹ᵁ X.basicOpen g := by
    obtain ⟨h, e⟩ := qg
    have h1 := Scheme.basicOpen_appLE (show X ⟶ X from F ^ m) U U h.le g
    erw [e] at h1
    rw [Scheme.basicOpen_pow _ _ (pow_pos hq m)] at h1
    refine h1.trans (inf_eq_right.2 ?_)
    exact ((show X ⟶ X from F ^ m).preimage_mono (X.basicOpen_le g)).trans h.ge
  obtain ⟨_, ea⟩ := qa.res (X.basicOpen_le g) hb
  obtain ⟨_, eg⟩ := qg.res (X.basicOpen_le g) hb
  refine ⟨m, hm, hb, ?_⟩
  change _ = algebraMap Γ(X, U) Γ(X, X.basicOpen g) a ^ _ at ea
  change _ = algebraMap Γ(X, U) Γ(X, X.basicOpen g) g ^ _ at eg
  have hu : IsUnit (algebraMap Γ(X, U) Γ(X, X.basicOpen g) g) := IsLocalization.Away.algebraMap_isUnit g
  have h2 := congrArg ((show X ⟶ X from F ^ m).appLE _ _ hb.le).hom ha
  rw [map_mul, map_pow] at h2
  erw [ea, eg] at h2
  rw [← ha, mul_pow, ← pow_mul, ← pow_mul, mul_comm n] at h2
  exact (hu.pow _).mul_right_cancel h2

theorem good_of_cover {X : Scheme.{0}} {F : End X} {q : ℕ} (hq : 0 < q)
    (H : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧ ∀ f, Good F q U f)
    (U : X.Opens) (hU : IsCompact (U : Set X)) (f : Γ(X, U)) : Good F q U f := by
  have key : ∃ V : Set X, (U : Set X) ⊆ V ∧ ∃ W : X.Opens, (W : Set X) = V ∧ W ≤ U ∧ ∀ f, Good F q W f := by
    refine hU.induction_on (p := fun s => ∃ V : Set X, s ⊆ V ∧ ∃ W : X.Opens, (W : Set X) = V ∧ W ≤ U ∧
      ∀ f, Good F q W f) ⟨∅, le_rfl, ⊥, rfl, bot_le, good_bot F q⟩ ?_ ?_ ?_
    · rintro s t hst ⟨V, hV, h⟩
      exact ⟨V, hst.trans hV, h⟩
    · rintro s t ⟨_, hs, V, rfl, hV, gV⟩ ⟨_, ht, W, rfl, hW, gW⟩
      exact ⟨_, Set.union_subset_union hs ht, V ⊔ W, rfl, sup_le hV hW,
        fun f => Good.sup f le_sup_left le_sup_right rfl (gV _) (gW _)⟩
    · intro x hx
      obtain ⟨V, hxV, hV, gV⟩ := H x
      obtain ⟨g, hg, hxg⟩ := hV.exists_basicOpen_le ⟨x, hx⟩ hxV
      exact ⟨_, mem_nhdsWithin_of_mem_nhds ((X.basicOpen g).isOpen.mem_nhds hxg), _, le_rfl,
        X.basicOpen g, rfl, hg, Good.basic hq hV gV g⟩
  obtain ⟨_, h1, W, rfl, h2, g⟩ := key
  obtain rfl : U = W := le_antisymm h1 h2
  exact g f

def goodSubring {X : Scheme.{0}} (F : End X) (p r : ℕ) (hp : p.Prime) (U : X.Opens)
    (hc : (p : Γ(X, U)) = 0) (h : U = (show X ⟶ X from F) ⁻¹ᵁ U) : Subring Γ(X, U) where
  carrier := {f | Good F (p ^ r) U f}
  mul_mem' := fun a b => by
    obtain ⟨m, hm, ⟨h, e⟩, ⟨h', e'⟩⟩ := Good.two a b
    exact ⟨m, hm, h, by rw [map_mul, e, e', mul_pow]⟩
  add_mem' := fun {x y} a b => by
    obtain ⟨m, hm, ⟨h, e⟩, ⟨h', e'⟩⟩ := Good.two a b
    refine ⟨m, hm, h, ?_⟩
    rw [map_add, e, e', ← pow_mul]
    exact (map_add (powHom _ p (r * m) hp hc) x y).symm
  one_mem' := ⟨1, le_rfl, by rw [pow_one]; exact h, by rw [map_one, one_pow]⟩
  zero_mem' := ⟨1, le_rfl, by rw [pow_one]; exact h, by
    rw [map_zero, zero_pow (pow_ne_zero _ (pow_ne_zero _ hp.ne_zero))]⟩
  neg_mem' := fun {x} a => by
    obtain ⟨m, hm, h, e⟩ := a
    refine ⟨m, hm, h, ?_⟩
    rw [map_neg, e, ← pow_mul]
    exact (map_neg (powHom _ p (r * m) hp hc) x).symm

theorem appLE_congr_hom {X Y : Scheme.{0}} {φ ψ : X ⟶ Y} (e : φ = ψ) (V : Y.Opens) (U : X.Opens)
    (h : U ≤ φ ⁻¹ᵁ V) (h' : U ≤ ψ ⁻¹ᵁ V) : φ.appLE V U h = ψ.appLE V U h' := by
  subst e; rfl

theorem good_of_isPullback {X G S T : Scheme.{0}} [IsAffine S] [IsAffine T] {g : X ⟶ G} {s : X ⟶ T}
    {a : G ⟶ S} {b : T ⟶ S} (H : IsPullback g s a b) (p r : ℕ) (hp : p.Prime) (hc : (p : Γ(X, ⊤)) = 0)
    (hT : ∀ c : Γ(T, ⊤), ∃ m, 1 ≤ m ∧ c ^ ((p ^ r) ^ m) = c) (F : End X)
    (hg : (show X ⟶ X from F) ≫ g = absFrob X p r hp hc ≫ g) (hs : (show X ⟶ X from F) ≫ s = s)
    (U : X.Opens) (hU : IsCompact (U : Set X)) (f : Γ(X, U)) : Good F (p ^ r) U f := by
  refine good_of_cover (pow_pos hp.pos r) (fun x => ?_) U hU f
  obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := G.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (g x)) isOpen_univ
  have : IsAffineHom b := inferInstance
  have : IsAffineHom g := MorphismProperty.of_isPullback H.flip this
  refine ⟨g ⁻¹ᵁ V, hx, IsAffineOpen.preimage hV g, fun f => ?_⟩
  have hF : g ⁻¹ᵁ V = (show X ⟶ X from F) ⁻¹ᵁ g ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, hg]; rfl
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := V) (UY := g ⁻¹ᵁ V) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
    (isAffineOpen_top _) hV)
  have hle : ⊤ ≤ goodSubring F p r hp _ (cast_zero hc _) hF := by
    rw [← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨c, rfl⟩)
    · refine ⟨1, le_rfl, ?_⟩
      rw [pow_one, pow_one]
      refine ⟨hF, ?_⟩
      have e1 := Scheme.Hom.appLE_comp_appLE (show X ⟶ X from F) g V (g ⁻¹ᵁ V) (g ⁻¹ᵁ V) le_rfl hF.le
      have e2 := Scheme.Hom.appLE_comp_appLE (absFrob X p r hp hc) g V (g ⁻¹ᵁ V) (g ⁻¹ᵁ V) le_rfl le_rfl
      have e3 := (e1.trans (appLE_congr_hom hg _ _ _ _)).trans e2.symm
      exact (congrArg (fun φ => φ.hom y) e3).trans (absFrob_appLE X p r hp hc _ _ _)
    · obtain ⟨m, hm, hc'⟩ := hT c
      have h1 : ∀ n : ℕ, (show X ⟶ X from F ^ n) ≫ s = s ∧
          g ⁻¹ᵁ V = (show X ⟶ X from F ^ n) ⁻¹ᵁ g ⁻¹ᵁ V := by
        intro n
        induction n with
        | zero => exact ⟨Category.id_comp _, rfl⟩
        | succ n ih =>
          rw [pow_succ]
          change ((show X ⟶ X from F) ≫ (show X ⟶ X from F ^ n)) ≫ s = s ∧
            g ⁻¹ᵁ V = ((show X ⟶ X from F) ≫ (show X ⟶ X from F ^ n)) ⁻¹ᵁ g ⁻¹ᵁ V
          rw [Category.assoc, ih.1, hs, Scheme.Hom.comp_preimage, ← ih.2, ← hF]
          exact ⟨rfl, rfl⟩
      refine ⟨m, hm, (h1 m).2, ?_⟩
      have e1 := Scheme.Hom.appLE_comp_appLE (show X ⟶ X from F ^ m) s ⊤ (g ⁻¹ᵁ V) (g ⁻¹ᵁ V) le_top
        (h1 m).2.le
      have e3 := e1.trans (appLE_congr_hom (h1 m).1 _ _ _ le_top)
      refine (congrArg (fun φ => φ.hom c) e3).trans ?_
      change (s.appLE ⊤ (g ⁻¹ᵁ V) le_top).hom c = (s.appLE ⊤ (g ⁻¹ᵁ V) le_top).hom c ^ _
      rw [← map_pow, hc']
  exact hle (Subring.mem_top f)

theorem cast_zero_sp (k : Type) [CommRing k] {p : ℕ} (h : (p : k) = 0) : (p : Γ(Sp k, ⊤)) = 0 := by
  have := congrArg (Scheme.ΓSpecIso (.of k)).inv.hom h
  rwa [map_natCast, map_zero] at this

section Rel
variable {W k : Type} [CommRing W] [CommRing k] (ρ : W →+* k) (p r : ℕ) (hp : p.Prime) (hk : (p : k) = 0)
  (hρ : ∀ w, ρ w ^ (p ^ r) = ρ w)

include hρ in
theorem absFrob_comp_spMap : absFrob (Sp k) p r hp (cast_zero_sp k hk) ≫ spMap ρ = spMap ρ := by
  rw [absFrob_spec k p r hp _ (powHom k p r hp hk) (fun _ => rfl), ← Spec.map_comp]
  congr 1
  ext w
  exact hρ w

def relLeft (G : Over (Sp W)) : pullback G.hom (spMap ρ) ⟶ pullback G.hom (spMap ρ) :=
  pullback.lift (absFrob _ p r hp (cast_zero_of_hom (pullback.snd _ _) (cast_zero_sp k hk)) ≫ pullback.fst _ _)
    (pullback.snd _ _) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc,
        absFrob_nat _ p r hp _ (cast_zero_sp k hk), Category.assoc, absFrob_comp_spMap ρ p r hp hk hρ])

def relNat : Over.pullback (spMap ρ) ⟶ Over.pullback (spMap ρ) where
  app G := Over.homMk (relLeft ρ p r hp hk hρ G) (pullback.lift_snd _ _ _)
  naturality G G' φ := by
    ext1
    apply pullback.hom_ext
    · simp only [Over.comp_left, Over.homMk_left, relLeft, Category.assoc, pullback.lift_fst,
        Over.pullback_map_left]
      erw [pullback.lift_fst_assoc]
      rw [← Category.assoc]
      erw [← absFrob_nat (X := pullback G.hom (spMap ρ)) (Y := pullback G'.hom (spMap ρ)) _ p r hp
        (cast_zero_of_hom (pullback.snd G.hom (spMap ρ)) (cast_zero_sp k hk))]
      erw [Category.assoc, pullback.lift_fst, Category.assoc]
    · simp only [Over.comp_left, Over.homMk_left, relLeft, Category.assoc, Over.pullback_map_left]
      erw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]

end Rel

theorem isMonHom_app {C D : Type*} [Category C] [Category D] [CartesianMonoidalCategory C]
    [CartesianMonoidalCategory D] (P : C ⥤ D) [P.Monoidal] (α : P ⟶ P) (G : C) [MonObj G] :
    IsMonHom (α.app G) where
  one_hom := by
    rw [Functor.obj.η_def, Category.assoc, α.naturality, ← Category.assoc, NatTrans.IsMonoidal.unit]
  mul_hom := by
    rw [Functor.obj.μ_def, Category.assoc, α.naturality, ← Category.assoc, NatTrans.IsMonoidal.tensor,
      Category.assoc]

theorem over_pow_left {S : Scheme.{0}} {G : Over S} (F : End G) (m : ℕ) :
    (show G ⟶ G from F ^ m).left = (show G.left ⟶ G.left from
      (show End G.left from (show G ⟶ G from F).left) ^ m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ, pow_succ, End.mul_def, End.mul_def]
    exact (Over.comp_left _ _ _ _ _).trans (congrArg _ ih)

end GlobalTheory.SS.FrobField

namespace GlobalTheory.SS
open FrobField

theorem exists_frobG_baseChange : ∀ (W k : Type) [CommRing W] [Field k] (ρ : W →+* k) (p r : ℕ) [Fact p.Prime] [CharP k p], 1 ≤ r → (∀ w, ρ w ^ (p ^ r) = ρ w) → (∀ c : k, ∃ m, 1 ≤ m ∧ c ^ ((p ^ r) ^ m) = c) → ∀ (G : Over (Sp W)) [GrpObj G], SmConn G → ∃ F : End ((Over.pullback (spMap ρ)).obj G), FrobG _ F (p ^ r) ∧ ∀ (x : 𝟙_ (Over (Sp k)) ⟶ (Over.pullback (spMap ρ)).obj G) (τ : k →+* k), (∀ c, τ c = c ^ (p ^ r)) → (x ≫ (show (Over.pullback (spMap ρ)).obj G ⟶ (Over.pullback (spMap ρ)).obj G from F)).left ≫ pullback.fst G.hom (spMap ρ) = spMap τ ≫ x.left ≫ pullback.fst G.hom (spMap ρ) := by
  intro W k _ _ ρ p r hp _ _ hρ hfin G _ _
  have hk : (p : k) = 0 := CharP.cast_eq_zero k p
  refine ⟨(relNat ρ p r hp.out hk hρ).app G, ⟨isMonHom_app _ _ G, fun U hU f => ?_⟩, fun x τ hτ => ?_⟩
  · obtain ⟨m, hm, h⟩ := good_of_isPullback (IsPullback.of_hasPullback G.hom (spMap ρ)) p r hp.out
      (cast_zero_of_hom (pullback.snd _ _) (cast_zero_sp k hk)) (fun c => by
        obtain ⟨m, hm, h⟩ := hfin ((Scheme.ΓSpecIso (.of k)).hom.hom c)
        refine ⟨m, hm, (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.injective ?_⟩
        rw [map_pow]; exact h)
      (relLeft ρ p r hp.out hk hρ G) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) U hU.isCompact f
    refine ⟨m, hm, ?_⟩
    have e := over_pow_left ((relNat ρ p r hp.out hk hρ).app G) m
    exact (congrArg (fun φ => Q φ ((p ^ r) ^ m) U f) e).mpr h
  · have e := absFrob_nat (show Sp k ⟶ pullback G.hom (spMap ρ) from x.left) p r hp.out (cast_zero_sp k hk)
      (cast_zero_of_hom (pullback.snd _ _) (cast_zero_sp k hk))
    rw [absFrob_spec k p r hp.out _ τ hτ] at e
    have e2 : relLeft ρ p r hp.out hk hρ G ≫ pullback.fst _ _ = _ := pullback.lift_fst _ _ _
    change ((show Sp k ⟶ pullback G.hom (spMap ρ) from x.left) ≫ relLeft ρ p r hp.out hk hρ G) ≫ _ = _
    rw [Category.assoc, e2, ← Category.assoc, ← e, Category.assoc]

end GlobalTheory.SS
end
