import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace GlobalTheory.CompanionTheory.OpenThick

variable {K : Type} [CommRing K]

section Pt

variable {X Y : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)}

abbrev Pt (q : X ⟶ Spec (CommRingCat.of K)) (B : Type) [CommRing B] : Type :=
  PtOver X q (Ideal.Quotient.mk (⊥ : Ideal K)) B

theorem pt_ext (V : X.Opens) {B : Type} [CommRing B] {y y' : Pt (V.ι ≫ q) B} (h1 : y.1.1 = y'.1.1)
    (h2 : y.1.2 ≫ V.ι = y'.1.2 ≫ V.ι) : y = y' :=
  Subtype.ext (Prod.ext h1 ((cancel_mono V.ι).1 h2))

def liftPt (V : X.Opens) {B : Type} [CommRing B] (y : Pt q B) (h : ⊤ ≤ y.1.2 ⁻¹ᵁ V) : Pt (V.ι ≫ q) B :=
  ⟨(y.1.1, IsOpenImmersion.lift V.ι y.1.2 (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact h (Set.mem_univ x))), by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]
    exact y.2⟩

theorem liftPt_fac (V : X.Opens) {B : Type} [CommRing B] (y : Pt q B) (h : ⊤ ≤ y.1.2 ⁻¹ᵁ V) :
    (liftPt V y h).1.2 ≫ V.ι = y.1.2 := IsOpenImmersion.lift_fac _ _ _

theorem liftPt_map (V : X.Opens) {B B' : CommRingCat.{0}} (φ : B ⟶ B') (y : Pt q B) (y' : Pt q B')
    (h : ⊤ ≤ y.1.2 ⁻¹ᵁ V) (h' : ⊤ ≤ y'.1.2 ⁻¹ᵁ V)
    (e : (ptFun X q (Ideal.Quotient.mk (⊥ : Ideal K))).map φ y = y') :
    (ptFun V.toScheme (V.ι ≫ q) (Ideal.Quotient.mk (⊥ : Ideal K))).map φ (liftPt V y h) = liftPt V y' h' := by
  subst e
  refine pt_ext V rfl ?_
  change (Spec.map φ ≫ (liftPt V y h).1.2) ≫ V.ι = (liftPt V _ h').1.2 ≫ V.ι
  rw [Category.assoc, liftPt_fac, liftPt_fac]
  rfl

theorem pt_id {Z : Scheme.{0}} {r : Z ⟶ Spec (CommRingCat.of K)} {B : Type} [CommRing B] (J : Ideal B) (hJ)
    (y : Pt r (B ⧸ J)) :
    (ptFun Z r (Ideal.Quotient.mk (⊥ : Ideal K))).map
      (CommRingCat.ofHom (Ideal.quotientMap J (RingHom.id B) hJ)) y = y := by
  have e : Ideal.quotientMap J (RingHom.id B) hJ = RingHom.id (B ⧸ J) := by
    ext
    rfl
  rw [e]
  exact congrFun (congrArg (fun t => (ConcreteCategory.hom t : _ → _))
    ((ptFun Z r (Ideal.Quotient.mk (⊥ : Ideal K))).map_id (CommRingCat.of (B ⧸ J)))) y

end Pt

section Thickenings

variable {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

abbrev InV (V : X.Opens) (T : Thick (smFun X q)) : Prop :=
  InU (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) V T

def smH {T T' : Thick (smFun X q)} (φ : T.B →+* T'.B) (comm : ∀ r, φ (T.i r) = T'.i r)
    (dp : IsDPMorphism T.δ T'.δ φ) (hle : T.J ≤ T'.J.comap φ)
    (hpt : (smFun X q).Pt.map (CommRingCat.ofHom (Ideal.quotientMap T'.J φ hle)) T.y = T'.y) : T ⟶ T' :=
  mkH (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (T := T) (T' := T') φ comm dp hle hpt

theorem sm_ext {T T' : Thick (smFun X q)} {f g : T ⟶ T'} (h : f.φ = g.φ) : f = g :=
  hom_ext (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (T := T) (T' := T') h

def liftT (V : X.Opens) (T : Thick (smFun X q)) (h : InV V T) : Thick (smFun V.toScheme (V.ι ≫ q)) :=
  mkT (γ := dividedPowersBot K) (p := 0) (q := V.ι ≫ q) (κ := Ideal.Quotient.mk ⊥) T.B T.i T.J T.δ T.adm T.compat
    (liftPt V T.y h) T.w

theorem inV_of {V : X.Opens} {s : ℕ} {T : Thick (smFun X q)} (h : KS q s {V} T) : InV V T := by
  obtain ⟨-, V', hV', hT⟩ := h
  obtain rfl := Set.mem_singleton_iff.1 hV'
  exact hT

variable (q) in

def mF (V : X.Opens) (s : ℕ) : (KS q s {V}).FullSubcategory ⥤ (KS (V.ι ≫ q) s {⊤}).FullSubcategory where
  obj T := ⟨liftT V T.obj (inV_of T.property), T.property.1, ⊤, rfl, fun _ _ => trivial⟩
  map {T T'} f := ObjectProperty.homMk (smH (T := liftT V T.obj (inV_of T.property)) (T' := liftT V T'.obj (inV_of T'.property))
    f.hom.φ f.hom.comm f.hom.dp f.hom.hle (liftPt_map V (CommRingCat.ofHom (Ideal.quotientMap T'.obj.J f.hom.φ f.hom.hle)) T.obj.y T'.obj.y (inV_of T.property) (inV_of T'.property) f.hom.pt))
  map_id _ := ObjectProperty.hom_ext _ (sm_ext rfl)
  map_comp _ _ := ObjectProperty.hom_ext _ (sm_ext rfl)

variable (q) in

def mV (V : X.Opens) (s a : ℕ) :
    CH.Mor ((KS (V.ι ≫ q) s {⊤}).ι ⋙ HT.grT (smFun V.toScheme (V.ι ≫ q)) a)
      ((KS q s {V}).ι ⋙ HT.grT (smFun X q) a) (RingHom.id K) where
  G := mF q V s
  τ T := LinearMap.id
  nat _ _ := rfl

end Thickenings

section Equivalence

variable {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem liftPt_unmap (V : X.Opens) {B B' : CommRingCat.{0}} (φ : B ⟶ B') (y : Pt q B) (y' : Pt q B')
    (h : ⊤ ≤ y.1.2 ⁻¹ᵁ V) (h' : ⊤ ≤ y'.1.2 ⁻¹ᵁ V)
    (e : (ptFun V.toScheme (V.ι ≫ q) (Ideal.Quotient.mk (⊥ : Ideal K))).map φ (liftPt V y h) = liftPt V y' h') :
    (ptFun X q (Ideal.Quotient.mk (⊥ : Ideal K))).map φ y = y' := by
  refine Subtype.ext (Prod.ext (congrArg (fun z : Pt (V.ι ≫ q) B' => z.1.1) e) ?_)
  have e2 := congrArg (fun z : Pt (V.ι ≫ q) B' => z.1.2 ≫ V.ι) e
  change (Spec.map φ ≫ (liftPt V y h).1.2) ≫ V.ι = (liftPt V y' h').1.2 ≫ V.ι at e2
  rw [Category.assoc, liftPt_fac, liftPt_fac] at e2
  exact e2

instance mF_faithful (V : X.Opens) (s : ℕ) : (mF q V s).Faithful where
  map_injective {T T'} f g e :=
    ObjectProperty.hom_ext _ (sm_ext (T := T.obj) (T' := T'.obj) (congrArg (fun t => t.hom.φ) e))

instance mF_full (V : X.Opens) (s : ℕ) : (mF q V s).Full where
  map_surjective {T T'} g :=
    ⟨ObjectProperty.homMk (smH (T := T.obj) (T' := T'.obj) g.hom.φ g.hom.comm g.hom.dp g.hom.hle
      (liftPt_unmap V (CommRingCat.ofHom (Ideal.quotientMap T'.obj.J g.hom.φ g.hom.hle)) T.obj.y T'.obj.y
        (inV_of T.property) (inV_of T'.property) g.hom.pt)),
      ObjectProperty.hom_ext _ (sm_ext rfl)⟩

theorem top_le_comp (V : X.Opens) {Z : Scheme.{0}} (z : Z ⟶ V.toScheme) : ⊤ ≤ (z ≫ V.ι) ⁻¹ᵁ V := by
  intro x _
  change (z ≫ V.ι) x ∈ V
  rw [Scheme.Hom.comp_apply]
  have hx : V.ι (z x) ∈ (V : Set X) := Scheme.Opens.range_ι V ▸ ⟨z x, rfl⟩
  exact hx

def pushPt (V : X.Opens) {B : Type} [CommRing B] (y : Pt (V.ι ≫ q) B) : Pt q B :=
  ⟨(y.1.1, y.1.2 ≫ V.ι), by
    rw [Category.assoc]
    exact y.2⟩

theorem lift_push (V : X.Opens) {B : Type} [CommRing B] (y : Pt (V.ι ≫ q) B) (h : ⊤ ≤ (pushPt V y).1.2 ⁻¹ᵁ V) :
    liftPt V (pushPt V y) h = y :=
  pt_ext V rfl (liftPt_fac V (pushPt V y) h)

def downT (V : X.Opens) (T : Thick (smFun V.toScheme (V.ι ≫ q))) : Thick (smFun X q) :=
  mkT (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T.B T.i T.J T.δ T.adm T.compat
    (pushPt V T.y) T.w

theorem down_inV (V : X.Opens) (T : Thick (smFun V.toScheme (V.ι ≫ q))) : InV V (downT V T) :=
  top_le_comp V _

def dnHom (V : X.Opens) (T : Thick (smFun V.toScheme (V.ι ≫ q))) (h : InV V (downT V T)) :
    liftT V (downT V T) h ⟶ T :=
  smH (T := liftT V (downT V T) h) (T' := T) (RingHom.id T.B) (fun _ => rfl) (DPMorphism.id T.δ).isDPMorphism
    (fun _ hx => hx) ((pt_id T.J _ _).trans (lift_push V T.y h))

def dnInv (V : X.Opens) (T : Thick (smFun V.toScheme (V.ι ≫ q))) (h : InV V (downT V T)) :
    T ⟶ liftT V (downT V T) h :=
  smH (T := T) (T' := liftT V (downT V T) h) (RingHom.id T.B) (fun _ => rfl) (DPMorphism.id T.δ).isDPMorphism
    (fun _ hx => hx) ((pt_id T.J _ _).trans (lift_push V T.y h).symm)

theorem ks_of {V : X.Opens} {s : ℕ} {T : Thick (smFun X q)} (h1 : TF 1 s T) (h2 : InV V T) : KS q s {V} T :=
  ⟨h1, V, rfl, h2⟩

def pushK (V : X.Opens) (s : ℕ) (T : (KS (V.ι ≫ q) s {⊤}).FullSubcategory) : (KS q s {V}).FullSubcategory :=
  ⟨downT V T.obj, ks_of T.property.1 (down_inV V T.obj)⟩

def pushIso (V : X.Opens) (s : ℕ) (T : (KS (V.ι ≫ q) s {⊤}).FullSubcategory) : (mF q V s).obj (pushK V s T) ≅ T where
  hom := ObjectProperty.homMk (dnHom V T.obj (inV_of (pushK V s T).property))
  inv := ObjectProperty.homMk (dnInv V T.obj (inV_of (pushK V s T).property))
  hom_inv_id := ObjectProperty.hom_ext _ (sm_ext rfl)
  inv_hom_id := ObjectProperty.hom_ext _ (sm_ext rfl)

instance mF_essSurj (V : X.Opens) (s : ℕ) : (mF q V s).EssSurj where
  mem_essImage T := ⟨pushK V s T, ⟨pushIso V s T⟩⟩

instance mF_equiv (V : X.Opens) (s : ℕ) : (mF q V s).IsEquivalence := { }

theorem mV_bij (V : X.Opens) (s a n : ℕ) : Function.Bijective ((mV q V s a).pull n) :=
  haveI : (mV q V s a).G.IsLeftAdjoint := inferInstanceAs (mF q V s).IsLeftAdjoint
  P.adj_mor (mV q V s a) (fun _ => Function.bijective_id) n

end Equivalence

section Natural

variable {X Y : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)}
  (u : X ⟶ Y) (hu : u ≫ p = q) (V : X.Opens) (W : Y.Opens) (h : V ≤ u ⁻¹ᵁ W)
  (hh : u.resLE W V h ≫ (W.ι ≫ p) = V.ι ≫ q)

theorem push_lift {B : CommRingCat.{0}} (y : Pt q B) (hV : ⊤ ≤ y.1.2 ⁻¹ᵁ V)
    (hW : ⊤ ≤ ((smMor u hu).pt.app B y : Pt p B).1.2 ⁻¹ᵁ W) :
    ((smMor (u.resLE W V h) hh).pt.app B (liftPt V y hV) : Pt (W.ι ≫ p) B) =
      liftPt W ((smMor u hu).pt.app B y) hW := by
  refine pt_ext W rfl ?_
  change ((liftPt V y hV).1.2 ≫ u.resLE W V h) ≫ W.ι = _
  rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, liftPt_fac, liftPt_fac]
  rfl

variable (s a : ℕ) (hG : ∀ T, KS q s {V} T → KS p s {W} ((pullM u hu a).G.obj T))
  (hG' : ∀ T, KS (V.ι ≫ q) s {⊤} T → KS (W.ι ≫ p) s {⊤} ((pullM (u.resLE W V h) hh a).G.obj T))

def etaN : (mV q V s a).G ⋙ (morU (pullM (u.resLE W V h) hh a) (U := KS (W.ι ≫ p) s {⊤}) (U' := KS (V.ι ≫ q) s {⊤}) hG').G ⟶
    (morU (pullM u hu a) (U := KS p s {W}) (U' := KS q s {V}) hG).G ⋙ (mV p W s a).G where
  app T := ObjectProperty.homMk (smH (RingHom.id _) (fun _ => rfl) (DPMorphism.id T.obj.δ).isDPMorphism (fun _ hx => hx)
    ((pt_id T.obj.J _ _).trans (push_lift u hu V W h hh T.obj.y (inV_of T.property) (inV_of (hG _ T.property)))))
  naturality _ _ _ := ObjectProperty.hom_ext _ (sm_ext rfl)

theorem mV_nat (n : ℕ) (x) :
    (mV q V s a).pull n ((morU (pullM (u.resLE W V h) hh a) (U := KS (W.ι ≫ p) s {⊤}) (U' := KS (V.ι ≫ q) s {⊤}) hG').pull n x) =
      (morU (pullM u hu a) (U := KS p s {W}) (U' := KS q s {V}) hG).pull n ((mV p W s a).pull n x) := by
  have e1 := (P.pull_comp (σ'' := RingHom.id K) (morU (pullM (u.resLE W V h) hh a) (U := KS (W.ι ≫ p) s {⊤})
    (U' := KS (V.ι ≫ q) s {⊤}) hG') (mV q V s a) n x).1
  have e2 := (P.pull_comp (σ'' := RingHom.id K) (mV p W s a) (morU (pullM u hu a) (U := KS p s {W}) (U' := KS q s {V}) hG) n x).1
  refine e1.symm.trans (Eq.trans ?_ e2)
  refine P.prism _ _ (etaN u hu V W h hh s a hG hG') (fun T z => ?_) n x
  obtain ⟨z, hz⟩ := z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  rfl

end Natural

theorem open_thick : ∀ (K : Type) [CommRing K], ∃ m : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s a : ℕ),
    CH.Mor ((KS (V.ι ≫ q) s {⊤}).ι ⋙ HT.grT (smFun V.toScheme (V.ι ≫ q)) a) ((KS q s {V}).ι ⋙ HT.grT (smFun X q) a)
      (RingHom.id K),
    (∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (s a n : ℕ), Function.Bijective ((m q V s a).pull n)) ∧
    ∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) (u : X ⟶ Y) (hu : u ≫ p = q)
      (V : X.Opens) (W : Y.Opens) (h : V ≤ u ⁻¹ᵁ W) (hh : u.resLE W V h ≫ (W.ι ≫ p) = V.ι ≫ q) (s a : ℕ)
      (hG : ∀ T, KS q s {V} T → KS p s {W} ((pullM u hu a).G.obj T))
      (hG' : ∀ T, KS (V.ι ≫ q) s {⊤} T → KS (W.ι ≫ p) s {⊤} ((pullM (u.resLE W V h) hh a).G.obj T)) (n : ℕ) x,
      (m q V s a).pull n ((morU (pullM (u.resLE W V h) hh a) (U := KS (W.ι ≫ p) s {⊤}) (U' := KS (V.ι ≫ q) s {⊤}) hG').pull n x) =
        (morU (pullM u hu a) (U := KS p s {W}) (U' := KS q s {V}) hG).pull n ((m p W s a).pull n x) :=
  fun K _ => ⟨@fun X q V s a => mV q V s a, @fun X q V s a n => mV_bij V s a n,
    @fun X Y q p u hu V W h hh s a hG hG' n x => mV_nat u hu V W h hh s a hG hG' n x⟩

end GlobalTheory.CompanionTheory.OpenThick
