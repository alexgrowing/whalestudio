import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfTorusBased
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoGenericOfDenseFibres
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PullPullAndSplitPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusCutByInvariantRatiosField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ.GenericTorus
open GlobalTheory.ZJ.SplitPull

theorem exists_zeroScheme (X : Scheme.{0}) (W : X.Opens) (hW : IsAffineOpen W) {J : Type} (f : J → Γ(X, W)) :
    ∃ (Z : Scheme.{0}) (_ : IsAffine Z) (κ : Z ⟶ X) (_ : IsImmersion κ), ∀ (Y : Scheme.{0}) (k : Y ⟶ X),
      (∃ h : ⊤ ≤ k ⁻¹ᵁ W, ∀ j, (k.appLE W ⊤ h).hom (f j) = 0) ↔ ∃ l, k = l ≫ κ := by
  let I : Ideal Γ(X, W) := Ideal.span (Set.range f)
  let q : Γ(X, W) ⟶ CommRingCat.of (Γ(X, W) ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
  have : IsClosedImmersion (Spec.map q) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨_, inferInstance, Spec.map q ≫ hW.fromSpec, inferInstance, fun Y k => ⟨?_, ?_⟩⟩
  · rintro ⟨h, hf⟩
    let φ : CommRingCat.of (Γ(X, W) ⧸ I) ⟶ Γ(Y, ⊤) := CommRingCat.ofHom (Ideal.Quotient.lift I (k.appLE W ⊤ h).hom
      fun a ha => (Ideal.span_le (I := RingHom.ker (k.appLE W ⊤ h).hom)).2 (by rintro _ ⟨j, rfl⟩; exact hf j) ha)
    refine ⟨Y.topIso.inv ≫ (⊤ : Y.Opens).toSpecΓ ≫ Spec.map φ, ?_⟩
    have e : q ≫ φ = k.appLE W ⊤ h := rfl
    rw [Category.assoc, Category.assoc, ← Spec.map_comp_assoc, e, Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc,
      IsAffineOpen.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι]
    simp
  · rintro ⟨l, rfl⟩
    have h0 : ⊤ ≤ hW.fromSpec ⁻¹ᵁ W := hW.fromSpec_preimage_self.ge
    have h1 : ⊤ ≤ (l ≫ Spec.map q ≫ hW.fromSpec) ⁻¹ᵁ W := fun x _ => h0 (Set.mem_univ _)
    refine ⟨h1, fun j => ?_⟩
    rw [← appTop_appLE (l ≫ Spec.map q) hW.fromSpec _ (Category.assoc _ _ _).symm W h0 h1]
    have e : hW.fromSpec.appLE W ⊤ h0 = (Scheme.ΓSpecIso Γ(X, W)).inv := by
      rw [Scheme.Hom.appLE, hW.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
      exact (congrArg (_ ≫ (Spec Γ(X, W)).presheaf.map ·) (Subsingleton.elim _ (𝟙 _))).trans (by simp)
    have e2 := congrArg (fun g => g.hom (f j)) (Scheme.ΓSpecIso_inv_naturality q)
    have e3 : q.hom (f j) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨j, rfl⟩)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, e3, map_zero] at e2
    rw [e, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, ← e2, map_zero]

section
variable {S : Scheme.{0}} {H : Over S} [GrpObj H] (C : Charts H.left) {d : ℕ} (a : {i // C.wt i = C.c₀})
  (j : Fin d → C.I)

def Rel {Y : Over S} (k : Y ⟶ H) (s : Y ⟶ splitTorus S (Fin d → ℤ)) : Prop :=
  ∀ (n : Fin d) (h : ⊤ ≤ k.left ⁻¹ᵁ C.W a) (h₁ : ⊤ ≤ (1 : Y ⟶ H).left ⁻¹ᵁ C.W a),
    (k.left.appLE _ ⊤ h).hom (C.r a (j n)) =
      s.left.appTop.hom (charUnit S (Fin d → ℤ) (Pi.single n 1)).val *
        ((1 : Y ⟶ H).left.appLE _ ⊤ h₁).hom (C.r a (j n))

def GraphRep {K₀ K₁ : Over S} (κ : K₀ ⟶ H) (p : K₁ ⟶ K₀) (u : K₁ ⟶ splitTorus S (Fin d → ℤ)) : Prop :=
  Mono κ ∧ (∀ (Y : Over S) (k : Y ⟶ H), C.InK a k ↔ ∃ l, k = l ≫ κ) ∧
    (∀ (Y : Over S) (m m' : Y ⟶ K₁), m ≫ p = m' ≫ p → m ≫ u = m' ≫ u → m = m') ∧
    ∀ (Y : Over S) (l : Y ⟶ K₀) (s : Y ⟶ splitTorus S (Fin d → ℤ)),
      Rel C a j (l ≫ κ) s ↔ ∃ m, m ≫ p = l ∧ m ≫ u = s

theorem one_left_eq (Y : Over S) : (1 : Y ⟶ H).left = Y.hom ≫ eSec H := by
  rw [Hom.one_def, Over.comp_left]
  rfl

variable {C a j}

theorem Rel.unique {c : Fin d → C.Cl} (hb : C.Based c a j) {Y : Over S} {k : Y ⟶ H} (hk : C.InK a k)
    {s s' : Y ⟶ splitTorus S (Fin d → ℤ)} (hs : Rel C a j k s) (hs' : Rel C a j k s') : s = s' := by
  obtain ⟨h, h₁, -⟩ := hk
  apply (splitTorusPointsEquiv S (Fin d → ℤ) Y).injective
  have key : ∀ n, splitTorusPointsEquiv S (Fin d → ℤ) Y s (Multiplicative.ofAdd (Pi.single n 1)) =
      splitTorusPointsEquiv S (Fin d → ℤ) Y s' (Multiplicative.ofAdd (Pi.single n 1)) := by
    intro n
    have hu : IsUnit (((1 : Y ⟶ H).left.appLE _ ⊤ h₁).hom (C.r a (j n))) := by
      have b := Scheme.basicOpen_appLE (1 : Y ⟶ H).left ⊤ _ h₁ (C.r a (j n))
      refine RingedSpace.isUnit_of_isUnit_germ _ _ _ fun y hy => ?_
      refine (Scheme.mem_basicOpen _ _ y hy).1 (b.ge ⟨hy, ?_⟩)
      rw [one_left_eq]
      exact (hb.2 n).2 (Set.mem_univ _)
    apply Units.ext
    rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val]
    exact hu.mul_right_cancel ((hs n h h₁).symm.trans (hs' n h h₁))
  apply MonoidHom.toAdditiveRight.injective
  refine AddMonoidHom.functions_ext' _ _ _ fun n => AddMonoidHom.ext_int ?_
  exact congrArg Additive.ofMul (key n)

variable {K₀ K₁ : Over S} {κ : K₀ ⟶ H} {p : K₁ ⟶ K₀} {u : K₁ ⟶ splitTorus S (Fin d → ℤ)}

theorem GraphRep.isIso {c : Fin d → C.Cl} (hb : C.Based c a j) (hr : GraphRep C a j κ p u)
    {i : splitTorus S (Fin d → ℤ) ⟶ H} (hi : C.KerIs a j i) : IsIso p ∧ IsIso u := by
  obtain ⟨mκ, hκ, hj, hp⟩ := hr
  obtain ⟨mi, hi, hi'⟩ := hi
  have rel : ∀ (Y : Over S) (m : Y ⟶ K₁), Rel C a j ((m ≫ p) ≫ κ) (m ≫ u) :=
    fun Y m => (hp Y _ _).2 ⟨m, rfl, rfl⟩
  have fac : ∀ (Y : Over S) (m : Y ⟶ K₁), (m ≫ p) ≫ κ = (m ≫ u) ≫ i := by
    intro Y m
    have hk := (hκ Y _).2 ⟨m ≫ p, rfl⟩
    obtain ⟨t, ht⟩ := (hi Y _).1 hk
    have h1 : Rel C a j ((m ≫ p) ≫ κ) t := by rw [ht]; exact hi' Y t
    rw [ht, Rel.unique hb hk h1 (rel Y m)]
  constructor
  · refine isIso_of_yoneda_map_bijective _ fun Y => ⟨fun m m' e => hj Y m m' e ?_, fun l => ?_⟩
    · rw [← cancel_mono i, ← fac, ← fac]
      exact congrArg (· ≫ κ) e
    · obtain ⟨t, ht⟩ := (hi Y _).1 ((hκ Y _).2 ⟨l, rfl⟩)
      obtain ⟨m, hm, -⟩ := (hp Y l t).1 (by rw [ht]; exact hi' Y t)
      exact ⟨m, hm⟩
  · refine isIso_of_yoneda_map_bijective _ fun Y => ⟨fun m m' e => hj Y m m' ?_ e, fun t => ?_⟩
    · rw [← cancel_mono κ, fac, fac]
      exact congrArg (· ≫ i) e
    · obtain ⟨l, hl⟩ := (hκ Y _).1 ((hi Y _).2 ⟨t, rfl⟩)
      obtain ⟨m, -, hm⟩ := (hp Y l t).1 (by rw [← hl]; exact hi' Y t)
      exact ⟨m, hm⟩

theorem GraphRep.kerIs (hr : GraphRep C a j κ p u) [IsIso p] [IsIso u] : C.KerIs a j (inv u ≫ p ≫ κ) := by
  obtain ⟨mκ, hκ, -, hp⟩ := hr
  refine ⟨inferInstance, fun Y k => (hκ Y k).trans ⟨?_, ?_⟩, fun Y t => ?_⟩
  · rintro ⟨l, rfl⟩
    exact ⟨l ≫ inv p ≫ u, by simp⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t ≫ inv u ≫ p, by simp⟩
  · have := (hp Y (t ≫ inv u ≫ p) t).2 ⟨t ≫ inv u, by simp, by simp⟩
    simp only [Category.assoc] at this
    exact this

end

section
variable {S S' : Scheme.{0}} (t : S' ⟶ S)

theorem homEquiv_left {Y : Over S'} {A : Over S} (k : (Over.map t).obj Y ⟶ A) :
    ((Over.mapPullbackAdj t).homEquiv Y A k).left ≫ pullback.fst A.hom t = k.left := by
  rw [Over.mapPullbackAdj, Adjunction.mkOfHomEquiv_homEquiv]
  exact pullback.lift_fst _ _ _

variable {G : Over S} [GrpObj G] [IsAffineHom (pullback.fst G.hom t)] {C : Charts G.left} {d : ℕ}
  {a : {i // C.wt i = C.c₀}} {j : Fin d → C.I}

omit [IsAffineHom (pullback.fst G.hom t)] in
theorem eSec_fst : eSec ((Over.pullback t).obj G) ≫ pullback.fst G.hom t = t ≫ eSec G := by
  rw [eSec, eSec, Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
    ← pullback.condition_assoc]
  exact (pullback.lift_fst _ _ _).trans (by simp)

omit [IsAffineHom (pullback.fst G.hom t)] in
theorem one_fst (Y : Over S') : (1 : (Over.map t).obj Y ⟶ G).left =
    (1 : Y ⟶ (Over.pullback t).obj G).left ≫ pullback.fst G.hom t := by
  rw [one_left_eq, one_left_eq]
  exact ((Category.assoc _ _ _).trans ((congrArg (Y.hom ≫ ·) (eSec_fst t)).trans (Category.assoc _ _ _).symm)).symm

theorem based_pull {c : Fin d → C.Cl} (hb : C.Based c a j) :
    Charts.Based (H := (Over.pullback t).obj G) (C.pull (pullback.fst G.hom t)) c a j := by
  have key : ∀ V : G.left.Opens, ⊤ ≤ eSec G ⁻¹ᵁ V →
      ⊤ ≤ eSec ((Over.pullback t).obj G) ⁻¹ᵁ pullback.fst G.hom t ⁻¹ᵁ V := by
    intro V h
    change ⊤ ≤ (eSec ((Over.pullback t).obj G) ≫ pullback.fst G.hom t) ⁻¹ᵁ V
    rw [eSec_fst]
    exact fun x _ => h (Set.mem_univ _)
  refine ⟨key _ hb.1, fun n => ⟨(hb.2 n).1, ?_⟩⟩
  have := key _ (hb.2 n).2
  rwa [Scheme.preimage_basicOpen] at this

omit [GrpObj G] [IsAffineHom (pullback.fst G.hom t)] in
theorem le_iff_of_eq {Y : Scheme.{0}} (r : Y ⟶ pullback G.hom t) (s : Y ⟶ G.left) (hs : s = r ≫ pullback.fst G.hom t)
    (V : G.left.Opens) : ⊤ ≤ r ⁻¹ᵁ pullback.fst G.hom t ⁻¹ᵁ V ↔ ⊤ ≤ s ⁻¹ᵁ V := by
  subst hs
  rfl

theorem inK_pull {Y : Over S'} (k : (Over.map t).obj Y ⟶ G) :
    Charts.InK (H := (Over.pullback t).obj G) (C.pull (pullback.fst G.hom t)) a
      ((Over.mapPullbackAdj t).homEquiv Y G k) ↔ C.InK a k := by
  have e := (homEquiv_left t k).symm
  have e₁ := one_fst t (G := G) Y
  constructor
  · rintro ⟨h, h₁, hh⟩
    refine ⟨(le_iff_of_eq t _ _ e _).1 h, (le_iff_of_eq t _ _ e₁ _).1 h₁, fun i hi => ?_⟩
    exact (appLE_app _ _ _ e _ h _ _).symm.trans ((hh i hi).trans (appLE_app _ _ _ e₁ _ h₁ _ _))
  · rintro ⟨h, h₁, hh⟩
    refine ⟨(le_iff_of_eq t _ _ e _).2 h, (le_iff_of_eq t _ _ e₁ _).2 h₁, fun i hi => ?_⟩
    exact (appLE_app _ _ _ e _ _ h _).trans ((hh i hi).trans (appLE_app _ _ _ e₁ _ _ h₁ _).symm)

theorem rel_pull {Y : Over S'} (k : (Over.map t).obj Y ⟶ G) (s : (Over.map t).obj Y ⟶ splitTorus S (Fin d → ℤ))
    (s' : Y ⟶ splitTorus S' (Fin d → ℤ))
    (hs : ∀ χ, s'.left.appTop.hom (charUnit S' (Fin d → ℤ) χ).val = s.left.appTop.hom (charUnit S (Fin d → ℤ) χ).val) :
    Rel (H := (Over.pullback t).obj G) (C.pull (pullback.fst G.hom t)) a j
      ((Over.mapPullbackAdj t).homEquiv Y G k) s' ↔ Rel C a j k s := by
  have e := (homEquiv_left t k).symm
  have e₁ := one_fst t (G := G) Y
  constructor
  · intro hh n h h₁
    have := hh n ((le_iff_of_eq t _ _ e _).2 h) ((le_iff_of_eq t _ _ e₁ _).2 h₁)
    rw [hs] at this
    exact (appLE_app _ _ _ e _ _ h _).symm.trans (this.trans
      (congrArg₂ (fun x y : Γ(Y.left, ⊤) => x * y) rfl (appLE_app _ _ _ e₁ _ _ h₁ _)))
  · intro hh n h h₁
    have := hh n ((le_iff_of_eq t _ _ e _).1 h) ((le_iff_of_eq t _ _ e₁ _).1 h₁)
    rw [hs]
    exact (appLE_app _ _ _ e _ h _ _).trans (this.trans (congrArg (_ * ·) (appLE_app _ _ _ e₁ _ h₁ _ _).symm))

theorem GraphRep.pull {K₀ K₁ : Over S} {κ : K₀ ⟶ G} {p : K₁ ⟶ K₀} {u : K₁ ⟶ splitTorus S (Fin d → ℤ)}
    (hr : GraphRep C a j κ p u) :
    ∃ e : splitTorus S' (Fin d → ℤ) ≅ (Over.pullback t).obj (splitTorus S (Fin d → ℤ)),
      GraphRep (H := (Over.pullback t).obj G) (C.pull (pullback.fst G.hom t)) a j ((Over.pullback t).map κ)
        ((Over.pullback t).map p) ((Over.pullback t).map u ≫ e.inv) := by
  obtain ⟨e, -, he⟩ := splitTorus_baseChange S S' t (Fin d → ℤ)
  obtain ⟨mκ, hκ, hj, hp⟩ := hr
  let adj := Over.mapPullbackAdj t
  have nat : ∀ {Y : Over S'} {A B : Over S} (f : (Over.map t).obj Y ⟶ A) (g : A ⟶ B),
      adj.homEquiv Y A f ≫ (Over.pullback t).map g = adj.homEquiv Y B (f ≫ g) :=
    fun f g => (adj.homEquiv_naturality_right f g).symm
  refine ⟨e, inferInstance, fun Y k => ?_, fun Y m m' h h' => ?_, fun Y l s' => ?_⟩
  · obtain ⟨k, rfl⟩ := (adj.homEquiv Y G).surjective k
    refine (inK_pull t k).trans ((hκ _ k).trans ⟨?_, ?_⟩)
    · rintro ⟨l, rfl⟩
      exact ⟨_, (nat l κ).symm⟩
    · rintro ⟨l, hl⟩
      obtain ⟨l, rfl⟩ := (adj.homEquiv Y K₀).surjective l
      exact ⟨l, (adj.homEquiv Y G).injective (hl.trans (nat l κ))⟩
  · obtain ⟨m, rfl⟩ := (adj.homEquiv Y K₁).surjective m
    obtain ⟨m', rfl⟩ := (adj.homEquiv Y K₁).surjective m'
    rw [← Category.assoc, ← Category.assoc, cancel_mono, nat, nat] at h'
    rw [nat, nat] at h
    rw [hj _ m m' ((adj.homEquiv _ _).injective h) ((adj.homEquiv _ _).injective h')]
  · obtain ⟨l, rfl⟩ := (adj.homEquiv Y K₀).surjective l
    obtain ⟨s, hs⟩ := (adj.homEquiv Y (splitTorus S (Fin d → ℤ))).surjective (s' ≫ e.hom)
    rw [nat]
    refine (rel_pull t (l ≫ κ) s s' fun χ => ?_).trans ((hp _ l s).trans ⟨?_, ?_⟩)
    · have h1 : s.left = s'.left ≫ e.hom.left ≫ pullback.fst (splitTorus S (Fin d → ℤ)).hom t := by
        rw [← homEquiv_left t s, hs, Over.comp_left, Category.assoc]
      rw [h1, ← he χ, Scheme.Hom.comp_appTop s'.left]
      rfl
    · rintro ⟨m, rfl, rfl⟩
      refine ⟨adj.homEquiv _ _ m, nat _ _, ?_⟩
      rw [← Category.assoc, nat, hs, Category.assoc, e.hom_inv_id, Category.comp_id]
    · rintro ⟨m, h, h'⟩
      obtain ⟨m, rfl⟩ := (adj.homEquiv Y K₁).surjective m
      rw [← Category.assoc, Iso.comp_inv_eq, ← hs, nat] at h'
      rw [nat] at h
      exact ⟨m, (adj.homEquiv _ _).injective h, (adj.homEquiv _ _).injective h'⟩

end

theorem exists_graphRep {S : Scheme.{0}} [IsAffine S] {G : Over S} [GrpObj G] [LocallyOfFiniteType G.hom]
    (C : Charts G.left) {d : ℕ} (a : {i // C.wt i = C.c₀}) (j : Fin d → C.I) (he : ⊤ ≤ eSec G ⁻¹ᵁ C.W a) :
    ∃ (K₀ K₁ : Over S) (_ : IsAffine K₀.left) (_ : IsAffine K₁.left) (_ : LocallyOfFiniteType K₀.hom)
      (_ : LocallyOfFiniteType K₁.hom) (κ : K₀ ⟶ G) (p : K₁ ⟶ K₀) (u : K₁ ⟶ splitTorus S (Fin d → ℤ)),
      GraphRep C a j κ p u := by
  let ε : C.I → Γ(S, ⊤) := fun i => ((eSec G).appLE (C.W a) ⊤ he).hom (C.r a i)
  have h1 : ∀ Y : Over S, ⊤ ≤ (1 : Y ⟶ G).left ⁻¹ᵁ C.W a := fun Y => by
    rw [one_left_eq]
    exact fun x _ => he (Set.mem_univ _)
  have hε : ∀ (Y : Over S) (h₁ : ⊤ ≤ (1 : Y ⟶ G).left ⁻¹ᵁ C.W a) (i : C.I),
      ((1 : Y ⟶ G).left.appLE _ ⊤ h₁).hom (C.r a i) = Y.hom.appTop.hom (ε i) :=
    fun Y h₁ i => (appTop_appLE Y.hom (eSec G) _ (one_left_eq Y) _ he h₁ _).symm
  obtain ⟨Z₀, _, z₀, _, hz₀⟩ := exists_zeroScheme G.left (C.W a) (C.aff a)
    fun i : {i // C.wt i = C.c₀} => C.r a i.1 - (G.hom.appLE ⊤ (C.W a) le_top).hom (ε i.1)
  let K₀ : Over S := Over.mk (z₀ ≫ G.hom)
  let κ : K₀ ⟶ G := Over.homMk z₀ rfl
  have hK₀ : IsAffine K₀.left := ‹IsAffine Z₀›
  have fK₀ : LocallyOfFiniteType K₀.hom := inferInstanceAs (LocallyOfFiniteType (z₀ ≫ G.hom))
  have hκ : ⊤ ≤ κ.left ⁻¹ᵁ C.W a := ((hz₀ _ z₀).2 ⟨𝟙 _, (Category.id_comp _).symm⟩).1
  let T := splitTorus S (Fin d → ℤ)
  have fT : LocallyOfFinitePresentation T.hom := ((splitTorus_properties S).1 (Fin d → ℤ)).2.1
  have hP : IsAffine (K₀ ⊗ T).left := inferInstanceAs (IsAffine (pullback K₀.hom T.hom))
  have fP : LocallyOfFiniteType (K₀ ⊗ T).hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst K₀.hom T.hom ≫ K₀.hom))
  obtain ⟨Z₁, _, z₁, _, hz₁⟩ := exists_zeroScheme (K₀ ⊗ T).left ⊤ (isAffineOpen_top _)
    fun n : Fin d => (fst K₀ T).left.appTop.hom ((κ.left.appLE _ ⊤ hκ).hom (C.r a (j n))) -
      (snd K₀ T).left.appTop.hom (charUnit S (Fin d → ℤ) (Pi.single n 1)).val * (K₀ ⊗ T).hom.appTop.hom (ε (j n))
  let K₁ : Over S := Over.mk (z₁ ≫ (K₀ ⊗ T).hom)
  let v : K₁ ⟶ K₀ ⊗ T := Over.homMk z₁ rfl
  have mκ : Mono κ := Over.mono_of_mono_left κ (hk := inferInstanceAs (Mono z₀))
  have mv : Mono v := Over.mono_of_mono_left v (hk := inferInstanceAs (Mono z₁))
  have lift₀ : ∀ {Z : Scheme.{0}} {A : Over S} (z : Z ⟶ A.left) (Y : Over S) (k : Y ⟶ A),
      (∃ l, k.left = l ≫ z) ↔ ∃ l : Y ⟶ Over.mk (z ≫ A.hom), k = l ≫ Over.homMk z rfl := by
    intro Z A z Y k
    constructor
    · rintro ⟨l, hl⟩
      refine ⟨Over.homMk l ?_, Over.OverMorphism.ext hl⟩
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ A.hom) hl.symm)).trans (Over.w k)
    · rintro ⟨l, rfl⟩
      exact ⟨l.left, rfl⟩
  refine ⟨K₀, K₁, hK₀, ‹IsAffine Z₁›, fK₀, inferInstanceAs (LocallyOfFiniteType (z₁ ≫ (K₀ ⊗ T).hom)), κ,
    v ≫ fst _ _, v ≫ snd _ _, mκ, fun Y k => ?_, fun Y m m' h h' => ?_, fun Y l s => ?_⟩
  · refine Iff.trans ?_ ((hz₀ _ k.left).trans (lift₀ z₀ Y k))
    constructor
    · rintro ⟨h, h₁, hh⟩
      refine ⟨h, fun i => ?_⟩
      rw [map_sub, hh i.1 i.2, hε, appLE_appLE_top _ _ _ (Over.w k), sub_self]
    · rintro ⟨h, hh⟩
      refine ⟨h, h1 Y, fun i hi => ?_⟩
      have := hh ⟨i, hi⟩
      rw [map_sub, appLE_appLE_top _ _ _ (Over.w k), sub_eq_zero] at this
      rw [hε, this]
  · rw [← cancel_mono v]
    exact CartesianMonoidalCategory.hom_ext _ _ (by simpa using h) (by simpa using h')
  · have e : (∃ m : Y ⟶ K₁, lift l s = m ≫ v) ↔ ∃ m : Y ⟶ K₁, m ≫ v ≫ fst _ _ = l ∧ m ≫ v ≫ snd _ _ = s := by
      refine exists_congr fun m => ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
      · rw [← Category.assoc, ← h, lift_fst]
      · rw [← Category.assoc, ← h, lift_snd]
      · exact CartesianMonoidalCategory.hom_ext _ _ (by simpa using h.1.symm) (by simpa using h.2.symm)
    refine Iff.trans ?_ (((hz₁ _ (lift l s).left).trans (lift₀ z₁ Y (lift l s))).trans e)
    have c : ∀ {A : Scheme.{0}} (g : (K₀ ⊗ T).left ⟶ A) (g' : Y.left ⟶ A) (_ : (lift l s).left ≫ g = g')
        (h : ⊤ ≤ (lift l s).left ⁻¹ᵁ ⊤) (x : Γ(A, ⊤)),
        ((lift l s).left.appLE ⊤ ⊤ h).hom (g.appTop.hom x) = g'.appTop.hom x := by
      intro A g g' hg h x
      subst hg
      erw [Scheme.Hom.appLE_eq_app]
      rw [Scheme.Hom.comp_appTop]
      rfl
    have c₁ : (lift l s).left ≫ (fst K₀ T).left = l.left := by rw [← Over.comp_left, lift_fst]
    have c₂ : (lift l s).left ≫ (snd K₀ T).left = s.left := by rw [← Over.comp_left, lift_snd]
    have hl : ⊤ ≤ (l ≫ κ).left ⁻¹ᵁ C.W a := fun x _ => hκ (Set.mem_univ _)
    constructor
    · intro hh
      refine ⟨(Scheme.Hom.preimage_top _).ge, fun n => ?_⟩
      rw [map_sub, map_mul, c _ _ c₁, c _ _ c₂, c _ _ (Over.w (lift l s)),
        appTop_appLE l.left κ.left (l ≫ κ).left rfl _ hκ hl, hh n hl (h1 Y), hε, sub_self]
    · rintro ⟨h, hh⟩ n h' h₁
      have := hh n
      rw [map_sub, map_mul, c _ _ c₁, c _ _ c₂, c _ _ (Over.w (lift l s)),
        appTop_appLE l.left κ.left (l ≫ κ).left rfl _ hκ h', sub_eq_zero] at this
      rw [hε, this]

theorem exists_kerIs_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom] (C : Charts G.left) (d : ℕ) (c : Fin d → C.Cl) (Sg : Set (Sp R)) [IsAffineHom (pullback.fst G.hom (Out.jK R))], Dense Sg → C.SplitOn c Sg → ∀ (a) (j : Fin d → C.I), C.Based c a j → ∃ i : splitTorus (Sp (FractionRing R)) (Fin d → ℤ) ⟶ ((Over.pullback (Out.jK R)).obj G), Charts.KerIs (H := ((Over.pullback (Out.jK R)).obj G)) (C.pull (pullback.fst G.hom (Out.jK R))) a j i := by
  intro R _ _ _ G _ _ _ _ _ C d c Sg _ hD hS a j hb
  obtain ⟨K₀, K₁, _, _, _, _, κ, p, u, hr⟩ := exists_graphRep C a j hb.1
  have fT : LocallyOfFinitePresentation (splitTorus (Sp R) (Fin d → ℤ)).hom :=
    ((splitTorus_properties (Sp R)).1 (Fin d → ℤ)).2.1
  have fib : ∀ x ∈ Sg, ∃ (K : Type) (_ : Field K) (t : Sp K ⟶ Sp R), Set.range t = {x} ∧
      IsIso ((Over.pullback t).map p) ∧ IsIso ((Over.pullback t).map u) := by
    intro x hx
    obtain ⟨K, _, t, _, ht, hc, i, hi⟩ := hS x hx
    obtain ⟨e, hr'⟩ := hr.pull t
    have : Smooth ((Over.pullback t).obj G).hom := inferInstanceAs (Smooth (pullback.snd _ _))
    have : IsSeparated ((Over.pullback t).obj G).hom := inferInstanceAs (IsSeparated (pullback.snd _ _))
    have : QuasiCompact ((Over.pullback t).obj G).hom := inferInstanceAs (QuasiCompact (pullback.snd _ _))
    have hk := GlobalTheory.ZJ.Charts.kerIs_of_torus K ((Over.pullback t).obj G) (C.pull (pullback.fst G.hom t)) d c i a j hc hi
      (based_pull t hb)
    obtain ⟨h₁, h₂⟩ := GraphRep.isIso (based_pull t hb) hr' hk
    exact ⟨K, inferInstance, t, ht, h₁, IsIso.of_isIso_comp_right _ e.inv⟩
  have hp := isIso_generic_of_dense_fibres R K₁ K₀ p Sg hD fun x hx => by
    obtain ⟨K, _, t, ht, h, -⟩ := fib x hx
    exact ⟨K, inferInstance, t, ht, h⟩
  have hu := isIso_generic_of_dense_fibres R K₁ _ u Sg hD fun x hx => by
    obtain ⟨K, _, t, ht, -, h⟩ := fib x hx
    exact ⟨K, inferInstance, t, ht, h⟩
  obtain ⟨e, hr'⟩ := hr.pull (Out.jK R)
  exact ⟨_, hr'.kerIs⟩

end GlobalTheory.ZJ.GenericTorus
