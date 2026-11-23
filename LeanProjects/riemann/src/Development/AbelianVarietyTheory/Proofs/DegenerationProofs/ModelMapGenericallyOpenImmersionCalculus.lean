import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfSchemeTheoreticallyDominant

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.GI
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' A'' B B' : Over (Sp K)}

theorem isPullback_j (M : Model R A) : IsPullback M.j A.hom M.Y.hom (spMap (algebraMap R K)) := by
  refine IsPullback.of_iso (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K)))
    ((Over.forget _).mapIso M.e) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp [Model.j, ← Over.comp_left_assoc]
  · simpa using (Over.w M.e.hom).symm

theorem twist_j (M : Model R A) (f : A ≅ A') : (M.twist f).j = f.inv.left ≫ M.j := by
  simp [Model.j, Model.twist]

theorem prod_j_fst (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (fst M.Y N.Y).left = (fst A A').left ≫ M.j := by
  have h : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (fst M.Y N.Y) = fst A A' ≫ M.e.inv := by
    simp [Model.prod]
  have := congr(($h).left ≫ pullback.fst M.Y.hom (spMap (algebraMap R K)))
  simpa [Model.j, pullback.lift_fst] using this

theorem prod_j_snd (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (snd M.Y N.Y).left = (snd A A').left ≫ N.j := by
  have h : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (snd M.Y N.Y) = snd A A' ≫ N.e.inv := by
    simp [Model.prod]
  have := congr(($h).left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K)))
  simpa [Model.j, pullback.lift_fst] using this

theorem prod_hom_ext (M : Model R A) (N : Model R A') {T : Scheme.{0}} {a b : T ⟶ (M.prod N).Y.left}
    (h₁ : a ≫ (fst M.Y N.Y).left = b ≫ (fst M.Y N.Y).left)
    (h₂ : a ≫ (snd M.Y N.Y).left = b ≫ (snd M.Y N.Y).left) : a = b :=
  pullback.hom_ext h₁ h₂

def Via (M : Model R A) (N : Model R A') (f : A ⟶ A') {W : Scheme.{0}} (u : W ⟶ M.Y.left) (g : W ⟶ N.Y.left) : Prop :=
  g ≫ N.Y.hom = u ≫ M.Y.hom ∧
    ∀ (T : Scheme.{0}) (w : T ⟶ W) (a : T ⟶ A.left), w ≫ u = a ≫ M.j → w ≫ g = a ≫ f.left ≫ N.j

theorem extends_iff_via {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {U : M.Y.left.Opens}
    {g : U.toScheme ⟶ N.Y.left} : Extends M N f U g ↔ Via M N f U.ι g := by
  refine and_congr_right fun _ => ⟨fun h T w a hw => ?_, fun h => h _ _ _ (morphismRestrict_ι _ _)⟩
  obtain ⟨l, h1, h2⟩ := (isPullback_morphismRestrict M.j U).exists_lift w a hw
  rw [← h1, ← h2, Category.assoc, h, Category.assoc]

theorem Via.precomp {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {W W' : Scheme.{0}} {u : W ⟶ M.Y.left}
    {g : W ⟶ N.Y.left} (h : Via M N f u g) (t : W' ⟶ W) : Via M N f (t ≫ u) (t ≫ g) :=
  ⟨by simp [h.1], fun T w a hw => by
    rw [← Category.assoc] at hw ⊢
    exact h.2 T _ a hw⟩

theorem Via.comp {M : Model R A} {N : Model R A'} {P : Model R A''} {f : A ⟶ A'} {f' : A' ⟶ A''}
    {W : Scheme.{0}} {u : W ⟶ M.Y.left} {g : W ⟶ N.Y.left} {g' : W ⟶ P.Y.left}
    (h : Via M N f u g) (h' : Via N P f' g g') : Via M P (f ≫ f') u g' :=
  ⟨h'.1.trans h.1, fun T w a hw => by
    have := h'.2 T w (a ≫ f.left) (by rw [h.2 T w a hw, Category.assoc])
    simpa using this⟩

theorem Via.inv {M : Model R A} {N : Model R A'} {f : A ≅ A'}
    {W : Scheme.{0}} {u : W ⟶ M.Y.left} {g : W ⟶ N.Y.left} (h : Via M N f.hom u g) : Via N M f.inv g u := by
  refine ⟨h.1.symm, fun T w b hw => ?_⟩
  obtain ⟨a, h1, h2⟩ := (isPullback_j M).exists_lift (w ≫ u) (b ≫ A'.hom) (by
    rw [Category.assoc, ← h.1, ← Category.assoc, hw, Category.assoc, N.j_hom, Category.assoc])
  have h3 : a ≫ f.hom.left = b := by
    refine (isPullback_j N).hom_ext ?_ ?_
    · rw [Category.assoc, ← h.2 T w a h1.symm, hw]
    · rw [Category.assoc, Over.w, h2]
  rw [← h1, ← h3]
  simp [← Over.comp_left_assoc]

theorem via_of_hom {M : Model R A} {N : Model R A'} {f : A ⟶ A'} (g : M.Y ⟶ N.Y)
    (h : M.j ≫ g.left = f.left ≫ N.j) : Via M N f (𝟙 _) g.left :=
  ⟨by simp, fun T w a hw => by
    rw [Category.comp_id] at hw
    rw [hw, Category.assoc, h]⟩

theorem via_twist {M : Model R A} {N : Model R B} (e : A ≅ A') {f : A' ⟶ B}
    {W : Scheme.{0}} {u : W ⟶ M.Y.left} {g : W ⟶ N.Y.left} :
    Via (M.twist e) N f u g ↔ Via M N (e.hom ≫ f) u g := by
  have h1 : Via M (M.twist e) e.hom u u := by
    simpa using (via_of_hom (M := M) (N := M.twist e) (f := e.hom) (𝟙 M.Y)
      (by simp [twist_j, ← Over.comp_left_assoc])).precomp u
  refine ⟨fun h => h1.comp h, fun h => ?_⟩
  simpa using h1.inv.comp h

theorem via_twist_right {M : Model R B} {N : Model R A} (e : A ≅ A') {f : B ⟶ A}
    {W : Scheme.{0}} {u : W ⟶ M.Y.left} {g : W ⟶ N.Y.left} :
    Via M (N.twist e) (f ≫ e.hom) u g ↔ Via M N f u g := by
  have h1 : Via N (N.twist e) e.hom g g := by
    simpa using (via_of_hom (M := N) (N := N.twist e) (f := e.hom) (𝟙 N.Y)
      (by simp [twist_j, ← Over.comp_left_assoc])).precomp g
  refine ⟨fun h => ?_, fun h => h.comp h1⟩
  simpa using h.comp h1.inv

theorem via_fst (M : Model R A) (N : Model R A') {W : Scheme.{0}} (u : W ⟶ (M.prod N).Y.left) :
    Via (M.prod N) M (fst A A') u (u ≫ (fst M.Y N.Y).left) := by
  simpa using (via_of_hom (M := M.prod N) (N := M) (fst M.Y N.Y) (prod_j_fst M N)).precomp u

theorem via_snd (M : Model R A) (N : Model R A') {W : Scheme.{0}} (u : W ⟶ (M.prod N).Y.left) :
    Via (M.prod N) N (snd A A') u (u ≫ (snd M.Y N.Y).left) := by
  simpa using (via_of_hom (M := M.prod N) (N := N) (snd M.Y N.Y) (prod_j_snd M N)).precomp u

theorem via_prod {M : Model R A} {P : Model R B} {Q : Model R B'} {f : A ⟶ B ⊗ B'}
    {W : Scheme.{0}} {u : W ⟶ M.Y.left} {g : W ⟶ (P.prod Q).Y.left}
    (h₁ : Via M P (f ≫ fst B B') u (g ≫ (fst P.Y Q.Y).left))
    (h₂ : Via M Q (f ≫ snd B B') u (g ≫ (snd P.Y Q.Y).left)) : Via M (P.prod Q) f u g := by
  refine ⟨?_, fun T w a hw => prod_hom_ext P Q ?_ ?_⟩
  · rw [← h₁.1, Category.assoc, Over.w]; rfl
  · rw [Category.assoc, h₁.2 T w a hw, Category.assoc, Category.assoc, prod_j_fst]; simp
  · rw [Category.assoc, h₂.2 T w a hw, Category.assoc, Category.assoc, prod_j_snd]; simp

theorem defAt_iff {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {y : M.Y.left} :
    DefAt M N f y ↔ ∃ (W : Scheme.{0}) (u : W ⟶ M.Y.left) (g : W ⟶ N.Y.left) (w : W),
      IsOpenImmersion u ∧ u w = y ∧ Via M N f u g := by
  constructor
  · rintro ⟨U, g, hy, h⟩
    exact ⟨_, U.ι, g, ⟨y, hy⟩, inferInstance, rfl, extends_iff_via.1 h⟩
  · rintro ⟨W, u, g, w, _, rfl, h⟩
    refine ⟨u.opensRange, u.isoOpensRange.inv ≫ g, ⟨w, rfl⟩, extends_iff_via.2 ?_⟩
    simpa using h.precomp u.isoOpensRange.inv

theorem isoAt_iff {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {y : M.Y.left} :
    IsoAt M N f y ↔ ∃ (W : Scheme.{0}) (u : W ⟶ M.Y.left) (g : W ⟶ N.Y.left) (w : W),
      IsOpenImmersion u ∧ IsOpenImmersion g ∧ u w = y ∧ Via M N f u g := by
  constructor
  · rintro ⟨U, g, hy, h, hg⟩
    exact ⟨_, U.ι, g, ⟨y, hy⟩, inferInstance, hg, rfl, extends_iff_via.1 h⟩
  · rintro ⟨W, u, g, w, _, _, rfl, h⟩
    refine ⟨u.opensRange, u.isoOpensRange.inv ≫ g, ⟨w, rfl⟩, extends_iff_via.2 ?_, inferInstance⟩
    simpa using h.precomp u.isoOpensRange.inv

theorem extends_mono {M : Model R A} {N : Model R A'} {f : A ⟶ A'} {U V : M.Y.left.Opens}
    {g : U.toScheme ⟶ N.Y.left} (h : Extends M N f U g) (hV : V ≤ U) :
    Extends M N f V (M.Y.left.homOfLE hV ≫ g) :=
  extends_iff_via.2 (by simpa using (extends_iff_via.1 h).precomp (M.Y.left.homOfLE hV))

theorem isOpen_defAt (M : Model R A) (N : Model R A') (f : A ⟶ A') : IsOpen {y | DefAt M N f y} :=
  isOpen_iff_forall_mem_open.2 fun _ ⟨U, g, hy, h⟩ => ⟨U, fun _ hz => ⟨U, g, hz, h⟩, U.isOpen, hy⟩

theorem isOpen_isoAt (M : Model R A) (N : Model R A') (f : A ⟶ A') : IsOpen {y | IsoAt M N f y} :=
  isOpen_iff_forall_mem_open.2 fun _ ⟨U, g, hy, h⟩ => ⟨U, fun _ hz => ⟨U, g, hz, h⟩, U.isOpen, hy⟩

theorem Via.unique [IsDomain R] [IsFractionRing R K] {M : Model R A} {N : Model R A'} {f : A ⟶ A'}
    {W : Scheme.{0}} {u : W ⟶ M.Y.left} [Flat u] {g g' : W ⟶ N.Y.left}
    (h : Via M N f u g) (h' : Via M N f u g') : g = g' := by
  have := schemeTheoreticallyDominant_fractionField R K
  have := M.smooth
  have := N.sep
  let Y : Over (Sp R) := Over.mk (u ≫ M.Y.hom)
  have : Flat Y.hom := inferInstanceAs (Flat (u ≫ M.Y.hom))
  have hp := ((IsPullback.of_hasPullback u M.j).paste_vert (isPullback_j M))
  have : IsSchemeTheoreticallyDominant (pullback.fst u M.j) :=
    IsSchemeTheoreticallyDominant.of_isPullback hp.flip
  have e := over_ext_of_schemeTheoreticallyDominant (Y := Y) (X := N.Y) (pullback.fst u M.j)
    (a := Over.homMk g h.1) (b := Over.homMk g' h'.1)
    ((h.2 _ _ _ pullback.condition).trans (h'.2 _ _ _ pullback.condition).symm)
  exact congr(($e).left)

theorem extends_unique [IsDomain R] [IsFractionRing R K] {M : Model R A} {N : Model R A'} {f : A ⟶ A'}
    {U : M.Y.left.Opens} {g g' : U.toScheme ⟶ N.Y.left}
    (h : Extends M N f U g) (h' : Extends M N f U g') : g = g' :=
  (extends_iff_via.1 h).unique (extends_iff_via.1 h')

theorem Via.apply_eq [IsDomain R] [IsFractionRing R K] {M : Model R A} {N : Model R A'} {f : A ⟶ A'}
    {W W' : Scheme.{0}} {u : W ⟶ M.Y.left} {u' : W' ⟶ M.Y.left} [Flat u] [Flat u']
    {g : W ⟶ N.Y.left} {g' : W' ⟶ N.Y.left} (h : Via M N f u g) (h' : Via M N f u' g')
    {w : W} {w' : W'} (e : u w = u' w') : g w = g' w' := by
  obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback (f := u) (g := u') w w' e
  have h2 := h'.precomp (pullback.snd u u')
  rw [← pullback.condition] at h2
  have := (h.precomp (pullback.fst u u')).unique h2
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, this]

theorem Via.hom_apply {M : Model R A} {N : Model R A'} {f : A ⟶ A'}
    {W : Scheme.{0}} {u : W ⟶ M.Y.left} {g : W ⟶ N.Y.left} (h : Via M N f u g) (w : W) :
    N.Y.hom (g w) = M.Y.hom (u w) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h.1]

theorem Via.mem_sp [IsLocalRing R] {M : Model R A} {N : Model R A'} {f : A ⟶ A'}
    {W : Scheme.{0}} {u : W ⟶ M.Y.left} {g : W ⟶ N.Y.left} (h : Via M N f u g) (w : W) :
    g w ∈ N.sp ↔ u w ∈ M.sp := by
  show N.Y.hom (g w) = _ ↔ M.Y.hom (u w) = _
  rw [h.hom_apply]

theorem Via.comp_pullback {M : Model R A} {N : Model R A'} {P : Model R A''} {f : A ⟶ A'} {f' : A' ⟶ A''}
    {W W' : Scheme.{0}} {u : W ⟶ M.Y.left} {g : W ⟶ N.Y.left} {u' : W' ⟶ N.Y.left} {g' : W' ⟶ P.Y.left}
    (h : Via M N f u g) (h' : Via N P f' u' g') :
    Via M P (f ≫ f') (pullback.fst g u' ≫ u) (pullback.snd g u' ≫ g') := by
  have h2 := h'.precomp (pullback.snd g u')
  rw [← pullback.condition] at h2
  exact (h.precomp _).comp h2

theorem defAt_comp {M : Model R A} {N : Model R A'} {P : Model R A''} {f : A ⟶ A'} {f' : A' ⟶ A''}
    {W : Scheme.{0}} {u : W ⟶ M.Y.left} [IsOpenImmersion u] {g : W ⟶ N.Y.left} (h : Via M N f u g) (w : W)
    (h' : DefAt N P f' (g w)) : DefAt M P (f ≫ f') (u w) := by
  replace h' := defAt_iff.1 h'
  obtain ⟨W', u', g', w', _, e, h'⟩ := h'
  obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := u') w w' e.symm
  exact defAt_iff.2 ⟨_, _, _, z, inferInstance, Scheme.Hom.comp_apply _ _ _, h.comp_pullback h'⟩

theorem isoAt_comp {M : Model R A} {N : Model R A'} {P : Model R A''} {f : A ⟶ A'} {f' : A' ⟶ A''}
    {W : Scheme.{0}} {u : W ⟶ M.Y.left} [IsOpenImmersion u] {g : W ⟶ N.Y.left} [IsOpenImmersion g]
    (h : Via M N f u g) (w : W) (h' : IsoAt N P f' (g w)) : IsoAt M P (f ≫ f') (u w) := by
  replace h' := isoAt_iff.1 h'
  obtain ⟨W', u', g', w', _, _, e, h'⟩ := h'
  obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := u') w w' e.symm
  exact isoAt_iff.2 ⟨_, _, _, z, inferInstance, inferInstance, Scheme.Hom.comp_apply _ _ _, h.comp_pullback h'⟩

theorem isoAt_inv {M : Model R A} {N : Model R A'} {f : A ≅ A'}
    {W : Scheme.{0}} {u : W ⟶ M.Y.left} [IsOpenImmersion u] {g : W ⟶ N.Y.left} [IsOpenImmersion g]
    (h : Via M N f.hom u g) (w : W) : IsoAt N M f.inv (g w) :=
  isoAt_iff.2 ⟨W, g, u, w, inferInstance, inferInstance, rfl, h.inv⟩

theorem defAt_twist {M : Model R A} {N : Model R B} (e : A ≅ A') {f : A' ⟶ B} {y : M.Y.left} :
    DefAt (M.twist e) N f y ↔ DefAt M N (e.hom ≫ f) y := by
  rw [defAt_iff, defAt_iff]
  constructor <;> rintro ⟨W, u, g, w, h1, h2, h⟩
  exacts [⟨W, u, g, w, h1, h2, (via_twist e).1 h⟩, ⟨W, u, g, w, h1, h2, (via_twist e).2 h⟩]

theorem isoAt_twist {M : Model R A} {N : Model R B} (e : A ≅ A') {f : A' ⟶ B} {y : M.Y.left} :
    IsoAt (M.twist e) N f y ↔ IsoAt M N (e.hom ≫ f) y := by
  rw [isoAt_iff, isoAt_iff]
  constructor <;> rintro ⟨W, u, g, w, h0, h1, h2, h⟩
  exacts [⟨W, u, g, w, h0, h1, h2, (via_twist e).1 h⟩, ⟨W, u, g, w, h0, h1, h2, (via_twist e).2 h⟩]

theorem defAt_twist_right {M : Model R B} {N : Model R A} (e : A ≅ A') {f : B ⟶ A} {y : M.Y.left} :
    DefAt M (N.twist e) (f ≫ e.hom) y ↔ DefAt M N f y := by
  rw [defAt_iff, defAt_iff]
  constructor <;> rintro ⟨W, u, g, w, h1, h2, h⟩
  exacts [⟨W, u, g, w, h1, h2, (via_twist_right e).1 h⟩, ⟨W, u, g, w, h1, h2, (via_twist_right e).2 h⟩]

theorem isoAt_twist_right {M : Model R B} {N : Model R A} (e : A ≅ A') {f : B ⟶ A} {y : M.Y.left} :
    IsoAt M (N.twist e) (f ≫ e.hom) y ↔ IsoAt M N f y := by
  rw [isoAt_iff, isoAt_iff]
  constructor <;> rintro ⟨W, u, g, w, h0, h1, h2, h⟩
  exacts [⟨W, u, g, w, h0, h1, h2, (via_twist_right e).1 h⟩, ⟨W, u, g, w, h0, h1, h2, (via_twist_right e).2 h⟩]

theorem defAt_of_hom {M : Model R A} {N : Model R A'} {f : A ⟶ A'} (g : M.Y ⟶ N.Y)
    (h : M.j ≫ g.left = f.left ≫ N.j) (y : M.Y.left) : DefAt M N f y :=
  defAt_iff.2 ⟨_, _, _, y, inferInstance, rfl, via_of_hom g h⟩

theorem isoAt_of_hom {M : Model R A} {N : Model R A'} {f : A ⟶ A'} (g : M.Y ⟶ N.Y) [IsOpenImmersion g.left]
    (h : M.j ≫ g.left = f.left ≫ N.j) (y : M.Y.left) : IsoAt M N f y :=
  isoAt_iff.2 ⟨_, _, _, y, inferInstance, inferInstance, rfl, via_of_hom g h⟩

def prodMap (M : Model R A) (N : Model R A') {W W' : Scheme.{0}} (s : W ⟶ Sp R) (s' : W' ⟶ Sp R)
    (u : W ⟶ M.Y.left) (u' : W' ⟶ N.Y.left) (h : u ≫ M.Y.hom = s) (h' : u' ≫ N.Y.hom = s') :
    pullback s s' ⟶ (M.prod N).Y.left :=
  pullback.map s s' M.Y.hom N.Y.hom u u' (𝟙 _) (by simp [h]) (by simp [h'])

section
variable (M : Model R A) (N : Model R A') {W W' : Scheme.{0}} (s : W ⟶ Sp R) (s' : W' ⟶ Sp R)
    (u : W ⟶ M.Y.left) (u' : W' ⟶ N.Y.left) (h : u ≫ M.Y.hom = s) (h' : u' ≫ N.Y.hom = s')

theorem prodMap_fst : prodMap M N s s' u u' h h' ≫ (fst M.Y N.Y).left = pullback.fst s s' ≫ u :=
  pullback.lift_fst _ _ _

theorem prodMap_snd : prodMap M N s s' u u' h h' ≫ (snd M.Y N.Y).left = pullback.snd s s' ≫ u' :=
  pullback.lift_snd _ _ _

instance isOpenImmersion_prodMap [IsOpenImmersion u] [IsOpenImmersion u'] :
    IsOpenImmersion (prodMap M N s s' u u' h h') :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) ‹_› ‹_› h.symm h'.symm
end

theorem Via.prod {M : Model R A} {N : Model R A'} {P : Model R B} {Q : Model R B'} {f : A ⟶ B} {f' : A' ⟶ B'}
    {W W' : Scheme.{0}} {u : W ⟶ M.Y.left} {g : W ⟶ P.Y.left} {u' : W' ⟶ N.Y.left} {g' : W' ⟶ Q.Y.left}
    (h : Via M P f u g) (h' : Via N Q f' u' g') :
    Via (M.prod N) (P.prod Q) (f ⊗ₘ f') (prodMap M N _ _ u u' rfl rfl) (prodMap P Q _ _ g g' h.1 h'.1) := by
  refine via_prod ?_ ?_
  · rw [tensorHom_fst, prodMap_fst]
    refine (via_fst M N _).comp ?_
    rw [prodMap_fst]
    exact h.precomp _
  · rw [tensorHom_snd, prodMap_snd]
    refine (via_snd M N _).comp ?_
    rw [prodMap_snd]
    exact h'.precomp _

theorem exists_prodMap_apply {M : Model R A} {N : Model R A'} {W W' : Scheme.{0}}
    (u : W ⟶ M.Y.left) (u' : W' ⟶ N.Y.left) [IsOpenImmersion u] [IsOpenImmersion u'] (z : (M.prod N).Y.left)
    (w : W) (w' : W') (e : u w = (fst M.Y N.Y).left z) (e' : u' w' = (snd M.Y N.Y).left z) :
    ∃ t, prodMap M N _ _ u u' rfl rfl t = z := by
  have := Scheme.Pullback.range_map (u ≫ M.Y.hom) (u' ≫ N.Y.hom) M.Y.hom N.Y.hom u u' (𝟙 _) (by simp) (by simp)
  exact (Set.ext_iff.1 this z).2 ⟨⟨w, e⟩, ⟨w', e'⟩⟩

theorem defAt_prod {M : Model R A} {N : Model R A'} {P : Model R B} {Q : Model R B'} {f : A ⟶ B} {f' : A' ⟶ B'}
    {z : (M.prod N).Y.left} (h : DefAt M P f ((fst M.Y N.Y).left z)) (h' : DefAt N Q f' ((snd M.Y N.Y).left z)) :
    DefAt (M.prod N) (P.prod Q) (f ⊗ₘ f') z := by
  obtain ⟨W, u, g, w, _, e, h⟩ := defAt_iff.1 h
  obtain ⟨W', u', g', w', _, e', h'⟩ := defAt_iff.1 h'
  obtain ⟨t, ht⟩ := exists_prodMap_apply u u' z w w' e e'
  exact defAt_iff.2 ⟨_, _, _, t, inferInstance, ht, h.prod h'⟩

theorem isoAt_prod {M : Model R A} {N : Model R A'} {P : Model R B} {Q : Model R B'} {f : A ⟶ B} {f' : A' ⟶ B'}
    {z : (M.prod N).Y.left} (h : IsoAt M P f ((fst M.Y N.Y).left z)) (h' : IsoAt N Q f' ((snd M.Y N.Y).left z)) :
    IsoAt (M.prod N) (P.prod Q) (f ⊗ₘ f') z := by
  obtain ⟨W, u, g, w, _, _, e, h⟩ := isoAt_iff.1 h
  obtain ⟨W', u', g', w', _, _, e', h'⟩ := isoAt_iff.1 h'
  obtain ⟨t, ht⟩ := exists_prodMap_apply u u' z w w' e e'
  exact isoAt_iff.2 ⟨_, _, _, t, inferInstance, inferInstance, ht, h.prod h'⟩

theorem isoAt_assoc (M : Model R A) (N : Model R A') (P : Model R A'') (z : ((M.prod N).prod P).Y.left) :
    IsoAt ((M.prod N).prod P) (M.prod (N.prod P)) (α_ A A' A'').hom z := by
  have : IsIso (α_ M.Y N.Y P.Y).hom.left := inferInstanceAs (IsIso ((Over.forget (Sp R)).map (α_ M.Y N.Y P.Y).hom))
  refine isoAt_iff.2 ⟨_, 𝟙 _, (α_ M.Y N.Y P.Y).hom.left, z, inferInstance, inferInstance, rfl, ?_⟩
  have h := via_fst (M.prod N) P (𝟙 _)
  refine via_prod ?_ (via_prod ?_ ?_)
  · have e : (α_ M.Y N.Y P.Y).hom.left ≫ (fst M.Y (N.prod P).Y).left =
        (𝟙 _ ≫ (fst (M.prod N).Y P.Y).left) ≫ (fst M.Y N.Y).left :=
      congr(($(associator_hom_fst M.Y N.Y P.Y)).left)
    rw [associator_hom_fst, e]
    exact h.comp (via_fst M N _)
  · have e : ((α_ M.Y N.Y P.Y).hom.left ≫ (snd M.Y (N.prod P).Y).left) ≫ (fst N.Y P.Y).left =
        (𝟙 _ ≫ (fst (M.prod N).Y P.Y).left) ≫ (snd M.Y N.Y).left := by
      rw [Category.assoc]
      exact congr(($(associator_hom_snd_fst M.Y N.Y P.Y)).left)
    rw [Category.assoc, associator_hom_snd_fst, e]
    exact h.comp (via_snd M N _)
  · have e : ((α_ M.Y N.Y P.Y).hom.left ≫ (snd M.Y (N.prod P).Y).left) ≫ (snd N.Y P.Y).left =
        (𝟙 _ ≫ (snd (M.prod N).Y P.Y).left) := by
      rw [Category.assoc]
      exact congr(($(associator_hom_snd_snd M.Y N.Y P.Y)).left)
    rw [Category.assoc, associator_hom_snd_snd, e]
    exact via_snd (M.prod N) P _

theorem isoAt_braiding (M : Model R A) (N : Model R A') (z : (M.prod N).Y.left) :
    IsoAt (M.prod N) (N.prod M) (β_ A A').hom z := by
  have : IsIso (β_ M.Y N.Y).hom.left := inferInstanceAs (IsIso ((Over.forget (Sp R)).map (β_ M.Y N.Y).hom))
  refine isoAt_iff.2 ⟨_, 𝟙 _, (β_ M.Y N.Y).hom.left, z, inferInstance, inferInstance, rfl, ?_⟩
  refine via_prod ?_ ?_
  · have e : (β_ M.Y N.Y).hom.left ≫ (fst N.Y M.Y).left = 𝟙 _ ≫ (snd M.Y N.Y).left :=
      congr(($(braiding_hom_fst M.Y N.Y)).left)
    rw [braiding_hom_fst, e]
    exact via_snd M N _
  · have e : (β_ M.Y N.Y).hom.left ≫ (snd N.Y M.Y).left = 𝟙 _ ≫ (fst M.Y N.Y).left :=
      congr(($(braiding_hom_snd M.Y N.Y)).left)
    rw [braiding_hom_snd, e]
    exact via_fst M N _

section
variable [IsLocalRing R]

theorem exists_mem_sp_prod {M : Model R A} {N : Model R A'} {x : M.Y.left} {y : N.Y.left}
    (hx : x ∈ M.sp) (hy : y ∈ N.sp) :
    ∃ z ∈ (M.prod N).sp, (fst M.Y N.Y).left z = x ∧ (snd M.Y N.Y).left z = y := by
  obtain ⟨z, h1, h2⟩ := Scheme.Pullback.exists_preimage_pullback (f := M.Y.hom) (g := N.Y.hom) x y
    (hx.trans hy.symm)
  refine ⟨z, ?_, h1, h2⟩
  exact ((via_fst M N (𝟙 _)).mem_sp z).1 (by
    rw [Category.id_comp]
    exact h1.symm ▸ hx)

theorem genIso_of_le {M N : Model R A} (hM : M.sp.Nonempty) (h : M.Le N) : GenIso M N (𝟙 A) := by
  obtain ⟨g, _, e⟩ := h
  obtain ⟨y, hy⟩ := hM
  exact ⟨y, hy, isoAt_of_hom g (by simpa using e) y⟩

theorem genIso_comp {M : Model R A} {N : Model R A'} {P : Model R A''} {f : A ⟶ A'} {f' : A' ⟶ A''}
    (hN : N.Irr) (h : GenIso M N f) (h' : GenIso N P f') : GenIso M P (f ≫ f') := by
  obtain ⟨y, hy, h⟩ := h
  replace h := isoAt_iff.1 h
  obtain ⟨W, u, g, w, _, _, rfl, h⟩ := h
  obtain ⟨_, hz, ⟨w', rfl⟩, hz'⟩ := hN.2 _ _ g.opensRange.isOpen (isOpen_isoAt N P f')
    ⟨g w, (h.mem_sp w).2 hy, w, rfl⟩ h'
  exact ⟨u w', (h.mem_sp w').1 hz, isoAt_comp h w' hz'⟩

theorem genIso_inv {M : Model R A} {N : Model R A'} {f : A ≅ A'} (h : GenIso M N f.hom) : GenIso N M f.inv := by
  obtain ⟨y, hy, h⟩ := h
  replace h := isoAt_iff.1 h
  obtain ⟨W, u, g, w, _, _, rfl, h⟩ := h
  exact ⟨g w, (h.mem_sp w).2 hy, isoAt_inv h w⟩

theorem genIso_twist {M : Model R A} {N : Model R B} (e : A ≅ A') {f : A' ⟶ B} :
    GenIso (M.twist e) N f ↔ GenIso M N (e.hom ≫ f) :=
  exists_congr fun _ => and_congr Iff.rfl (isoAt_twist e)

theorem genIso_twist_right {M : Model R B} {N : Model R A} (e : A ≅ A') {f : B ⟶ A} :
    GenIso M (N.twist e) (f ≫ e.hom) ↔ GenIso M N f :=
  exists_congr fun _ => and_congr Iff.rfl (isoAt_twist_right e)

theorem genIso_prod {M : Model R A} {N : Model R A'} {P : Model R B} {Q : Model R B'} {f : A ⟶ B} {f' : A' ⟶ B'}
    (h : GenIso M P f) (h' : GenIso N Q f') : GenIso (M.prod N) (P.prod Q) (f ⊗ₘ f') := by
  obtain ⟨x, hx, h⟩ := h
  obtain ⟨y, hy, h'⟩ := h'
  obtain ⟨z, hz, rfl, rfl⟩ := exists_mem_sp_prod hx hy
  exact ⟨z, hz, isoAt_prod h h'⟩
end

theorem genIso_calculus : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → (∀ (A : Over (Sp K)) (M N : Model R A), M.Irr → M.Le N → GenIso M N (𝟙 A)) ∧ (∀ (A A' A'' : Over (Sp K)) (M : Model R A) (N : Model R A') (P : Model R A'') (f : A ⟶ A') (g : A' ⟶ A''), N.Irr → GenIso M N f → GenIso N P g → GenIso M P (f ≫ g)) ∧ (∀ (A A' : Over (Sp K)) (M : Model R A) (N : Model R A') (f : A ≅ A'), (GenIso M N f.hom → GenIso N M f.inv) ∧ (GenIso M N f.hom ↔ GenIso (M.twist f) N (𝟙 A')) ∧ (M.Irr → (M.twist f).Irr)) ∧ (∀ (A A' B B' : Over (Sp K)) (M : Model R A) (N : Model R A') (P : Model R B) (Q : Model R B') (f : A ⟶ B) (g : A' ⟶ B'), GenIso M P f → GenIso N Q g → GenIso (M.prod N) (P.prod Q) (f ⊗ₘ g)) ∧ (∀ (A A' A'' : Over (Sp K)) (M : Model R A) (N : Model R A') (P : Model R A''), M.Irr → N.Irr → P.Irr → GenIso ((M.prod N).prod P) (M.prod (N.prod P)) (α_ A A' A'').hom ∧ GenIso (M.prod N) (N.prod M) (β_ A A').hom) := by
  intro R K _ _ _ _ _ _
  refine ⟨fun A M N hM h => genIso_of_le hM.1 h, fun _ _ _ _ _ _ _ _ hN h h' => genIso_comp hN h h',
    fun A A' M N f => ⟨genIso_inv, ?_, id⟩, fun _ _ _ _ _ _ _ _ _ _ h h' => genIso_prod h h',
    fun A A' A'' M N P ⟨⟨x, hx⟩, _⟩ ⟨⟨y, hy⟩, _⟩ ⟨⟨t, ht⟩, _⟩ => ?_⟩
  · rw [genIso_twist, Category.comp_id]
  · obtain ⟨z, hz, -⟩ := exists_mem_sp_prod hx hy
    obtain ⟨z', hz', -⟩ := exists_mem_sp_prod hz ht
    exact ⟨⟨z', hz', isoAt_assoc M N P z'⟩, ⟨z, hz, isoAt_braiding M N z⟩⟩

end GlobalTheory.SS.GI
end
