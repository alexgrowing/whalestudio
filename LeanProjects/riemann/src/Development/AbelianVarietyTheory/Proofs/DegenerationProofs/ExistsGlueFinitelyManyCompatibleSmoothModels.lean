import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GlueModelsOverSubfield
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.GlueCompat

set_option backward.isDefEq.respectTransparency false

noncomputable def coverTwo {X U V : Scheme.{0}} (u : U ⟶ X) (v : V ⟶ X) [IsOpenImmersion u] [IsOpenImmersion v]
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v) : X.OpenCover :=
  let T : Bool → Scheme.{0} := fun i => Bool.rec U V i
  let t : ∀ i, T i ⟶ X := fun i => Bool.rec (motive := fun i => T i ⟶ X) u v i
  have ht : ∀ i, IsOpenImmersion (t i) := fun i => by cases i <;> assumption
  Scheme.Cover.mkOfCovers Bool T t (fun x => by
    rcases hc x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact ⟨false, y, hy⟩
    · exact ⟨true, y, hy⟩)

theorem target_two (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P] {X Y U V U' V' : Scheme.{0}}
    {f : X ⟶ Y} {u : U ⟶ Y} {v : V ⟶ Y} [IsOpenImmersion u] [IsOpenImmersion v]
    (hc : ∀ x : Y, x ∈ Set.range u ∨ x ∈ Set.range v) {a : U' ⟶ X} {b : U' ⟶ U} {c : V' ⟶ X} {d : V' ⟶ V}
    (h₁ : IsPullback a b f u) (h₂ : IsPullback c d f v) (hb : P b) (hd : P d) : P f := by
  refine IsZariskiLocalAtTarget.of_openCover (coverTwo u v hc) ?_
  rintro (_ | _)
  · change P (pullback.snd f u)
    rwa [← h₁.isoPullback_inv_snd, P.cancel_left_of_respectsIso]
  · change P (pullback.snd f v)
    rwa [← h₂.isoPullback_inv_snd, P.cancel_left_of_respectsIso]

theorem source_two (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtSource P] {X Y U V : Scheme.{0}}
    {f : X ⟶ Y} {u : U ⟶ X} {v : V ⟶ X} [IsOpenImmersion u] [IsOpenImmersion v]
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v) (hb : P (u ≫ f)) (hd : P (v ≫ f)) : P f := by
  refine IsZariskiLocalAtSource.of_openCover (coverTwo u v hc) ?_
  rintro (_ | _)
  · exact hb
  · exact hd

theorem qc_two {X Y U V : Scheme.{0}} [IsAffine Y] {f : X ⟶ Y} {u : U ⟶ X} {v : V ⟶ X}
    (hc : ∀ x : X, x ∈ Set.range u ∨ x ∈ Set.range v) (hb : QuasiCompact (u ≫ f)) (hd : QuasiCompact (v ≫ f)) :
    QuasiCompact f := by
  have h1 : CompactSpace U := (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).1 hb
  have h2 : CompactSpace V := (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).1 hd
  refine (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).2 ⟨?_⟩
  have : (Set.univ : Set X) = Set.range u ∪ Set.range v := by
    ext x; simpa using hc x
  rw [this]
  exact (isCompact_range u.continuous).union (isCompact_range v.continuous)

theorem pb_mono {A X Y : Scheme.{0}} {a : A ⟶ X} {i : X ⟶ Y} [Mono i] {j : A ⟶ Y} (h : a ≫ i = j) :
    IsPullback a (𝟙 A) i j := by
  subst h
  exact IsPullback.of_vert_isIso_mono (by constructor; simp)

theorem pb_snd {S : Scheme.{0}} (N : Over S) {M G : Over S} (g : M ⟶ G) :
    IsPullback (N ◁ g).left (snd N M).left (snd N G).left g.left := by
  have : IsPullback (N ◁ g) (snd N M) (snd N G) g := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift (s.fst ≫ fst N G) s.snd) ?_ ?_ ?_⟩⟩
    · intro s; ext <;> simp [s.condition]
    · intro s; simp
    · intro s m h1 h2; ext
      · simp [← h1]
      · simp [← h2]
  exact this.map (Over.forget S)

theorem closed_two {S : Scheme.{0}} {X N G M₁ M₂ W₁ W₂ : Over S} (p : X ⟶ N) (q : X ⟶ G) {g₁ : M₁ ⟶ G} {g₂ : M₂ ⟶ G}
    [IsOpenImmersion g₁.left] [IsOpenImmersion g₂.left]
    (hc : ∀ x : G.left, x ∈ Set.range g₁.left ∨ x ∈ Set.range g₂.left)
    {a₁ : W₁ ⟶ X} {b₁ : W₁ ⟶ M₁} {a₂ : W₂ ⟶ X} {b₂ : W₂ ⟶ M₂}
    (h₁ : IsPullback a₁.left b₁.left q.left g₁.left) (h₂ : IsPullback a₂.left b₂.left q.left g₂.left)
    (c₁ : IsClosedImmersion (lift (a₁ ≫ p) b₁).left) (c₂ : IsClosedImmersion (lift (a₂ ≫ p) b₂).left) :
    IsClosedImmersion (lift p q).left := by
  have key : ∀ {M W : Over S} {g : M ⟶ G} {a : W ⟶ X} {b : W ⟶ M}, IsPullback a.left b.left q.left g.left →
      IsPullback a.left (lift (a ≫ p) b).left (lift p q).left (N ◁ g).left := by
    intro M W g a b h
    have e : a ≫ q = b ≫ g := Over.OverMorphism.ext h.w
    refine IsPullback.of_bot ?_ ?_ (pb_snd N g)
    · rwa [← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd]
    · rw [← Over.comp_left, ← Over.comp_left]
      congr 1
      ext <;> simp [e]
  have : IsOpenImmersion (N ◁ g₁).left := MorphismProperty.of_isPullback (P := @IsOpenImmersion) (pb_snd N g₁).flip ‹_›
  have : IsOpenImmersion (N ◁ g₂).left := MorphismProperty.of_isPullback (P := @IsOpenImmersion) (pb_snd N g₂).flip ‹_›
  refine target_two @IsClosedImmersion ?_ (key h₁) (key h₂) c₁ c₂
  intro z
  rcases hc ((snd N G).left z) with ⟨y, hy⟩ | ⟨y, hy⟩
  · obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback (pb_snd N g₁) z y hy.symm
    exact Or.inl ⟨w, hw⟩
  · obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback (pb_snd N g₂) z y hy.symm
    exact Or.inr ⟨w, hw⟩

theorem closed_swap {S : Scheme.{0}} {X N G : Over S} {p : X ⟶ N} {q : X ⟶ G}
    (h : IsClosedImmersion (lift p q).left) : IsClosedImmersion (lift q p).left := by
  have : lift q p = lift p q ≫ (β_ N G).hom := by ext <;> simp
  rw [this, Over.comp_left]
  have : IsIso (β_ N G).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (β_ N G).hom))
  infer_instance

theorem sep_iff {S : Scheme.{0}} (G : Over S) : IsSeparated G.hom ↔ IsClosedImmersion (lift (𝟙 G) (𝟙 G)).left := by
  have : (lift (𝟙 G) (𝟙 G)).left = pullback.diagonal G.hom := by
    apply pullback.hom_ext <;> simp
  rw [this]
  exact ⟨fun h => h.1, fun h => ⟨h⟩⟩

theorem ext_of_schemeDominant {W X Y Z : Scheme.{0}} {f g : X ⟶ Y} (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s)
    (d : W ⟶ X) [IsSchemeTheoreticallyDominant d] (hU : d ≫ f = d ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  haveI : IsSeparated Y'.hom := ‹IsSeparated s›
  let U' : Over Z := Over.mk (d ≫ f ≫ s)
  let d' : U' ⟶ X' := Over.homMk d
  have e : d' ≫ f' = d' ≫ g' := by
    ext1
    exact hU
  let l := equalizer.lift d' e
  have hd : d = l.left ≫ (equalizer.ι f' g').left := by
    rw [← Over.comp_left, equalizer.lift_ι]; rfl
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    apply le_bot_iff.1
    calc _ ≤ (l.left ≫ (equalizer.ι f' g').left).ker := Scheme.Hom.le_ker_comp _ _
      _ = ⊥ := by rw [← hd]; exact d.ker_eq_bot
  haveI : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.2 hker
  have h0 : IsIso ((Over.forget Z).map (equalizer.ι f' g')) := (inferInstance : IsIso (equalizer.ι f' g').left)
  have : IsIso (equalizer.ι f' g') := isIso_of_reflects_iso _ (Over.forget Z)
  have hfg : f' = g' := (cancel_epi (equalizer.ι f' g')).1 (equalizer.condition f' g')
  exact congrArg CommaMorphism.left hfg

theorem exists_sup {S : Scheme.{0}} {N W₁ W₂ : Over S} (p₁ : W₁ ⟶ N) (p₂ : W₂ ⟶ N) [IsOpenImmersion p₁.left]
    [IsOpenImmersion p₂.left] : ∃ (X : Over S) (p : X ⟶ N) (a₁ : W₁ ⟶ X) (a₂ : W₂ ⟶ X), IsOpenImmersion p.left ∧
      a₁ ≫ p = p₁ ∧ a₂ ≫ p = p₂ ∧ ∀ x, x ∈ Set.range a₁.left ∨ x ∈ Set.range a₂.left := by
  let U : N.left.Opens := p₁.left.opensRange ⊔ p₂.left.opensRange
  let X : Over S := Over.mk (U.ι ≫ N.hom)
  let p : X ⟶ N := Over.homMk U.ι rfl
  have op : IsOpenImmersion p.left := inferInstanceAs (IsOpenImmersion U.ι)
  have mk : ∀ {W : Over S} (p' : W ⟶ N) [IsOpenImmersion p'.left], p'.left.opensRange ≤ U →
      ∃ a : W ⟶ X, a ≫ p = p' := by
    intro W p' _ hle
    have hr : Set.range p'.left ⊆ Set.range U.ι := by rw [Scheme.Opens.range_ι]; exact hle
    refine ⟨Over.homMk (IsOpenImmersion.lift U.ι p'.left hr) ?_, Over.OverMorphism.ext ?_⟩
    · change _ ≫ U.ι ≫ N.hom = _
      rw [IsOpenImmersion.lift_fac_assoc, Over.w p']
    · exact IsOpenImmersion.lift_fac U.ι p'.left hr
  obtain ⟨a₁, e₁⟩ := mk p₁ le_sup_left
  obtain ⟨a₂, e₂⟩ := mk p₂ le_sup_right
  refine ⟨X, p, a₁, a₂, op, e₁, e₂, fun x => ?_⟩
  have hx : p.left x ∈ U := x.2
  rcases TopologicalSpace.Opens.mem_sup.1 hx with ⟨y, hy⟩ | ⟨y, hy⟩
  · refine Or.inl ⟨y, p.left.isOpenEmbedding.injective ?_⟩
    rw [← hy, ← e₁, Over.comp_left, Scheme.Hom.comp_apply]
  · refine Or.inr ⟨y, p.left.isOpenEmbedding.injective ?_⟩
    rw [← hy, ← e₂, Over.comp_left, Scheme.Hom.comp_apply]

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A : Over (Sp K)}

theorem j_isPullback (M : Model R A) : IsPullback M.j A.hom M.Y.hom (spMap (algebraMap R K)) := by
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  have h : M.e.inv.left ≫ pullback.snd M.Y.hom (spMap (algebraMap R K)) = A.hom ≫ 𝟙 _ := by
    rw [Category.comp_id]; exact Over.w M.e.inv
  have := (IsPullback.of_horiz_isIso ⟨h⟩).paste_horiz (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K)))
  rw [Category.id_comp] at this
  exact this

noncomputable def ofSquare (Y : Over (Sp R)) (h₁ : Smooth Y.hom) (h₂ : IsSeparated Y.hom) (h₃ : QuasiCompact Y.hom)
    {j : A.left ⟶ Y.left} (h : IsPullback j A.hom Y.hom (spMap (algebraMap R K))) : Model R A :=
  ⟨Y, Over.isoMk h.isoPullback.symm (h.isoPullback_inv_snd), h₁, h₂, h₃⟩

theorem ofSquare_j (Y : Over (Sp R)) (h₁ : Smooth Y.hom) (h₂ : IsSeparated Y.hom) (h₃ : QuasiCompact Y.hom)
    {j : A.left ⟶ Y.left} (h : IsPullback j A.hom Y.hom (spMap (algebraMap R K))) :
    (ofSquare Y h₁ h₂ h₃ h).j = j := h.isoPullback_hom_fst

variable [IsDomain R] [IsFractionRing R K]

theorem schDom_open (M : Model R A) {X : Scheme.{0}} (i : X ⟶ M.Y.left) [IsOpenImmersion i] {a : A.left ⟶ X}
    (h : a ≫ i = M.j) : IsSchemeTheoreticallyDominant a := by
  have := M.smooth
  have : IsSchemeTheoreticallyDominant (spMap (algebraMap R K)) := by
    have : IsDominant (spMap (algebraMap R K)) :=
      ⟨PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _ |>.2 (by
        exact ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)).le.trans bot_le)⟩
    exact IsSchemeTheoreticallyDominant.of_isDominant _
  have : IsSchemeTheoreticallyDominant M.j := IsSchemeTheoreticallyDominant.of_isPullback (j_isPullback M).flip
  have : QuasiCompact M.j := MorphismProperty.of_isPullback (P := @QuasiCompact) (j_isPullback M).flip inferInstance
  exact IsSchemeTheoreticallyDominant.of_isPullback (pb_mono h).flip

theorem pb_of_closed (N : Model R A) {X G M W : Over (Sp R)} (p : X ⟶ N.Y) [IsOpenImmersion p.left] (q : X ⟶ G)
    (g : M ⟶ G) [IsOpenImmersion g.left] (a : W ⟶ X) (b : W ⟶ M) (w : a.left ≫ q.left = b.left ≫ g.left)
    (hc : IsClosedImmersion (lift (a ≫ p) b).left) (j : A.left ⟶ W.left) (hj : j ≫ a.left ≫ p.left = N.j) :
    IsPullback a.left b.left q.left g.left := by
  let l : W.left ⟶ pullback q.left g.left := pullback.lift a.left b.left w
  let m : pullback q.left g.left ⟶ pullback N.Y.hom M.hom :=
    pullback.lift (pullback.fst _ _ ≫ p.left) (pullback.snd _ _) (by
      rw [Category.assoc, Over.w p, ← Over.w q, ← Over.w g, pullback.condition_assoc])
  have e : l ≫ m = (lift (a ≫ p) b).left := by
    apply pullback.hom_ext <;> simp [l, m]
  have : IsSeparated (m ≫ pullback.fst _ _) := by
    simp only [m, pullback.lift_fst]; infer_instance
  have : IsSeparated m := IsSeparated.of_comp m (pullback.fst _ _)
  have : IsClosedImmersion (l ≫ m) := e ▸ hc
  have : IsClosedImmersion l := IsClosedImmersion.of_comp l m
  have : IsSchemeTheoreticallyDominant (j ≫ l) :=
    schDom_open N (pullback.fst q.left g.left ≫ p.left) (by simp [l, ← hj])
  have : IsIso l := IsClosedImmersion.isIso_iff_ker_eq_bot.2
    (le_bot_iff.1 ((Scheme.Hom.le_ker_comp j l).trans (j ≫ l).ker_eq_bot.le))
  exact IsPullback.of_iso_pullback ⟨w⟩ (asIso l) (by simp [l]) (by simp [l])

theorem exists_union {M N : Model R A} (h : Compat M N) :
    ∃ (G : Model R A) (g₁ : M.Y ⟶ G.Y) (g₂ : N.Y ⟶ G.Y), IsOpenImmersion g₁.left ∧ IsOpenImmersion g₂.left ∧
      M.j ≫ g₁.left = G.j ∧ N.j ≫ g₂.left = G.j ∧ ∀ y, y ∈ Set.range g₁.left ∨ y ∈ Set.range g₂.left := by
  obtain ⟨W, a, b, ha, hb, ja, jb, hc⟩ := h
  let Y : Over (Sp R) := Over.mk (pushout.desc M.Y.hom N.Y.hom ((Over.w a).trans (Over.w b).symm))
  let g₁ : M.Y ⟶ Y := Over.homMk (pushout.inl a.left b.left) (pushout.inl_desc _ _ _)
  let g₂ : N.Y ⟶ Y := Over.homMk (pushout.inr a.left b.left) (pushout.inr_desc _ _ _)
  have o₁ : IsOpenImmersion g₁.left := GlobalTheory.GlueModels.isOpenImmersion_inl a.left b.left
  have o₂ : IsOpenImmersion g₂.left := GlobalTheory.GlueModels.isOpenImmersion_inr a.left b.left
  have cov : ∀ y, y ∈ Set.range g₁.left ∨ y ∈ Set.range g₂.left := GlobalTheory.GlueModels.pushout_cover a.left b.left
  have w : a.left ≫ g₁.left = b.left ≫ g₂.left := pushout.condition
  have ej : N.j ≫ g₂.left = M.j ≫ g₁.left := by rw [← ja, ← jb, Category.assoc, Category.assoc, w]
  have sm : Smooth Y.hom := source_two @Smooth cov (by rw [Over.w g₁]; exact M.smooth) (by rw [Over.w g₂]; exact N.smooth)
  have qc : QuasiCompact Y.hom := qc_two cov (by rw [Over.w g₁]; exact M.qc) (by rw [Over.w g₂]; exact N.qc)
  have oi : ∀ Z : Over (Sp R), IsOpenImmersion (𝟙 Z : Z ⟶ Z).left := fun Z => by rw [Over.id_left]; infer_instance
  have self : ∀ {Z : Over (Sp R)} (g : Z ⟶ Y) [IsOpenImmersion g.left],
      IsPullback (𝟙 Z : Z ⟶ Z).left (𝟙 Z : Z ⟶ Z).left g.left g.left := fun g _ => by
    rw [Over.id_left]; exact pb_mono (Category.id_comp _)
  have pb : IsPullback a.left b.left g₁.left g₂.left := by
    have := oi M.Y
    exact pb_of_closed M (𝟙 _) g₁ g₂ a b w (by rwa [Category.comp_id]) W.j (by simpa using ja)
  have c₁ : IsClosedImmersion (lift (𝟙 M.Y) g₁).left :=
    closed_two _ _ cov (self g₁) pb (by rw [Category.comp_id]; exact (sep_iff _).1 M.sep) (by rwa [Category.comp_id])
  have c₂ : IsClosedImmersion (lift (𝟙 N.Y) g₂).left :=
    closed_two _ _ cov pb.flip (self g₂) (by rw [Category.comp_id]; exact closed_swap hc)
      (by rw [Category.comp_id]; exact (sep_iff _).1 N.sep)
  have top : ∀ {Z : Over (Sp R)} (g : Z ⟶ Y),
      IsPullback g.left (𝟙 Z : Z ⟶ Z).left (𝟙 Y : Y ⟶ Y).left g.left := fun g => by
    rw [Over.id_left, Over.id_left]; exact pb_mono (Category.comp_id _)
  have sep : IsSeparated Y.hom := (sep_iff _).2 (closed_two _ _ cov (top g₁) (top g₂)
    (by rw [Category.comp_id]; exact closed_swap c₁) (by rw [Category.comp_id]; exact closed_swap c₂))
  have sq : IsPullback (M.j ≫ g₁.left) A.hom Y.hom (spMap (algebraMap R K)) :=
    GlobalTheory.GlueModels.isPullback_of_two cov (pb_mono rfl) (pb_mono ej)
      (by rw [Category.id_comp, Over.w g₁]; exact j_isPullback M)
      (by rw [Category.id_comp, Over.w g₂]; exact j_isPullback N)
  exact ⟨ofSquare Y sm sep qc sq, g₁, g₂, o₁, o₂, (ofSquare_j Y sm sep qc sq).symm,
    ej.trans (ofSquare_j Y sm sep qc sq).symm, cov⟩

theorem compat_of_cover {M₁ M₂ G N : Model R A} (g₁ : M₁.Y ⟶ G.Y) (g₂ : M₂.Y ⟶ G.Y) [IsOpenImmersion g₁.left]
    [IsOpenImmersion g₂.left] (j₁ : M₁.j ≫ g₁.left = G.j) (j₂ : M₂.j ≫ g₂.left = G.j)
    (cov : ∀ y, y ∈ Set.range g₁.left ∨ y ∈ Set.range g₂.left) (h₁ : Compat N M₁) (h₂ : Compat N M₂) :
    Compat N G := by
  obtain ⟨W₁, p₁, b₁, hp₁, hb₁, jp₁, jb₁, hc₁⟩ := h₁
  obtain ⟨W₂, p₂, b₂, hp₂, hb₂, jp₂, jb₂, hc₂⟩ := h₂
  obtain ⟨X, p, a₁, a₂, op, rfl, rfl, cx⟩ := exists_sup p₁ p₂
  rw [Over.comp_left] at hp₁ hp₂ jp₁ jp₂
  have o₁ : IsOpenImmersion a₁.left := IsOpenImmersion.of_comp _ p.left
  have o₂ : IsOpenImmersion a₂.left := IsOpenImmersion.of_comp _ p.left
  have ej : W₂.j ≫ a₂.left = W₁.j ≫ a₁.left := by
    rw [← cancel_mono p.left, Category.assoc, Category.assoc, jp₁, jp₂]
  have := G.sep
  have hab : pullback.fst a₁.left a₂.left ≫ b₁.left ≫ g₁.left = pullback.snd a₁.left a₂.left ≫ b₂.left ≫ g₂.left := by
    have : IsSchemeTheoreticallyDominant (pullback.lift W₁.j W₂.j ej.symm) :=
      schDom_open W₁ (pullback.fst a₁.left a₂.left) (pullback.lift_fst _ _ _)
    refine ext_of_schemeDominant G.Y.hom ?_ (pullback.lift W₁.j W₂.j ej.symm) ?_
    · simp only [Category.assoc, Over.w]
      rw [← Over.w a₁, ← Over.w a₂, pullback.condition_assoc]
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, reassoc_of% jb₁, reassoc_of% jb₂, j₁, j₂]
  obtain ⟨φ, f₁, f₂⟩ := GlobalTheory.GlueModels.exists_glue (IsPullback.of_hasPullback a₁.left a₂.left) cx _ _ hab
  have hφ : φ ≫ G.Y.hom = X.hom := by
    refine (coverTwo a₁.left a₂.left cx).hom_ext _ _ ?_
    rintro (_ | _)
    · change a₁.left ≫ φ ≫ _ = a₁.left ≫ _
      rw [reassoc_of% f₁]; simp only [Over.w]
    · change a₂.left ≫ φ ≫ _ = a₂.left ≫ _
      rw [reassoc_of% f₂]; simp only [Over.w]
  let q : X ⟶ G.Y := Over.homMk φ hφ
  have pb₁ : IsPullback a₁.left b₁.left q.left g₁.left := pb_of_closed N p q g₁ a₁ b₁ f₁ hc₁ W₁.j jp₁
  have pb₂ : IsPullback a₂.left b₂.left q.left g₂.left := pb_of_closed N p q g₂ a₂ b₂ f₂ hc₂ W₂.j jp₂
  have := N.smooth
  have := N.sep
  have sm : Smooth X.hom := by rw [← Over.w p]; infer_instance
  have sep : IsSeparated X.hom := by rw [← Over.w p]; infer_instance
  have qc : QuasiCompact X.hom := qc_two cx (by rw [Over.w a₁]; exact W₁.qc) (by rw [Over.w a₂]; exact W₂.qc)
  have sq : IsPullback (W₁.j ≫ a₁.left) A.hom X.hom (spMap (algebraMap R K)) := by
    have := (pb_mono (a := W₁.j ≫ a₁.left) (i := p.left) (j := N.j) (by rw [Category.assoc, jp₁])).paste_vert
      (j_isPullback N)
    rwa [Category.id_comp, Over.w p] at this
  refine ⟨ofSquare X sm sep qc sq, p, q, op, target_two @IsOpenImmersion cov pb₁ pb₂ hb₁ hb₂, ?_, ?_,
    closed_two p q cov pb₁ pb₂ hc₁ hc₂⟩
  · rw [ofSquare_j, Category.assoc, jp₁]
  · rw [ofSquare_j, Category.assoc]
    change W₁.j ≫ a₁.left ≫ φ = _
    rw [f₁, reassoc_of% jb₁, j₁]

theorem glue_compat : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) (n : ℕ) (M : Fin (n + 1) → Model R A), (∀ i j, Compat (M i) (M j)) → ∃ G : Model R A, (∀ i, (M i).Le G) ∧ (∀ y : G.Y.left, ∃ (i : Fin (n + 1)) (g : (M i).Y ⟶ G.Y), IsOpenImmersion g.left ∧ (M i).j ≫ g.left = G.j ∧ y ∈ Set.range g.left) ∧ ∀ N : Model R A, (∀ i, Compat N (M i)) → Compat N G := by
  intro R K _ _ _ _ _ _ A n
  induction n with
  | zero =>
    intro M _
    refine ⟨M 0, fun i => ?_, fun y => ⟨0, 𝟙 _, ?_, by simp, by simp⟩, fun N h => h 0⟩
    · obtain rfl : i = 0 := Subsingleton.elim (α := Fin 1) _ _
      exact Model.le_refl _
    · rw [Over.id_left]; infer_instance
  | succ n ih =>
    intro M hM
    obtain ⟨G₀, le₀, cov₀, comp₀⟩ := ih (fun i => M i.succ) (fun i j => hM _ _)
    obtain ⟨G, g₁, g₂, o₁, o₂, j₁, j₂, cov⟩ := exists_union (comp₀ (M 0) (fun i => hM _ _))
    refine ⟨G, fun i => ?_, fun y => ?_, fun N hN => compat_of_cover g₁ g₂ j₁ j₂ cov (hN 0) (comp₀ N fun i => hN _)⟩
    · refine Fin.cases ⟨g₁, o₁, j₁⟩ (fun i => (le₀ i).trans ⟨g₂, o₂, j₂⟩) i
    · rcases cov y with hy | ⟨x, rfl⟩
      · exact ⟨0, g₁, o₁, j₁, hy⟩
      · obtain ⟨i, g, og, jg, z, rfl⟩ := cov₀ x
        refine ⟨i.succ, g ≫ g₂, ?_, ?_, z, ?_⟩
        · rw [Over.comp_left]; infer_instance
        · rw [Over.comp_left, reassoc_of% jg, j₂]
        · rw [Over.comp_left, Scheme.Hom.comp_apply]

end GlobalTheory.SS.GlueCompat
