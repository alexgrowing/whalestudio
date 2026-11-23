import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open TopologicalSpace

namespace GlobalTheory.SecGlue

section Fn

variable {X Y Z : Scheme.{0}}

theorem gs_appLE (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (V : Y.Opens) (e : V ≤ g ⁻¹ᵁ U)
    (h : r z ∈ V) (a : Γ(X, U)) : gs r z V ((g.appLE U V e).hom a) = gs (r ≫ g) z U a :=
  (gs_res r z e h ((g.app U).hom a)).trans (gs_pull r g z U (e h) a)

theorem gs_id (r : Z ⟶ X) (z : Z) (U : X.Opens) (h : r z ∈ U) (a : Γ(X, U)) :
    gs r z U a = (r.stalkMap z).hom (gs (𝟙 X) (r z) U a) := by
  rw [gs_eq r z U h, gs_eq (𝟙 X) (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r U z h _).symm

theorem gs_inj (r : Z ⟶ X) [IsOpenImmersion r] (z : Z) {U V : X.Opens} (h : r z ∈ U) (h' : r z ∈ V)
    {a : Γ(X, U)} {b : Γ(X, V)} (e : gs r z U a = gs r z V b) :
    gs (𝟙 X) (r z) U a = gs (𝟙 X) (r z) V b := by
  rw [gs_id r z U h, gs_id r z V h'] at e
  exact (ConcreteCategory.bijective_of_isIso (r.stalkMap z)).1 e

variable {J : Type} {T : J → Scheme.{0}} (a : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (a i)]

theorem ext_cover (hc : ∀ x : X, ∃ i y, a i y = x) {V : X.Opens} {s t : Γ(X, V)}
    (h : ∀ i y, a i y ∈ V → gs (a i) y V s = gs (a i) y V t) : s = t :=
  fn_ext fun x hx => by
    obtain ⟨i, y, rfl⟩ := hc x
    exact gs_inj (a i) y hx hx (h i y hx)

theorem exists_appLE_eq (r : Z ⟶ X) [IsOpenImmersion r] {U : X.Opens} (hU : U ≤ r.opensRange)
    {W : Z.Opens} (h : W = r ⁻¹ᵁ U) (u : Γ(Z, W)) : ∃ w, (r.appLE U W h.le).hom w = u := by
  subst h
  have := r.isIso_app U hU
  rw [← r.app_eq_appLE]
  exact (ConcreteCategory.bijective_of_isIso (r.app U)).2 u

theorem glue_cover (hc : ∀ x : X, ∃ i y, a i y = x) (V : X.Opens) (W : ∀ i, (T i).Opens)
    (hW : ∀ i y, y ∈ W i ↔ a i y ∈ V) (u : ∀ i, Γ(T i, W i))
    (h : ∀ i j y y', a i y = a j y' → y ∈ W i → ∃ (Z : Scheme.{0}) (b : Z ⟶ T i) (c : Z ⟶ T j) (z : Z),
      IsOpenImmersion (b ≫ a i) ∧ b ≫ a i = c ≫ a j ∧ b z = y ∧ gs b z _ (u i) = gs c z _ (u j)) :
    ∃ s : Γ(X, V), ∀ i y, y ∈ W i → gs (a i) y V s = gs (𝟙 _) y _ (u i) := by
  have e : ∀ i, W i = a i ⁻¹ᵁ (V ⊓ (a i).opensRange) := fun i => by
    ext y
    exact ⟨fun h => ⟨(hW i y).1 h, y, rfl⟩, fun h => (hW i y).2 h.1⟩
  choose w hw using fun i => exists_appLE_eq (a i) inf_le_right (e i) (u i)
  have v : ∀ i (Z : Scheme.{0}) (r : Z ⟶ T i) (z : Z), r z ∈ W i →
      gs r z _ (u i) = gs (r ≫ a i) z _ (w i) := fun i Z r z hz => by
    rw [← hw i, gs_appLE r (a i) z _ _ _ hz]
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun i => V ⊓ (a i).opensRange) V
    (fun i => homOfLE inf_le_left) (fun x hx => by
      obtain ⟨i, y, rfl⟩ := hc x
      exact Opens.mem_iSup.2 ⟨i, hx, y, rfl⟩) w
    (fun k l => fn_ext (V := (V ⊓ (a k).opensRange) ⊓ (V ⊓ (a l).opensRange)) fun x hx => by
      refine (gs_res (𝟙 X) x inf_le_left hx _).trans (Eq.trans ?_
        (gs_res (𝟙 X) x inf_le_right hx _).symm)
      obtain ⟨y, rfl⟩ := hx.1.2
      obtain ⟨y', hy'⟩ := hx.2.2
      obtain ⟨Z, b, c, z, _, e1, rfl, e2⟩ := h k l y y' hy'.symm ((hW k y).2 hx.1.1)
      have hcz : c z ∈ W l := by
        rw [hW, ← Scheme.Hom.comp_apply, ← e1]; exact hx.1.1
      rw [v k Z b z ((hW k _).2 hx.1.1), v l Z c z hcz, ← e1] at e2
      exact gs_inj (b ≫ a k) z hx.1 hx.2 e2)
  refine ⟨s, fun i y hy => ?_⟩
  rw [v i _ (𝟙 _) y hy, Category.id_comp, ← hs i]
  exact (gs_res (a i) y inf_le_left ((e i).le hy) s).symm

end Fn

section Sec

variable {A X Y Z : Scheme.{0}} {L : LB A} {K : Type} [Fintype K] {ε : K → ℤ}

def Rel (h : Y ⟶ X) {q : X ⟶ A} {q' : Y ⟶ A} (s : LB.Sec (LB.LinComb L (fun _ : K => q) ε))
    (t : LB.Sec (LB.LinComb L (fun _ : K => q') ε)) : Prop :=
  ∀ (j : K → L.ι) (hh : LB.wchart L (fun _ : K => q') j ≤ h ⁻¹ᵁ LB.wchart L (fun _ : K => q) j),
    (h.appLE _ _ hh).hom (s.f j) = t.f j

theorem mem_chart {h : Y ⟶ X} {q : X ⟶ A} {q' : Y ⟶ A} (e : h ≫ q = q') (j : K → L.ι) (y : Y) :
    y ∈ LB.wchart L (fun _ : K => q') j ↔ h y ∈ LB.wchart L (fun _ : K => q) j := by
  subst e
  exact ⟨fun hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k,
    fun hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k⟩

theorem Rel.gs_eq {h : Y ⟶ X} {q : X ⟶ A} {q' : Y ⟶ A} (e : h ≫ q = q')
    {s : LB.Sec (LB.LinComb L (fun _ : K => q) ε)} {t : LB.Sec (LB.LinComb L (fun _ : K => q') ε)}
    (H : Rel h s t) (j : K → L.ι) (r : Z ⟶ Y) (z : Z) (hz : r z ∈ LB.wchart L (fun _ : K => q') j) :
    gs (r ≫ h) z (LB.wchart L (fun _ : K => q) j) (s.f j) =
      gs r z (LB.wchart L (fun _ : K => q') j) (t.f j) := by
  rw [← H j (fun y hy => (mem_chart e j y).1 hy)]
  exact (gs_appLE r h z _ _ _ hz _).symm

theorem compat_at {φ : K → (X ⟶ A)} (r : Z ⟶ X) (z : Z) {j j' : K → L.ι}
    (f : Γ(X, LB.wchart L φ j)) (f' : Γ(X, LB.wchart L φ j'))
    (hm : r z ∈ LB.wchart L φ j ⊓ LB.wchart L φ j')
    (h : gs r z _ f = (trF φ ε r z j j').val * gs r z _ f') :
    gs r z (LB.wchart L φ j ⊓ LB.wchart L φ j') ((X.presheaf.map (homOfLE inf_le_left).op).hom f) =
      gs r z (LB.wchart L φ j ⊓ LB.wchart L φ j') (((LB.LinComb L φ ε).g j j').val *
        (X.presheaf.map (homOfLE inf_le_right).op).hom f') := by
  refine (gs_res r z _ hm _).trans (h.trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) ?_ (gs_res r z _ hm _))).symm)
  exact (gs_unit r z _ hm _).trans (congrArg Units.val (gm_linComb L φ ε r z j j' hm.1 hm.2))

theorem trF_comp {h : Y ⟶ X} {q : X ⟶ A} {q' : Y ⟶ A} (e : h ≫ q = q') (y : Y) (j j' : K → L.ι) :
    trF (fun _ : K => q') ε (𝟙 Y) y j j' = trF (fun _ : K => q) ε h y j j' := by
  subst e
  simp only [trF, Category.id_comp]

theorem exists_rel {h : Y ⟶ X} {q : X ⟶ A} {q' : Y ⟶ A} (e : h ≫ q = q')
    (s : LB.Sec (LB.LinComb L (fun _ : K => q) ε)) :
    ∃ t : LB.Sec (LB.LinComb L (fun _ : K => q') ε), Rel h s t := by
  refine ⟨⟨fun j => (h.appLE (LB.wchart L (fun _ : K => q) j) (LB.wchart L (fun _ : K => q') j)
    (fun y hy => (mem_chart e j y).1 hy)).hom (s.f j), fun (j j' : K → L.ι) => ?_⟩,
    fun j hh => rfl⟩
  refine fn_ext fun y hy => compat_at (𝟙 Y) y _ _ hy ?_
  refine (gs_appLE (𝟙 Y) h y _ _ _ hy.1 _).trans (Eq.trans ?_
    (congrArg (_ * ·) (gs_appLE (𝟙 Y) h y _ _ _ hy.2 _).symm))
  rw [Category.id_comp]
  exact (sec_trans s h y ((mem_chart e j y).1 hy.1) ((mem_chart e j' y).1 hy.2)).trans
    (congrArg (fun u => Units.val u * _) (trF_comp e y j j').symm)

theorem sec_ext {M : LB X} {s t : LB.Sec M} (h : ∀ j, s.f j = t.f j) : s = t := by
  cases s; cases t
  congr
  exact funext h

theorem glue_rel {J : Type} {T : J → Scheme.{0}} (a : ∀ i, T i ⟶ X) [∀ i, IsOpenImmersion (a i)]
    (hc : ∀ x : X, ∃ i y, a i y = x) (q : X ⟶ A) (q' : ∀ i, T i ⟶ A) (e : ∀ i, a i ≫ q = q' i)
    (s : ∀ i, LB.Sec (LB.LinComb L (fun _ : K => q' i) ε))
    (h : ∀ i j y y', a i y = a j y' → ∃ (Z : Scheme.{0}) (b : Z ⟶ T i) (c : Z ⟶ T j) (z : Z)
      (p : Z ⟶ A) (t : LB.Sec (LB.LinComb L (fun _ : K => p) ε)),
      IsOpenImmersion (b ≫ a i) ∧ b ≫ a i = c ≫ a j ∧ b z = y ∧ b ≫ q' i = p ∧
        Rel b (s i) t ∧ Rel c (s j) t) :
    ∃! s₀ : LB.Sec (LB.LinComb L (fun _ : K => q) ε), ∀ i, Rel (a i) s₀ (s i) := by
  have key : ∀ k : K → L.ι, ∃ f : Γ(X, LB.wchart L (fun _ : K => q) k), ∀ i y,
      y ∈ LB.wchart L (fun _ : K => q' i) k →
      gs (a i) y _ f = gs (𝟙 _) y (LB.wchart L (fun _ : K => q' i) k) ((s i).f k) := fun k =>
    glue_cover a hc _ (fun i => LB.wchart L (fun _ : K => q' i) k) (fun i y => mem_chart (e i) k y)
      (fun i => (s i).f k) fun i j y y' hy hk => by
        obtain ⟨Z, b, c, z, p, t, h1, h2, rfl, h4, h5, h6⟩ := h i j y y' hy
        have h7 : c ≫ q' j = p := by rw [← h4, ← e i, ← e j, reassoc_of% h2]
        have hz := (mem_chart h4 k z).2 hk
        have h8 := h5.gs_eq h4 k (𝟙 Z) z hz
        have h9 := h6.gs_eq h7 k (𝟙 Z) z hz
        rw [Category.id_comp] at h8 h9
        exact ⟨Z, b, c, z, h1, h2, rfl, h8.trans h9.symm⟩
  choose f hf using key
  refine ⟨⟨f, fun (k k' : K → L.ι) => ?_⟩, fun i k hh => ?_, fun t ht => sec_ext fun k => ?_⟩
  · refine ext_cover a hc fun i y hy => compat_at (a i) y _ _ hy ?_
    have h1 := (mem_chart (e i) k y).2 hy.1
    have h2 := (mem_chart (e i) k' y).2 hy.2
    rw [hf k i y h1, hf k' i y h2]
    exact (sec_trans (s i) (𝟙 _) y h1 h2).trans
      (congrArg (fun u => Units.val u * _) (trF_comp (e i) y k k'))
  · refine fn_ext fun y hy => (gs_appLE (𝟙 _) (a i) y _ _ _ hy _).trans ?_
    rw [Category.id_comp]
    exact hf k i y hy
  · refine ext_cover a hc fun i y hy => ?_
    have h1 := (mem_chart (e i) k y).2 hy
    have h2 := (ht i).gs_eq (e i) k (𝟙 _) y h1
    rw [Category.id_comp] at h2
    exact h2.trans (hf k i y h1).symm

end Sec

section Fib

variable {B : Scheme.{0}} (G : Over B) {S T : Scheme.{0}}

def Can (f : T ⟶ S) (x : S ⟶ B) (x' : T ⟶ B) (pm : (Over.mk x' ⊗ G).left ⟶ (Over.mk x ⊗ G).left) : Prop :=
  pm ≫ (snd (Over.mk x) G).left = (snd (Over.mk x') G).left ∧
    pm ≫ (fst (Over.mk x) G).left = (fst (Over.mk x') G).left ≫ f

variable {G}

theorem exists_can {f : T ⟶ S} {x : S ⟶ B} {x' : T ⟶ B} (e : f ≫ x = x') : ∃ pm, Can G f x x' pm :=
  ⟨((Over.homMk f e : Over.mk x' ⟶ Over.mk x) ▷ G).left,
    congrArg (·.left) (whiskerRight_snd (Over.homMk f e : Over.mk x' ⟶ Over.mk x) G),
    congrArg (·.left) (whiskerRight_fst (Over.homMk f e : Over.mk x' ⟶ Over.mk x) G)⟩

theorem Can.unique {f : T ⟶ S} {x : S ⟶ B} {x' : T ⟶ B} {pm pm'} (h : Can G f x x' pm)
    (h' : Can G f x x' pm') : pm = pm' :=
  pullback.hom_ext (f := x) (g := G.hom) (h.2.trans h'.2.symm) (h.1.trans h'.1.symm)

theorem Can.comp {U : Scheme.{0}} {f : T ⟶ S} {g : U ⟶ T} {x : S ⟶ B} {x' : T ⟶ B} {x'' : U ⟶ B} {pm pm'}
    (h : Can G f x x' pm) (h' : Can G g x' x'' pm') : Can G (g ≫ f) x x'' (pm' ≫ pm) :=
  ⟨by rw [Category.assoc, h.1, h'.1], by
    rw [Category.assoc, h.2, ← Category.assoc, h'.2]
    exact Category.assoc _ _ _⟩

theorem Can.isPullback {f : T ⟶ S} {x : S ⟶ B} {x' : T ⟶ B} (e : f ≫ x = x') {pm}
    (h : Can G f x x' pm) :
    IsPullback pm (fst (Over.mk x') G).left (fst (Over.mk x) G).left f := by
  have h1 : IsPullback (snd (Over.mk x) G).left (fst (Over.mk x) G).left G.hom x :=
    (IsPullback.of_hasPullback x G.hom).flip
  have h2 : IsPullback (snd (Over.mk x') G).left (fst (Over.mk x') G).left G.hom x' :=
    (IsPullback.of_hasPullback x' G.hom).flip
  refine IsPullback.of_right ?_ h.2 h1
  rw [h.1]
  exact e ▸ h2

end Fib

theorem away_open {S : Type} [CommRing S] (r : S) :
    IsOpenImmersion (spMap (algebraMap S (Localization.Away r))) :=
  IsOpenImmersion.of_isLocalization r

theorem away_range {S : Type} [CommRing S] (r : S) (p : PrimeSpectrum S) :
    (∃ y, spMap (algebraMap S (Localization.Away r)) y = p) ↔ r ∉ p.asIdeal :=
  Set.ext_iff.1 (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r) p

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S) (ψ : S →+* T) :
    spMap ψ ≫ spMap φ = spMap (ψ.comp φ) := (Spec.map_comp _ _).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem scal_one' {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (i) : scal x 1 i = 1 := by
  simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_one]

theorem secBC_iff {S T : Type} [CommRing S] [CommRing T] {φ : S →+* T} {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    {pm} (h : Can Xo.univ.t.G (spMap φ) x x' pm) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) :
    SecBC φ 1 x x' s s' ↔ Rel pm s s' := by
  have e : ∀ j, scal x 1 j * s.f j = s.f j := fun j => by rw [scal_one', _root_.one_mul]
  constructor
  · rintro ⟨pm', h1, h2, h3⟩ j hh
    obtain rfl : pm' = pm := Can.unique ⟨h1, h2⟩ h
    exact (congrArg _ (e j).symm).trans (h3 j hh)
  · exact fun H => ⟨pm, h.1, h.2, fun j hh => (congrArg _ (e j)).trans (H j hh)⟩

theorem existsUnique_glue : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (n : ℕ) (h : Fin n → S), Ideal.span (Set.range h) = ⊤ → ∀ s : ∀ i, LB.Sec (PPx (spMap (algebraMap S (Localization.Away (h i))) ≫ x)), (∀ i j (α : Localization.Away (h i) →+* Localization.Away (h i * h j)) (β : Localization.Away (h j) →+* Localization.Away (h i * h j)), α.comp (algebraMap S (Localization.Away (h i))) = (algebraMap S (Localization.Away (h i * h j))) → β.comp (algebraMap S (Localization.Away (h j))) = (algebraMap S (Localization.Away (h i * h j))) → ∀ t : LB.Sec (PPx (spMap (algebraMap S (Localization.Away (h i * h j))) ≫ x)), SecBC α 1 _ _ (s i) t → SecBC β 1 _ _ (s j) t) → ∃! s₀ : LB.Sec (PPx x), ∀ i, SecBC (algebraMap S (Localization.Away (h i))) 1 x _ s₀ (s i) := by
  intro E _ _ _ H Dw l Xo S _ x n h hspan s hs
  choose a ha using fun i => exists_can (G := Xo.univ.t.G)
    (f := spMap (algebraMap S (Localization.Away (h i)))) (x := x) rfl
  have hop : ∀ (r : S) {pm}, Can Xo.univ.t.G (spMap (algebraMap S (Localization.Away r))) x
      (spMap (algebraMap S (Localization.Away r)) ≫ x) pm → IsOpenImmersion pm := fun r pm hp =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hp.isPullback rfl).flip (away_open r)
  have hra : ∀ (r : S) {pm}, Can Xo.univ.t.G (spMap (algebraMap S (Localization.Away r))) x
      (spMap (algebraMap S (Localization.Away r)) ≫ x) pm → ∀ p : Gx x,
      (∃ y, pm y = p) ↔ r ∉ PrimeSpectrum.asIdeal ((fst (Over.mk x) Xo.univ.t.G).left p) := by
    intro r pm hp p
    refine Iff.trans ⟨?_, ?_⟩ (away_range r _)
    · rintro ⟨y, rfl⟩
      exact ⟨_, (congrArg (fun q => q y) hp.2).symm⟩
    · rintro ⟨w, hw⟩
      obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback (hp.isPullback rfl) p w hw.symm
      exact ⟨y, hy⟩
  haveI : ∀ i, IsOpenImmersion (a i) := fun i => hop _ (ha i)
  simp only [fun i => secBC_iff (ha i)]
  refine glue_rel a (fun p => ?_) _ _ (fun i => (ha i).1) s fun i j y y' hy => ?_
  · by_contra hp
    let P : PrimeSpectrum S := (fst (Over.mk x) Xo.univ.t.G).left p
    refine P.isPrime.ne_top (top_le_iff.1 (hspan ▸ Ideal.span_le.2 ?_))
    rintro _ ⟨i, rfl⟩
    by_contra hi
    exact hp ⟨i, (hra _ (ha i) p).2 hi⟩
  · let α : Localization.Away (h i) →+* Localization.Away (h i * h j) :=
      IsLocalization.Away.awayToAwayRight (h i) (h j)
    let β : Localization.Away (h j) →+* Localization.Away (h i * h j) :=
      IsLocalization.Away.awayToAwayLeft (h j) (h i)
    have hα : α.comp (algebraMap S _) = algebraMap S _ :=
      RingHom.ext fun r => IsLocalization.Away.awayToAwayRight_eq (h i) (h j) r
    have hβ : β.comp (algebraMap S _) = algebraMap S _ :=
      RingHom.ext fun r => IsLocalization.Away.awayToAwayLeft_eq (h j) (h i) r
    obtain ⟨b, hb⟩ := exists_can (G := Xo.univ.t.G) (f := spMap α)
      (x := spMap (algebraMap S (Localization.Away (h i))) ≫ x)
      (x' := spMap (algebraMap S (Localization.Away (h i * h j))) ≫ x)
      (by rw [← Category.assoc, spMap_comp', hα])
    obtain ⟨c, hc⟩ := exists_can (G := Xo.univ.t.G) (f := spMap β)
      (x := spMap (algebraMap S (Localization.Away (h j))) ≫ x)
      (x' := spMap (algebraMap S (Localization.Away (h i * h j))) ≫ x)
      (by rw [← Category.assoc, spMap_comp', hβ])
    have h1 := (ha i).comp hb
    have h2 := (ha j).comp hc
    rw [spMap_comp', hα] at h1
    rw [spMap_comp', hβ] at h2
    obtain ⟨t, ht⟩ := exists_rel hb.1 (s i)
    obtain ⟨z, hz⟩ := (hra _ h1 (a i y)).2 fun hm => by
      rcases (PrimeSpectrum.isPrime _).mem_or_mem hm with hm | hm
      · exact (hra _ (ha i) _).1 ⟨y, rfl⟩ hm
      · exact (hra _ (ha j) _).1 ⟨y', hy.symm⟩ hm
    exact ⟨_, b, c, z, _, t, hop _ h1, h1.unique h2, (a i).isOpenEmbedding.injective hz, hb.1, ht,
      (secBC_iff hc _ _).1 (hs i j α β hα hβ t ((secBC_iff hb _ _).2 ht))⟩

end GlobalTheory.SecGlue
