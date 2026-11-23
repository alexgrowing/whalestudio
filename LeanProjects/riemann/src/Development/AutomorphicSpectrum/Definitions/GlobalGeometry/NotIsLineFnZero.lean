import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsConstMul

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Fl.FlatModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

def baseOf {F : Type} [Field F] (y : Sp F ⟶ Xo.XF c) : c.F →+* F :=
  (Spec.preimage (y ≫ pullback.snd _ _)).hom

theorem baseOf_eq {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c} {β : c.F →+* F}
    (h : y ≫ pullback.snd _ _ = spMap β) : baseOf y = β := by
  unfold baseOf
  rw [h]
  simp [spMap]

def scale (a : c.F) (φ : FrameFn Xo c) : FrameFn Xo c := fun F _ y v w => baseOf y a * φ F y v w

variable {U : Set (Xo.XF c)} {τ : E →+* ℂ} {φ : FrameFn Xo c} {a : c.F}

theorem isLineFn_scale (ha : a ≠ 0) (h : IsLineFn U τ φ) : IsLineFn U τ (scale a φ) where
  ne F _ β y v w hf := mul_ne_zero ((map_ne_zero _).2 ha) (h.ne F β y v w hf)
  chg F _ β y v w v' w' A B h1 h2 h3 h4 := by
    simp only [scale, _root_.mul_assoc, h.chg F β y v w v' w' A B h1 h2 h3 h4]
  nat F F' _ _ f β y v w y' v' w' h1 h2 h3 h4 := by
    have hb : baseOf y' = f.comp β := baseOf_eq (by
      rw [h2, Category.assoc, h1.1, ← Spec.map_comp]; rfl)
    simp only [scale, h.nat F F' f β y v w y' v' w' h1 h2 h3 h4, hb, baseOf_eq h1.1, map_mul, RingHom.comp_apply]

theorem isFlatGen_scale {g : ℕ} {ty : Fin g → (E →+* ℂ)} {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty}
    {i : Fin FU.n} (ha : a ≠ 0) (h : IsFlatGen U τ φ FU i) : IsFlatGen U τ (scale a φ) FU i where
  mem := h.mem
  line := isLineFn_scale ha h.line
  flat := by
    obtain ⟨e, ρ, he, hc⟩ := h.flat
    refine ⟨e, (a : ℂ) * ρ, he, fun P y v w V W C Fm B h1 h2 h3 h4 h5 h6 h7 h8 => ?_⟩
    rw [← hc P y v w V W C Fm B h1 h2 h3 h4 h5 h6 h7 h8]
    simp only [scale, baseOf_eq h3.1, _root_.mul_assoc]
    rfl

theorem hasNorms_scale (ha : a ≠ 0) (hl : IsLineFn U τ φ) {N : LogNorms c.F} (h : HasNorms U τ φ N) :
    HasNorms U τ (scale a φ)
      ⟨fun s => (LogNorms.ofElt a).inf s + N.inf s, fun p κ => (LogNorms.ofElt a).fin p κ + N.fin p κ⟩ := by
  refine ⟨fun s y v w Γ Δ h1 h2 h3 => ?_, fun p κ V K _ _ _ _ _ _ j β y v w T tK m m' h1 h2 h3 h4 h5 => ?_⟩
  · have := h.1 s y v w Γ Δ h1 h2 h3
    simp only [scale, baseOf_eq h1.1, norm_mul, LogNorms.ofElt]
    rw [Real.log_mul (norm_ne_zero_iff.2 ((map_ne_zero _).2 ha)) (norm_ne_zero_iff.2 (hl.ne _ s y v w h1))]
    linarith
  · have := h.2 p κ V K j β y v w T tK m m' h1 h2 h3 h4 h5
    simp only [scale, baseOf_eq h3.1, map_mul, norm_mul, LogNorms.ofElt]
    rw [Real.log_mul (norm_ne_zero_iff.2 ((map_ne_zero _).2 ((map_ne_zero _).2 ha)))
      (norm_ne_zero_iff.2 ((map_ne_zero _).2 (hl.ne _ β y v w h3))), this, ← h2]
    simp only [RingHom.comp_apply]
    ring

theorem inf_unique {N N' : LogNorms c.F} (h : HasNorms U τ φ N) (h' : HasNorms U τ φ N') (s : c.F →+* ℂ)
    (y : Sp ℂ ⟶ Xo.XF c) (v w Γ Δ) (h1 : IsFramed U τ s y v w)
    (h2 : IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) v Γ)
    (h3 : IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L (under y) w Δ) : N.inf s = N'.inf s :=
  (h.1 s y v w Γ Δ h1 h2 h3).symm.trans (h'.1 s y v w Γ Δ h1 h2 h3)

theorem isLineFn_one (hp : D.p = 0) (hq : D.q = 0) : IsLineFn U τ (fun _ _ _ _ _ => 1) where
  ne _ _ _ _ _ _ _ := one_ne_zero
  chg F _ β y v w v' w' A B _ _ _ _ := by
    have : IsEmpty (Fin D.p) := by rw [hp]; infer_instance
    have : IsEmpty (Fin D.q) := by rw [hq]; infer_instance
    simp [Matrix.det_isEmpty]
  nat _ _ _ _ f _ _ _ _ _ _ _ _ _ _ _ := (map_one f).symm

theorem not_isLineFn_zero {F : Type} [Field F] {β : c.F →+* F} {y : Sp F ⟶ Xo.XF c} {v w}
    (h : IsFramed U τ β y v w) : ¬ IsLineFn U τ (fun _ _ _ _ _ => 0) := fun h' => h'.ne F β y v w h rfl

theorem epsMul_zero_comp {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S}
    {v : epsAt x ⟶ G} (hv : IsTanAt G x v) : spMap (epsMul (0 : R)) ≫ v.left = (1 : epsAt x ⟶ G).left := by
  have h0 : epsMul (0 : R) = (algebraMap R (DualNumber R)).comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
    ext z <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  have h1 : spMap (epsMul (0 : R)) = spMap (algebraMap R (DualNumber R)) ≫
      spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
    rw [h0, ← Spec.map_comp]; rfl
  rw [h1, Category.assoc]
  erw [hv]
  let k : epsAt x ⟶ Over.mk x := Over.homMk (spMap (algebraMap R (DualNumber R))) rfl
  have := congrArg (fun t => t.left) (MonObj.comp_one k (M := G))
  exact this

theorem isComb_one {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {n : ℕ}
    {v : Fin n → (epsAt x ⟶ G)} (hv : ∀ i, IsTanAt G x (v i)) (i : Fin n) :
    IsComb ((1 : Matrix (Fin n) (Fin n) R) i) v (v i) := by
  classical
  refine ⟨fun j => if i = j then v j else 1, fun j => ?_, ?_⟩
  · by_cases h : i = j
    · have h1 : epsMul (1 : R) = RingHom.id _ := by ext z <;> simp [epsMul]
      simp [h, Matrix.one_apply, h1, spMap]
    · simp only [h, Matrix.one_apply, if_false]
      exact (epsMul_zero_comp (hv j)).symm
  · induction n with
    | zero => exact i.elim0
    | succ n ih =>
      rw [List.ofFn_succ, List.prod_cons]
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [List.prod_eq_one, (Fin.succ_ne_zero _).symm]
      · simp only [Fin.succ_ne_zero, if_false, _root_.one_mul, Fin.succ_inj]
        exact ih (v := fun j => v j.succ) (fun j => hv _) i

open Classical in

def scaleOn (Z : Set (Xo.XF c)) (a : c.F) (φ : FrameFn Xo c) : FrameFn Xo c :=
  fun F _ y v w => (if Set.range y ⊆ Z then baseOf y a else 1) * φ F y v w

theorem range_spMap_comp {F F' : Type} [Field F] [Field F'] (f : F →+* F') (y : Sp F ⟶ Xo.XF c) :
    Set.range (spMap f ≫ y) = Set.range y := by
  have : Function.Surjective (spMap f) := fun z => ⟨default, Subsingleton.elim _ _⟩
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, this.range_eq, Set.image_univ]

theorem isLineFn_scaleOn (Z : Set (Xo.XF c)) (ha : a ≠ 0) (h : IsLineFn U τ φ) : IsLineFn U τ (scaleOn Z a φ) where
  ne F _ β y v w hf := by
    refine mul_ne_zero ?_ (h.ne F β y v w hf)
    split_ifs
    exacts [(map_ne_zero _).2 ha, one_ne_zero]
  chg F _ β y v w v' w' A B h1 h2 h3 h4 := by
    simp only [scaleOn, _root_.mul_assoc, h.chg F β y v w v' w' A B h1 h2 h3 h4]
  nat F F' _ _ f β y v w y' v' w' h1 h2 h3 h4 := by
    have hb : baseOf y' = f.comp β := baseOf_eq (by
      rw [h2, Category.assoc, h1.1, ← Spec.map_comp]; rfl)
    have hr : Set.range y' = Set.range y := by rw [h2, range_spMap_comp]
    simp only [scaleOn, h.nat F F' f β y v w y' v' w' h1 h2 h3 h4, hb, baseOf_eq h1.1, map_mul,
      RingHom.comp_apply]
    split_ifs with p q q
    · rfl
    · exact absurd (hr ▸ p) q
    · exact absurd (hr ▸ q) p
    · simp

theorem isFlatGen_scaleOn {g : ℕ} {ty : Fin g → (E →+* ℂ)} {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty}
    {i : Fin FU.n} (Z : Set (Xo.XF c)) (ha : a ≠ 0) (h : IsFlatGen U τ φ FU i)
    (hZ : ∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P →
      y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → ¬ Set.range y ⊆ Z) :
    IsFlatGen U τ (scaleOn Z a φ) FU i where
  mem := h.mem
  line := isLineFn_scaleOn Z ha h.line
  flat := by
    obtain ⟨e, ρ, he, hc⟩ := h.flat
    refine ⟨e, ρ, he, fun P y v w V W C Fm B h1 h2 h3 h4 h5 h6 h7 h8 => ?_⟩
    rw [← hc P y v w V W C Fm B h1 h2 h3 h4 h5 h6 h7 h8]
    simp only [scaleOn, if_neg (hZ P y h1 h2 h3.1), _root_.one_mul]

end GlobalTheory.CompanionTheory.Ar.Fl.FlatModel
