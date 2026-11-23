import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatTorsionIsomorphism
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFiniteFlatTorsionOfIsGt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionFormCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.TorusModel GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.KernelNoTorsion IsLocalRing
open scoped CategoryTheory.Obj

section Points

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {Gt : Over (Sp R)} [GrpObj Gt]
  {Φ : ∀ T, (T ⟶ Gt) ≃ GtPt D T}

theorem isZero_unique {T : Over (Sp R)} {g g' : GtPt D T} (h : g.IsZero) (h' : g'.IsZero) : g = g' :=
  pt_ext (h.1.trans h'.1.symm) fun χ _ _ hJ =>
    (val_corr hJ (h.2 χ) (𝟙 _)).trans (val_corr hJ (h'.2 χ) (𝟙 _)).symm

theorem isZero_of_isAdd {T : Over (Sp R)} {g : GtPt D T} (h : g.IsAdd g g) : g.IsZero := by
  obtain ⟨hb, hv⟩ := (TorusModel.isAdd_iff _ _ _).1 h
  have hb1 : g.b = 1 := mul_eq_left.1 hb.symm
  refine ⟨hb1, fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  have C : IsCub (th D (T := T) y J) := isCub_cubV D.cub hJ
  have e' : th D y J (cP D T χ) g.b g.b = 1 := by
    rw [hb1, C.face₃]
  have e := hv χ y J hJ
  rw [e', _root_.mul_one] at e
  have e₂ : cv g χ y J = 1 := mul_eq_left.1 e.symm
  exact e₂.trans (val_one _).symm

theorem isZero_one (hΦ : Represents Φ) (T : Over (Sp R)) : (Φ T 1).IsZero := by
  have h := hΦ.2 T 1 1
  rw [_root_.mul_one] at h
  exact isZero_of_isAdd h

theorem tors_iff (hΦ : Represents Φ) (k : ℕ) {T : Over (Sp R)} (x : T ⟶ Gt) :
    FlatIsoUnitGenerator.GtTors k (Φ T x) ↔ x ^ k = 1 := by
  constructor
  · rintro ⟨_, ⟨u, u0, us, rfl⟩, hz⟩
    have : ∀ i : Fin (k + 1), u i = Φ T (x ^ (i : ℕ)) := fun i => by
      induction i using Fin.induction with
      | zero => exact isZero_unique u0 (by simpa using isZero_one hΦ T)
      | succ i ih =>
        have h := us i
        rw [ih] at h
        rw [Fin.val_succ, pow_succ]
        exact isAdd_unique h (hΦ.2 T _ _)
    exact (Φ T).injective ((this (Fin.last k)).symm.trans (isZero_unique hz (isZero_one hΦ T)))
  · intro hx
    refine ⟨Φ T (x ^ k), ⟨fun i => Φ T (x ^ (i : ℕ)), by simpa using isZero_one hΦ T, fun i => ?_, rfl⟩,
      hx ▸ isZero_one hΦ T⟩
    simp only [Fin.val_succ, Fin.val_castSucc, pow_succ]
    exact hΦ.2 T _ _

theorem isPull_iff_comp (hΦ : Represents Φ) {T T' : Over (Sp R)} (h : T' ⟶ T) (x : T ⟶ Gt) (x' : T' ⟶ Gt) :
    GtPt.IsPull h.left (Φ T x) (Φ T' x') ↔ h ≫ x = x' :=
  ⟨fun H => (Φ T').injective (isPull_unique (hΦ.1 _ _ h x) H), fun H => H ▸ hΦ.1 _ _ h x⟩

theorem isSmulPt_unique (hG : GlobalFnsSt) {O : Type} [CommRing O] [StarRing O] [Module O D.X] {oa : D.OAct O} {a : O}
    {T : Over (Sp R)} {g g' g'' : GtPt D T} (h : IsSmulPt oa a g g') (h' : IsSmulPt oa a g g'') : g' = g'' := by
  obtain ⟨b, v⟩ := (isSmulPt_iff hG oa _ _ _).1 h
  obtain ⟨b', v'⟩ := (isSmulPt_iff hG oa _ _ _).1 h'
  exact pt_ext (b.trans b'.symm) fun χ y J hJ => (v χ y J hJ).trans (v' χ y J hJ).symm

theorem exists_represents [IsNoetherianRing R] (D : DegPre R) :
    ∃ (Gt : Over (Sp R)) (_ : GrpObj Gt) (_ : IsCommMonObj Gt) (Φ : ∀ T, (T ⟶ Gt) ≃ GtPt D T), Represents Φ ∧
      ∀ k : ℕ, 1 ≤ k → IsFinite (torsion Gt k).hom ∧ Flat (torsion Gt k).hom := by
  have hL := abelianSchemeLaws_all.1
  obtain ⟨H, _, _, hH⟩ := exists_isGt hL.globalFns (splitExt D)
  obtain ⟨Φ, hΦ⟩ := exists_points hL.globalFns hH
  refine ⟨H, inferInstance, inferInstance, Φ, hΦ, fun k hk => ?_⟩
  obtain ⟨h₁, h₂, -⟩ := hL.mulN _ D.P k hk
  have h₁' : IsFinite (𝟙 D.P.A ^ k).left := h₁
  have h₂' : Flat (𝟙 D.P.A ^ k).left := h₂
  rw [← MulEtaleDvr.mulN_eq_pow] at h₁' h₂'
  have P := MulEtaleDvr.isPullback_torsion D.P.A k
  exact isFinite_flat_torsion_of_isGt _ (splitExt D) H hH k hk (MorphismProperty.of_isPullback (P := @IsFinite) P h₁')
    (MorphismProperty.of_isPullback (P := @Flat) P h₂')

end Points

theorem isAdicColimit_of_isFinite {R : Type} [CommRing R] [IsLocalRing R] (hc : IsAdicComplete (maximalIdeal R) R)
    (N : Over (Sp R)) [IsFinite N.hom] [Flat N.hom] : IsAdicColimit (maximalIdeal R) N := by
  have : IsAffine N.left := isAffine_of_isAffineHom N.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (N.left.isoSpec.inv ≫ N.hom)
  have hf : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  have hl : Flat (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at hf
  rw [HasRingHomProperty.Spec_iff (P := @Flat)] at hl
  letI : Algebra R Γ(N.left, ⊤) := φ.hom.toAlgebra
  have : Module.Finite R Γ(N.left, ⊤) := hf
  have : Module.Flat R Γ(N.left, ⊤) := hl
  have H := isAdicColimit_of_finite_flat (maximalIdeal R) (RingHom.id R) (by rwa [Ideal.map_id])
    (fun a ha => ⟨1, by rwa [Ideal.map_id, pow_one]⟩) Γ(N.left, ⊤)
  exact IsAdicColimit.of_iso (Over.isoMk N.left.isoSpec.symm hφ.symm) H

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)}

theorem formalEq_iff {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) {T : Over (Sp R)} (x : T ⟶ G) (g : GtPt D.toPre T) :
    FlatIsoUnitGenerator.FormalEq U x g ↔ IsPointOf U g x := by
  rw [isPointOf_iff_thick]
  refine forall_congr' fun e => and_congr eq_comm (forall_congr' fun χ => ⟨fun h => ?_, fun h => ?_⟩) <;>
  exact corr_of_val D.toPre.P.isLB fun _ _ hJ => (val_corr hJ h (𝟙 _)).symm

theorem coordOf_iff {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) {e : ℕ} {T : Over (Sp (R ⧸ I ^ (e + 1)))} (x : T ⟶ thickObj R I e G)
    (g : GtPt D.toPre ((Over.map (thick R I e)).obj T)) :
    FlatTorsionIsomorphism.CoordOf (U.gt e) x g ↔ HasCoords U e g (𝟙 _) x.left := by
  rw [hasCoords_iff]
  refine and_congr ⟨fun h => (congrArg (·.left) h).symm.trans (Category.id_comp _).symm,
    fun h => Over.OverMorphism.ext (h.trans (Category.id_comp _)).symm⟩
    (forall_congr' fun χ => ⟨fun h z J hJ => ?_, fun h => corr_of_val D.toPre.P.isLB fun z J hJ => ?_⟩)
  · have := (val_corr hJ h (𝟙 _)).trans (val_pull hJ _ _ _)
    rw [Category.id_comp] at this
    exact this.symm
  · refine (h z J hJ).symm.trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    rw [Category.id_comp]

theorem isFinitePart_of_finitePart [IsNoetherianRing R] (P : PELUnif I t) {k : ℕ} (hk : 1 ≤ k)
    (φ : FlatTorsionIsomorphism.FinitePart P k) :
    ∃ (N : Over (Sp R)) (g₀ : GtPt P.D.toPre N) (x₀ : N ⟶ t.G), FlatIsoUnitGenerator.IsFinitePart P.U.toUnifPre k N g₀ x₀ ∧
      ∀ (T : Over (Sp R)) (h : T ⟶ N) (g : FlatTorsionIsomorphism.GtTors P.D.toPre k T), GtPt.IsPull h.left g₀ g.g →
        φ.h T g = h ≫ x₀ := by
  obtain ⟨Gt, _, _, Φ, hΦ, hfin⟩ := exists_represents P.D.toPre
  let τ : ∀ {T} (h : T ⟶ torsion Gt k), FlatTorsionIsomorphism.GtTors P.D.toPre k T := fun {T} h =>
    ⟨Φ T (h ≫ torsion.ι Gt k), (tors_iff hΦ k _).2 (by rw [← MonObj.comp_pow, torsionι_pow, MonObj.comp_one])⟩
  let c₀ : FlatTorsionIsomorphism.GtTors P.D.toPre k (torsion Gt k) := ⟨Φ _ (torsion.ι Gt k), (tors_iff hΦ k _).2 (torsionι_pow Gt k)⟩
  have hτ : ∀ {T} (h : T ⟶ torsion Gt k), φ.h T (τ h) = h ≫ φ.h _ c₀ := fun h => φ.pull _ _ h c₀ (τ h) (hΦ.1 _ _ h _)
  refine ⟨torsion Gt k, c₀.g, φ.h _ c₀, ⟨(hfin k hk).1, (hfin k hk).2, c₀.tors, fun T g hg => ?_, φ.tors _ _,
    ⟨fun h h' e => ?_⟩, fun T hT x hx => ?_, (formalEq_iff _ _ _).2 ((isPointOf_iff_thick _ _ _).2 fun e => ?_)⟩,
    fun T h g hg => φ.pull _ _ h c₀ g hg⟩
  · obtain ⟨x, rfl⟩ := (Φ T).surjective g
    have hx := (tors_iff hΦ k x).1 hg
    refine ⟨torsionLift x hx, (isPull_iff_comp hΦ _ _ _).2 (torsionLift_ι _ _), fun h hh => torsion_hom_ext ?_⟩
    rw [torsionLift_ι]
    exact (isPull_iff_comp hΦ _ _ _).1 hh
  · rw [← hτ, ← hτ] at e
    exact torsion_hom_ext ((Φ _).injective (congrArg (·.g) (φ.inj _ e)))
  · obtain ⟨⟨g, hg⟩, rfl⟩ := φ.onto T hT x hx
    obtain ⟨y, rfl⟩ := (Φ T).surjective g
    exact ⟨torsionLift y ((tors_iff hΦ k y).1 hg),
      (φ.pull _ _ _ c₀ ⟨_, hg⟩ ((isPull_iff_comp hΦ _ _ _).2 (torsionLift_ι _ _))).symm⟩
  · obtain ⟨y, hy⟩ := exists_hasCoords P.U.toUnifPre e c₀.g (thickι I e (torsion Gt k))
      (thickObj R I e (torsion Gt k)).hom pullback.condition.symm
    have hy' : HasCoords P.U.toUnifPre e (τ (fstG I e (torsion Gt k))).g (𝟙 _) y :=
      (hasCoords_pull (k := fstG I e (torsion Gt k)) (hΦ.1 _ _ _ _)).1 (by rw [Category.id_comp]; exact hy)
    have hw : y ≫ (thickObj R I e t.G).hom = (thickObj R I e (torsion Gt k)).hom := by
      rw [← cancel_mono (thick R I e), Category.assoc]
      have h₁ := congrArg (· ≫ P.D.toPre.P.A.hom) hy.1
      simp only [Category.assoc, Over.w] at h₁
      exact h₁.trans pullback.condition
    have r := φ.red e (thickObj R I e (torsion Gt k)) (Over.homMk y hw) (τ (fstG I e _)) ((coordOf_iff _ _ _).2 hy')
    rw [hτ] at r
    have : thickHom I e (φ.h _ c₀) = y := by
      rw [← cancel_mono (thickι I e t.G), thickHom_ι]
      exact congrArg (·.left) r
    rw [this]
    exact hy

theorem finitePart_of_isFinitePart [IsNoetherianRing R] [IsLocalRing R] (hc : IsAdicComplete (maximalIdeal R) R)
    (P : PELUnif (maximalIdeal R) t) {k : ℕ} {N : Over (Sp R)} {g₀ : GtPt P.D.toPre N} {x₀ : N ⟶ t.G}
    (hN : FlatIsoUnitGenerator.IsFinitePart P.U.toUnifPre k N g₀ x₀) :
    ∃ φ : FlatTorsionIsomorphism.FinitePart P k, ∀ (T : Over (Sp R)) (g : FlatTorsionIsomorphism.GtTors P.D.toPre k T),
      ∃ h : T ⟶ N, GtPt.IsPull h.left g₀ g.g ∧ φ.h T g = h ≫ x₀ := by
  letI := H.starRing
  have hG := abelianSchemeLaws_all.1.globalFns
  obtain ⟨Gt, _, _, Φ, hΦ, -⟩ := exists_represents P.D.toPre
  obtain ⟨ρ, hρ⟩ := exists_ringAct hG P.oD hΦ
  obtain ⟨c₀, rfl⟩ := (Φ N).surjective g₀
  have hc₀ := (tors_iff hΦ k c₀).1 hN.gt_tors
  have hp := (formalEq_iff _ _ _).1 hN.formal
  have := hN.finite
  have := hN.flat
  have := hN.g_mono
  have univ : ∀ {T} (x : T ⟶ Gt), x ^ k = 1 → ∃! h : T ⟶ N, h ≫ c₀ = x := fun {T} x hx =>
    (existsUnique_congr fun h => isPull_iff_comp hΦ h c₀ x).1 (hN.gt_univ T _ ((tors_iff hΦ k x).2 hx))
  have tz : ∀ {T} (h : T ⟶ N), (h ≫ c₀) ^ k = 1 := fun h => by rw [← MonObj.comp_pow, hc₀, MonObj.comp_one]
  have canc : ∀ {T} {h h' : T ⟶ N}, h ≫ c₀ = h' ≫ c₀ → h = h' := fun {T h h'} e => (univ _ (tz h')).unique e rfl
  have pt : ∀ {T} (h : T ⟶ N), IsPointOf P.U.toUnifPre (Φ T (h ≫ c₀)) (h ≫ x₀) := fun h => hp.pull h (hΦ.1 _ _ h c₀)
  choose l hl using fun T (g : FlatTorsionIsomorphism.GtTors P.D.toPre k T) =>
    (univ ((Φ T).symm g.g) ((tors_iff hΦ k _).1 (by rw [Equiv.apply_symm_apply]; exact g.tors))).exists
  have hl' : ∀ T g, Φ T (l T g ≫ c₀) = g.g := fun T g => by rw [hl, Equiv.apply_symm_apply]
  have hNN : IsAdicColimit (maximalIdeal R) (N ⊗ N) := by
    have : IsFinite (N ⊗ N).hom := inferInstanceAs (IsFinite (pullback.fst N.hom N.hom ≫ N.hom))
    have : Flat (N ⊗ N).hom := inferInstanceAs (Flat (pullback.fst N.hom N.hom ≫ N.hom))
    exact isAdicColimit_of_isFinite hc _
  obtain ⟨m, hm, -⟩ := univ ((fst N N ≫ c₀) * (snd N N ≫ c₀)) (by rw [mul_pow, tz, tz, _root_.mul_one])
  have hm' : m ≫ x₀ = (fst N N ≫ x₀) * (snd N N ≫ x₀) :=
    (existsUnique_point _ hNN _).unique (pt m) (hm ▸ (pt _).mul hG (pt _) (hΦ.2 _ _ _))
  refine ⟨⟨fun T g => l T g ≫ x₀, fun T g => by rw [← MonObj.comp_pow, hN.g_tors, MonObj.comp_one],
    fun T T' f g g' h => ?_, fun T g g' g'' h => ?_, fun T a g g' h => ?_, fun T g g' h => ?_, fun T hT x hx => ?_,
    fun e T x g h => ?_⟩, fun T g => ⟨l T g, hl' T g ▸ hΦ.1 _ _ _ c₀, rfl⟩⟩
  · rw [← hl' T g, ← hl' T' g', isPull_iff_comp hΦ, ← Category.assoc] at h
    rw [← canc h, Category.assoc]
  · rw [← hl' T g, ← hl' T g', ← hl' T g''] at h
    have e := (Φ T).injective (isAdd_unique h (hΦ.2 T _ _))
    have : l T g'' = lift (l T g) (l T g') ≫ m := canc (by
      rw [e, Category.assoc, hm, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc])
    rw [this, Category.assoc, hm', MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
  · have := ρ.hom a
    obtain ⟨n, hn, -⟩ := univ (c₀ ≫ ρ.act a) (by rw [← MonObj.pow_comp, hc₀, MonObj.one_comp])
    have hn' : n ≫ x₀ = x₀ ≫ t.act.act a :=
      (existsUnique_point _ (isAdicColimit_of_isFinite hc N) _).unique (pt n) (hn ▸ hp.smul hG P.lin a (hρ a _ _))
    rw [← hl' T g, ← hl' T g'] at h
    have e := (Φ T).injective (isSmulPt_unique hG h (hρ a T _))
    have : l T g' = l T g ≫ n := canc (by rw [e, Category.assoc, Category.assoc, hn])
    rw [this, Category.assoc, hn', Category.assoc]
  · have e : g.g = g'.g := by rw [← hl' T g, ← hl' T g', (cancel_mono x₀).1 h]
    cases g; cases g'; cases e; rfl
  · obtain ⟨h, rfl⟩ := hN.g_univ T hT x hx
    refine ⟨⟨Φ T (h ≫ c₀), (tors_iff hΦ k _).2 (tz h)⟩, ?_⟩
    exact congrArg (· ≫ x₀) (canc ((Φ T).injective (hl' T _)))
  · have h₁ := (coordOf_iff _ _ _).1 h
    rw [← hl' _ g] at h₁
    exact Over.OverMorphism.ext (((pt _).comp_fstG_eq h₁).trans (Category.id_comp _)).symm

end GlobalTheory.TorsionFormCompare
