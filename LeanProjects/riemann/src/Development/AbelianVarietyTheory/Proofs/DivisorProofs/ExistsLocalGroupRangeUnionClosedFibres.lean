import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSmoothGroupOverNbhdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMemRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpLawAndUnitAgreeOfOpenInDescentModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitMemIdentityComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianIdentityComponent
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OverExtOfPoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.UnionLocal

theorem awayMap_notMem {R : Type} [CommRing R] (g : R) (w : Sp (Localization.Away g)) : g ∉ (awayMap g w).asIdeal := by
  intro h
  have : algebraMap R (Localization.Away g) g ∈ w.asIdeal := h
  exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ this (IsLocalization.Away.algebraMap_isUnit g))

theorem mul_left_comp {S T T' : Scheme.{0}} {H : Over S} [GrpObj H] {t : T ⟶ S} {t' : T' ⟶ S} (k : T' ⟶ T)
    (a b : Over.mk t ⟶ H) (a₁ b₁ : Over.mk t' ⟶ H) (ha : a₁.left = k ≫ a.left) (hb : b₁.left = k ≫ b.left) :
    (a₁ * b₁).left = k ≫ (a * b).left := by
  have ht : k ≫ t = t' := by
    have e1 : a.left ≫ H.hom = t := Over.w a
    have e2 : a₁.left ≫ H.hom = t' := Over.w a₁
    rw [← e1, ← e2, ha]; exact (Category.assoc _ _ _).symm
  let κ : Over.mk t' ⟶ Over.mk t := Over.homMk k ht
  have e1 : a₁ = κ ≫ a := Over.OverMorphism.ext ha
  have e2 : b₁ = κ ≫ b := Over.OverMorphism.ext hb
  rw [e1, e2, ← MonObj.comp_mul]
  rfl

theorem mulAgree_pullback {S S' S₂ P : Scheme.{0}} {H : Over S} [GrpObj H] {H' : Over S'} [GrpObj H'] {A : Over S₂} [GrpObj A]
    {t : S' ⟶ S} {π : H'.left ⟶ H.left} (hπ : IsGrpPullback H' H t π) {h : H.left ⟶ P} {i : A.left ⟶ P}
    (hm : MulAgree H A h i) : MulAgree H' A (π ≫ h) i := by
  intro T t₁ t₂ a b a' b' ha hb
  have w : ∀ c : Over.mk t₁ ⟶ H', (c.left ≫ π) ≫ H.hom = t₁ ≫ t := fun c => by
    have e : c.left ≫ H'.hom = t₁ := Over.w c
    rw [Category.assoc, hπ.1.w, ← Category.assoc, e]
  let a₀ : Over.mk (t₁ ≫ t) ⟶ H := Over.homMk (a.left ≫ π) (w a)
  let b₀ : Over.mk (t₁ ≫ t) ⟶ H := Over.homMk (b.left ≫ π) (w b)
  have e := hπ.2 (Over.mk t₁) a b a₀ b₀ rfl rfl
  have e2 := hm T (t₁ ≫ t) t₂ a₀ b₀ a' b' ((Category.assoc _ _ _).trans ha) ((Category.assoc _ _ _).trans hb)
  rw [← e2, ← Category.assoc]
  exact congrArg (· ≫ h) e.symm

theorem openIn_pullback {P S₀ S S' Y : Scheme.{0}} (p : P ⟶ S₀) (u : S ⟶ S₀) [Mono u] (q : Y ⟶ S) (h : Y ⟶ P)
    [IsOpenImmersion h] (w : h ≫ p = q ≫ u) (t : S' ⟶ S) :
    OpenIn (pullback.fst q t ≫ h) (pullback.snd q t) p (t ≫ u) := by
  have w' : (pullback.fst q t ≫ h) ≫ p = pullback.snd q t ≫ t ≫ u := by
    rw [Category.assoc, w, pullback.condition_assoc]
  refine ⟨w', ?_⟩
  have hsq : CommSq (pullback.fst q t) (pullback.lift _ _ w') h (pullback.fst p (t ≫ u)) := ⟨by rw [pullback.lift_fst]⟩
  have hc : ∀ c : PullbackCone h (pullback.fst p (t ≫ u)), c.fst ≫ q = (c.snd ≫ pullback.snd p (t ≫ u)) ≫ t := fun c => by
    rw [← cancel_mono u, Category.assoc, ← w, ← Category.assoc, c.condition, Category.assoc, pullback.condition]
    simp only [Category.assoc]
  have hp : IsPullback (pullback.fst q t) (pullback.lift _ _ w') h (pullback.fst p (t ≫ u)) := by
    refine IsPullback.of_isLimit' hsq (PullbackCone.IsLimit.mk hsq.w (fun c => pullback.lift c.fst _ (hc c))
      (fun c => pullback.lift_fst _ _ _) (fun c => ?_) (fun c m hm1 hm2 => ?_))
    · apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, c.condition]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
    · apply pullback.hom_ext
      · rw [pullback.lift_fst, hm1]
      · rw [pullback.lift_snd, ← hm2, Category.assoc, pullback.lift_snd]
  exact MorphismProperty.of_isPullback hp ‹_›

theorem exists_point {P S₀ S : Scheme.{0}} (p : P ⟶ S₀) (s : S ⟶ S₀) (H₁ H₂ : Over S) [GrpObj H₁] [GrpObj H₂]
    (h₁ : H₁.left ⟶ P) (h₂ : H₂.left ⟶ P) (o₁ : OpenIn h₁ H₁.hom p s) (o₂ : OpenIn h₂ H₂.hom p s)
    (hs : Smooth H₁.hom) (hc : GeometricallyConnected H₁.hom) (hm : MulAgree H₁ H₂ h₁ h₂) (ho : OneAgree s s H₁ H₂ h₁ h₂)
    (y : H₁.left) : ∃ y' : H₂.left, h₂ y' = h₁ y ∧ H₂.hom y' = H₁.hom y := by
  obtain ⟨w₁, o₁⟩ := o₁
  obtain ⟨w₂, o₂⟩ := o₂
  have key : ∀ {T : Scheme.{0}} {t₁ t₂ : T ⟶ S} (a : Over.mk t₁ ⟶ H₁) (a' : Over.mk t₂ ⟶ H₂),
      a.left ≫ pullback.lift h₁ H₁.hom w₁ = a'.left ≫ pullback.lift h₂ H₂.hom w₂ ↔ a.left ≫ h₁ = a'.left ≫ h₂ ∧ t₁ = t₂ := by
    intro T t₁ t₂ a a'
    have e1 : a.left ≫ H₁.hom = t₁ := Over.w a
    have e2 : a'.left ≫ H₂.hom = t₂ := Over.w a'
    constructor
    · intro h
      have f1 := congrArg (· ≫ pullback.fst p s) h
      have f2 := congrArg (· ≫ pullback.snd p s) h
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd] at f1 f2
      exact ⟨f1, e1.symm.trans (f2.trans e2)⟩
    · rintro ⟨h, h'⟩
      apply pullback.hom_ext
      · simpa only [Category.assoc, pullback.lift_fst] using h
      · simp only [Category.assoc, pullback.lift_snd]
        exact e1.trans (h'.trans e2.symm)
  obtain ⟨y', hy'⟩ := GlobalTheory.OpenSubgrp.range_subset S (pullback p s) H₁ H₂ (pullback.lift h₁ H₁.hom w₁) (pullback.lift h₂ H₂.hom w₂)
    (pullback.snd p s) (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) o₁ o₂ hs hc
    (fun T t₁ t₂ a b a' b' ha hb => (key _ _).2 ⟨hm T t₁ t₂ a b a' b' ((key _ _).1 ha).1 ((key _ _).1 hb).1, ((key _ _).1 ha).2⟩)
    (fun T t₁ t₂ e => by
      have e' : t₁ = t₂ := by simpa using e
      exact (key _ _).2 ⟨ho T t₁ t₂ (by rw [e']), e'⟩) ⟨y, rfl⟩
  refine ⟨y', ?_, ?_⟩
  · have := congrArg (pullback.fst p s) hy'
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst, pullback.lift_fst] at this
  · have := congrArg (pullback.snd p s) hy'
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_snd, pullback.lift_snd] at this

theorem exists_connected (σ : Setup) (E : Emb σ) (g : σ.R) (H' : Over (Sp (Localization.Away g))) [GrpObj H']
    (h' : H'.left ⟶ E.P) (hl : E.LocGrp g H' h') :
    ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ E.P), E.LocGrp g H h ∧ GeometricallyConnected H.hom := by
  obtain ⟨hsm, hqc, hop, hp, hm⟩ := hl
  obtain ⟨H, _, j, hj, hjo, hr⟩ := GlobalTheory.identityComponentOpen _ H' hsm
  have hw : j.left ≫ H'.hom = H.hom := Over.w j
  have hsm₀ : Smooth H.hom := by rw [← hw]; infer_instance
  have : IsNoetherianRing (Localization.Away g) := IsLocalization.isNoetherianRing (Submonoid.powers g) _ inferInstance
  have : IsLocallyNoetherian H'.left := LocallyOfFiniteType.isLocallyNoetherian H'.hom
  have : CompactSpace H'.left := QuasiCompact.compactSpace_of_compactSpace H'.hom
  have : IsNoetherian H'.left := {}
  have hqc₀ : QuasiCompact H.hom := by rw [← hw]; infer_instance
  refine ⟨H, inferInstance, j.left ≫ h', ⟨hsm₀, hqc₀, inferInstance, by rw [Category.assoc, hp, ← Category.assoc, hw], ?_⟩,
    GlobalTheory.SS.NeutralPart.geometricallyConnected_of_section H.hom (η[H]).left (Over.w _)
      (GlobalTheory.SemiStableId.isConnected_fibre j hr)⟩
  intro T t₁ t₂ a b a' b' ha hb
  rw [← hm T t₁ t₂ (a ≫ j) (b ≫ j) a' b' ((Category.assoc _ _ _).trans ha) ((Category.assoc _ _ _).trans hb),
    ← MonObj.mul_comp, Over.comp_left, Category.assoc]

theorem lift_open (σ : Setup) (x : Sp σ.R) {T : Scheme.{0}} (c : T ⟶ (σ.C x).G.left) (d : T ⟶ Sp (Localization.Away σ.f))
    (e : c ≫ (σ.C x).G.hom ≫ spMap (σ.ρ x) = d ≫ awayMap σ.f) : ∃ l : T ⟶ (σ.V x).toScheme, l ≫ (σ.V x).ι = c := by
  refine ⟨IsOpenImmersion.lift (σ.V x).ι c ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨τ, rfl⟩
  rw [Scheme.Opens.range_ι]
  refine (σ.hV x _).2 ?_
  have h1 := awayMap_notMem σ.f (d τ)
  rw [← Scheme.Hom.comp_apply, ← e] at h1
  exact h1

theorem chart_mul_generic (σ : Setup) (E : Emb σ) (x : Sp σ.R) {T : Scheme.{0}} (s : T ⟶ Sp (FractionRing (σ.C x).R))
    (t₂ : T ⟶ Sp (Localization.Away σ.f)) (a b : Over.mk (s ≫ jK (σ.C x).R) ⟶ (σ.C x).G) (a' b' : Over.mk t₂ ⟶ σ.A)
    (ha : a.left ≫ E.emb x = a'.left ≫ E.ιA) (hb : b.left ≫ E.emb x = b'.left ≫ E.ιA) :
    (a * b).left ≫ E.emb x = (a' * b').left ≫ E.ιA := by
  have : IsOpenImmersion E.ιA := MorphismProperty.of_isPullback E.cartA.flip inferInstance
  obtain ⟨l, hl⟩ := lift_open σ x (pullback.fst (σ.C x).G.hom (jK (σ.C x).R)) (pullback.snd _ _ ≫ (σ.C x).y) (by
    rw [pullback.condition_assoc, Category.assoc, (σ.C x).hy, σ.hρ])
  have hα : (σ.C x).α ≫ E.ιA = pullback.fst (σ.C x).G.hom (jK (σ.C x).R) ≫ E.emb x := by
    have := σ.compat x _ (𝟙 _) l (by rw [Category.id_comp, hl])
    rw [Category.id_comp] at this
    rw [this, Category.assoc, E.onV, ← Category.assoc, hl]
  let P : (Over.mk (s ≫ jK (σ.C x).R) ⟶ (σ.C x).G) → (Over.mk s ⟶ (Over.pullback (jK (σ.C x).R)).obj (σ.C x).G) :=
    fun c => Over.homMk (pullback.lift c.left s (Over.w c)) (pullback.lift_snd _ _ _)
  have hP : ∀ c, c.left = (P c).left ≫ pullback.fst (σ.C x).G.hom (jK (σ.C x).R) := fun c => (pullback.lift_fst _ _ _).symm
  have hA : ∀ c (c' : Over.mk t₂ ⟶ σ.A), c.left ≫ E.emb x = c'.left ≫ E.ιA → c'.left = (P c).left ≫ (σ.C x).α := by
    intro c c' h
    rw [← cancel_mono E.ιA, ← h, hP c]
    exact (Category.assoc _ _ _).trans ((congrArg ((P c).left ≫ ·) hα.symm).trans (Category.assoc _ _ _).symm)
  have ht : t₂ = s ≫ (σ.C x).y := by
    have e1 : a'.left ≫ σ.A.hom = t₂ := Over.w a'
    have e2 : (P a).left ≫ ((Over.pullback (jK (σ.C x).R)).obj (σ.C x).G).hom = s := Over.w (P a)
    have e3 := (σ.C x).gen.1.w
    rw [← e1, hA a a' ha]
    exact (Category.assoc _ _ _).trans ((congrArg ((P a).left ≫ ·) e3).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (σ.C x).y) e2)))
  subst ht
  have m1 := (σ.C x).gen.2 (Over.mk s) (P a) (P b) a' b' (hA a a' ha) (hA b b' hb)
  have m2 := (isGrpPullback_pullback (σ.C x).G (jK (σ.C x).R)).2 (Over.mk s) (P a) (P b) a b (hP a) (hP b)
  exact (congrArg (· ≫ E.emb x) m2).trans ((Category.assoc _ _ _).trans ((congrArg ((P a * P b).left ≫ ·) hα.symm).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ E.ιA) m1.symm))))

theorem chart_mul_flat (σ : Setup) (E : Emb σ) (x : Sp σ.R) {T : Scheme.{0}} (t₁ : T ⟶ Sp (σ.C x).R) [Flat t₁]
    (t₂ : T ⟶ Sp (Localization.Away σ.f)) (a b : Over.mk t₁ ⟶ (σ.C x).G) (a' b' : Over.mk t₂ ⟶ σ.A)
    (ha : a.left ≫ E.emb x = a'.left ≫ E.ιA) (hb : b.left ≫ E.emb x = b'.left ≫ E.ιA) :
    (a * b).left ≫ E.emb x = (a' * b').left ≫ E.ιA := by
  have := E.sep
  obtain ⟨w, -⟩ := E.openIn x
  have p1 : ∀ c : Over.mk t₁ ⟶ (σ.C x).G, (c.left ≫ E.emb x) ≫ E.p = t₁ ≫ spMap (σ.ρ x) := fun c => by
    have e : c.left ≫ (σ.C x).G.hom = t₁ := Over.w c
    rw [Category.assoc, w, ← Category.assoc, e]
  have p2 : ∀ c : Over.mk t₂ ⟶ σ.A, (c.left ≫ E.ιA) ≫ E.p = t₂ ≫ awayMap σ.f := fun c => by
    have e : c.left ≫ σ.A.hom = t₂ := Over.w c
    rw [Category.assoc, E.cartA.w, ← Category.assoc, e]
  have : IsSchemeTheoreticallyDominant (jK (σ.C x).R) :=
    schDom_spec_map _ (IsFractionRing.injective (σ.C x).R (FractionRing (σ.C x).R))
  have : IsSchemeTheoreticallyDominant (pullback.fst t₁ (jK (σ.C x).R)) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback t₁ (jK (σ.C x).R)).flip
  refine ext_of_schDom E.p (by rw [p1, p2, ← p1 a, ← p2 a', ha]) (pullback.fst t₁ (jK (σ.C x).R)) ?_
  let k := pullback.fst t₁ (jK (σ.C x).R)
  let Q : (Over.mk t₁ ⟶ (σ.C x).G) → (Over.mk (pullback.snd t₁ (jK (σ.C x).R) ≫ jK (σ.C x).R) ⟶ (σ.C x).G) := fun c =>
    Over.homMk (k ≫ c.left) ((Category.assoc _ _ _).trans ((congrArg (k ≫ ·) (Over.w c)).trans pullback.condition))
  let Q' : (Over.mk t₂ ⟶ σ.A) → (Over.mk (k ≫ t₂) ⟶ σ.A) := fun c =>
    Over.homMk (k ≫ c.left) ((Category.assoc _ _ _).trans (congrArg (k ≫ ·) (Over.w c)))
  have h := chart_mul_generic σ E x _ _ (Q a) (Q b) (Q' a') (Q' b')
    ((Category.assoc _ _ _).trans ((congrArg (k ≫ ·) ha).trans (Category.assoc _ _ _).symm))
    ((Category.assoc _ _ _).trans ((congrArg (k ≫ ·) hb).trans (Category.assoc _ _ _).symm))
  rw [mul_left_comp k a b (Q a) (Q b) rfl rfl, mul_left_comp k a' b' (Q' a') (Q' b') rfl rfl] at h
  exact (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))

theorem chart_mulAgree (σ : Setup) (E : Emb σ) (x : Sp σ.R) : MulAgree (σ.C x).G σ.A (E.emb x) E.ιA := by
  intro T t₁ t₂ a b a' b' ha hb
  have : IsOpenImmersion E.ιA := MorphismProperty.of_isPullback E.cartA.flip inferInstance
  have := (σ.C x).semi.smooth
  obtain ⟨w, -⟩ := E.openIn x
  have hl : ∀ (c : Over.mk t₁ ⟶ (σ.C x).G) (c' : Over.mk t₂ ⟶ σ.A), c.left ≫ E.emb x = c'.left ≫ E.ιA →
      ∃ l : T ⟶ (σ.V x).toScheme, l ≫ (σ.V x).ι = c.left ∧ l ≫ σ.φ x = c'.left := by
    intro c c' h
    obtain ⟨l, hl⟩ := lift_open σ x c.left (c'.left ≫ σ.A.hom) (by
      rw [← w, ← Category.assoc, h, Category.assoc, E.cartA.w, Category.assoc])
    refine ⟨l, hl, ?_⟩
    rw [← cancel_mono E.ιA, Category.assoc, E.onV, ← Category.assoc, hl]
    exact h
  obtain ⟨la, ha1, ha2⟩ := hl a a' ha
  obtain ⟨lb, hb1, hb2⟩ := hl b b' hb
  let q : (σ.V x).toScheme ⟶ Sp (σ.C x).R := (σ.V x).ι ≫ (σ.C x).G.hom
  have hq : la ≫ q = lb ≫ q := by
    have e1 : a.left ≫ (σ.C x).G.hom = t₁ := Over.w a
    have e2 : b.left ≫ (σ.C x).G.hom = t₁ := Over.w b
    simp only [q, ← Category.assoc, ha1, hb1]
    exact e1.trans e2.symm
  have hu : pullback.snd q q ≫ σ.φ x ≫ σ.A.hom = pullback.fst q q ≫ σ.φ x ≫ σ.A.hom := by
    rw [← cancel_mono (awayMap σ.f)]
    simp only [Category.assoc]
    rw [(σ.cart x).w]
    exact (pullback.condition_assoc (f := q) (g := q) _).symm
  let a₀ : Over.mk (pullback.fst q q ≫ q) ⟶ (σ.C x).G := Over.homMk (pullback.fst q q ≫ (σ.V x).ι) (Category.assoc _ _ _)
  let b₀ : Over.mk (pullback.fst q q ≫ q) ⟶ (σ.C x).G := Over.homMk (pullback.snd q q ≫ (σ.V x).ι)
    ((Category.assoc _ _ _).trans pullback.condition.symm)
  let a₁ : Over.mk (pullback.fst q q ≫ σ.φ x ≫ σ.A.hom) ⟶ σ.A := Over.homMk (pullback.fst q q ≫ σ.φ x) (Category.assoc _ _ _)
  let b₁ : Over.mk (pullback.fst q q ≫ σ.φ x ≫ σ.A.hom) ⟶ σ.A := Over.homMk (pullback.snd q q ≫ σ.φ x)
    ((Category.assoc _ _ _).trans hu)
  have h := chart_mul_flat σ E x (pullback.fst q q ≫ q) _ a₀ b₀ a₁ b₁
    ((Category.assoc _ _ _).trans ((congrArg (pullback.fst q q ≫ ·) (E.onV x).symm).trans (Category.assoc _ _ _).symm))
    ((Category.assoc _ _ _).trans ((congrArg (pullback.snd q q ≫ ·) (E.onV x).symm).trans (Category.assoc _ _ _).symm))
  let k := pullback.lift la lb hq
  have k1 : k ≫ pullback.fst q q = la := pullback.lift_fst _ _ _
  have k2 : k ≫ pullback.snd q q = lb := pullback.lift_snd _ _ _
  rw [mul_left_comp k a₀ b₀ a b (ha1.symm.trans (by rw [← k1]; exact Category.assoc _ _ _))
      (hb1.symm.trans (by rw [← k2]; exact Category.assoc _ _ _)),
    mul_left_comp k a₁ b₁ a' b' (ha2.symm.trans (by rw [← k1]; exact Category.assoc _ _ _))
      (hb2.symm.trans (by rw [← k2]; exact Category.assoc _ _ _))]
  exact (Category.assoc _ _ _).trans ((congrArg (k ≫ ·) h).trans (Category.assoc _ _ _).symm)

theorem mem_range_iff (σ : Setup) (E : Emb σ) (g : σ.R) (H : Over (Sp (Localization.Away g))) [GrpObj H] (h : H.left ⟶ E.P)
    (hl : E.LocGrp g H h) (hc : GeometricallyConnected H.hom) (x : Sp σ.R) (hx : g ∉ x.asIdeal) (z : E.P) (hz : E.p z = x) :
    z ∈ Set.range h ↔ ∃ y : (σ.C x).G.left, (σ.C x).G.hom y = closedPoint _ ∧ E.emb x y = z := by
  obtain ⟨hsm, -, hop, hp, hm⟩ := hl
  have hcen : spMap (σ.ρ x) (closedPoint (σ.C x).R) = x := by rw [← σ.hρ]; exact (σ.C x).centre
  have hu : IsUnit (σ.ρ x g) := by
    by_contra hn
    apply hx
    have : g ∈ (spMap (σ.ρ x) (closedPoint (σ.C x).R)).asIdeal := hn
    rwa [hcen] at this
  let t : Sp (σ.C x).R ⟶ Sp (Localization.Away g) := spMap (IsLocalization.Away.lift g hu)
  have ht : t ≫ awayMap g = spMap (σ.ρ x) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsLocalization.Away.lift_comp]
  have o₂ : OpenIn (pullback.fst H.hom t ≫ h) ((Over.pullback t).obj H).hom E.p (spMap (σ.ρ x)) :=
    ht ▸ openIn_pullback E.p (awayMap g) H.hom h hp t
  have s₂ : Smooth ((Over.pullback t).obj H).hom := inferInstanceAs (Smooth (pullback.snd H.hom t))
  have c₂ : GeometricallyConnected ((Over.pullback t).obj H).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd H.hom t))
  have s₁ := (σ.C x).semi.smooth
  have fl : Flat (spMap (σ.ρ x)) := Flat.SpecMap_iff.2 (σ.flat x)
  have m₁ := chart_mulAgree σ E x
  have m₂ := mulAgree_pullback (isGrpPullback_pullback H t) hm
  constructor
  · rintro ⟨v, rfl⟩
    have e : H.hom v = t (closedPoint (σ.C x).R) := by
      apply (awayMap g).isOpenEmbedding.injective
      have e1 : (H.hom ≫ awayMap g) v = x := by rw [← hp]; exact hz
      have e2 : (t ≫ awayMap g) (closedPoint (σ.C x).R) = x := by rw [ht]; exact hcen
      exact e1.trans e2.symm
    obtain ⟨v₂, hv1, hv2⟩ := Scheme.Pullback.exists_preimage_pullback (f := H.hom) (g := t) v _ e
    obtain ⟨ma, oa⟩ := GlobalTheory.T.grpLaw_and_unit_agree_of_openIn_descentModel σ E _ _ _ _ ((Over.pullback t).obj H) (σ.C x).G _ _ fl fl inferInstance inferInstance
      o₂ (E.openIn x) m₂ m₁
    obtain ⟨y, hy1, hy2⟩ := exists_point E.p _ ((Over.pullback t).obj H) (σ.C x).G _ _ o₂ (E.openIn x) s₂ c₂ ma oa v₂
    exact ⟨y, hy2.trans hv2, hy1.trans (congrArg h hv1)⟩
  · rintro ⟨y, -, rfl⟩
    obtain ⟨ma, oa⟩ := GlobalTheory.T.grpLaw_and_unit_agree_of_openIn_descentModel σ E _ _ _ _ (σ.C x).G ((Over.pullback t).obj H) _ _ fl fl inferInstance inferInstance
      (E.openIn x) o₂ m₁ m₂
    obtain ⟨v, hv, -⟩ := exists_point E.p _ (σ.C x).G ((Over.pullback t).obj H) _ _ (E.openIn x) o₂ s₁
      (σ.C x).semi.geomConnected ma oa y
    exact ⟨pullback.fst H.hom t v, hv⟩

theorem exists_locGrp_range_eq : ∀ (σ : Setup) (E : Emb σ), σ.Common → ∀ x : Sp σ.R, ∃ g : σ.R, g ∉ x.asIdeal ∧ ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ E.P), E.LocGrp g H h ∧ Set.range h = E.U ∩ E.p ⁻¹' {z : Sp σ.R | g ∉ z.asIdeal} := by
  intro σ E hC x
  obtain ⟨g, hg, H', _, h', hl', -⟩ := GlobalTheory.T.exists_local_smooth_group_over_nbhd σ E hC x
  obtain ⟨H, _, h, hl, hgc⟩ := exists_connected σ E g H' h' hl'
  refine ⟨g, hg, H, inferInstance, h, hl, ?_⟩
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    have hpz : g ∉ (E.p (h v)).asIdeal := by
      rw [← Scheme.Hom.comp_apply, hl.2.2.2.1, Scheme.Hom.comp_apply]
      exact awayMap_notMem g _
    obtain ⟨y, hy, hyz⟩ := (mem_range_iff σ E g H h hl hgc _ hpz _ rfl).1 ⟨v, rfl⟩
    exact ⟨⟨_, y, hy, hyz⟩, hpz⟩
  · rintro ⟨⟨x₀, y, hy, rfl⟩, hz⟩
    have hx₀ : E.p (E.emb x₀ y) = x₀ := by
      obtain ⟨w, -⟩ := E.openIn x₀
      rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply, hy, ← σ.hρ x₀]
      exact (σ.C x₀).centre
    have hz' : g ∉ x₀.asIdeal := by rw [← hx₀]; exact hz
    exact (mem_range_iff σ E g H _ hl hgc x₀ hz' _ hx₀).2 ⟨y, hy, rfl⟩

end GlobalTheory.Desc.UnionLocal
