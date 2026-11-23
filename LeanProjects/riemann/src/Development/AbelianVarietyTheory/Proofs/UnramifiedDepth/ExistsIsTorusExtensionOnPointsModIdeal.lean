import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorExtPoints

variable {S S' : Scheme.{0}} {Ω : Type} [Field Ω]

theorem exists_lift {X Y : Scheme.{0}} (q : X ⟶ Y) [Smooth q] {A : Type} [CommRing A] [Algebra Ω A]
    (π : A →ₐ[Ω] Ω) (hn : IsNilpotent (RingHom.ker π)) (y : Sp A ⟶ Y) (x₀ : Sp Ω ⟶ X)
    (h : x₀ ≫ q = spMap (π : A →+* Ω) ≫ y) : ∃ x : Sp A ⟶ X, spMap (π : A →+* Ω) ≫ x = x₀ ∧ x ≫ q = y := by
  have hπ : Function.Surjective π := fun a => ⟨algebraMap Ω A a, π.commutes a⟩
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ := exists_isAffineOpen_pair q (x₀ (closedPoint Ω)) (O := ⊤) trivial
  refine exists_lift_of_smooth_of_isAffineOpen q hU hV hVU (CommRingCat.ofHom (π : A →+* Ω)) y x₀ h ?_
    (range_subset_opens_of_isLocalRing x₀ hxV) ?_
  · rintro _ ⟨p, rfl⟩
    obtain ⟨z, hz⟩ : p ∈ Set.range (PrimeSpectrum.comap (π : A →+* Ω)) := by
      refine (range_comap_of_surjective _ (π : A →+* Ω) hπ).ge ?_
      obtain ⟨n, hn⟩ := hn
      exact (Ideal.IsPrime.pow_le_iff (P := p.asIdeal) (hP := p.isPrime) n.succ_ne_zero).1 (by
        rw [pow_succ]
        exact Ideal.mul_le_left.trans (hn.le.trans bot_le))
    obtain rfl : z = closedPoint Ω := Subsingleton.elim _ _
    have e : q (x₀ (closedPoint Ω)) = y (spMap (π : A →+* Ω) (closedPoint Ω)) := congr($h (closedPoint Ω))
    rw [← hz]
    exact e ▸ hVU hxV
  · intro R C _ _ _ _ _ _ p hp φ
    have hs : Function.Surjective p := fun c => (hπ c).imp fun b hb => (hp b).trans hb
    have hk : IsNilpotent (RingHom.ker p.toRingHom) := by
      convert hn using 1
      exact Ideal.ext fun b => Eq.congr_left (hp b)
    exact ⟨Algebra.FormallySmooth.liftOfSurjective φ p hs hk,
      Algebra.FormallySmooth.comp_liftOfSurjective φ p hs hk⟩

def torPt (s : Sp Ω ⟶ S) (X : Type) [AddCommGroup X] (A : Type) [CommRing A] [Algebra Ω A] :
    (overAt s A ⟶ splitTorus S X) ≃* (Multiplicative X →* Aˣ) :=
  (splitTorusPointsEquiv S X (overAt s A)).trans
    (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.toMulEquiv).monoidHomCongrRight

theorem torPt_nat (s : Sp Ω ⟶ S) (X : Type) [AddCommGroup X] {A A' : Type} [CommRing A] [Algebra Ω A]
    [CommRing A'] [Algebra Ω A'] (f : A →ₐ[Ω] A') (t : overAt s A ⟶ splitTorus S X) :
    torPt s X A' (homAt s f ≫ t) = (Units.map (f : A →* A')).comp (torPt s X A t) := by
  ext x
  change (Scheme.ΓSpecIso (CommRingCat.of A')).hom.hom
      (splitTorusPointsEquiv S X _ (homAt s f ≫ t) (Multiplicative.ofAdd x)).val =
    f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
      (splitTorusPointsEquiv S X _ t (Multiplicative.ofAdd x)).val)
  rw [splitTorusPointsEquiv_val, splitTorusPointsEquiv_val, Over.comp_left, Scheme.Hom.comp_appTop]
  exact congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (f : A →+* A'))) _)

theorem isTorExt_of_kernel (s : Sp Ω ⟶ S) {G B : Over S} [GrpObj G] [GrpObj B] {X : Type} [AddCommGroup X]
    (i : splitTorus S X ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q] [Smooth q.left]
    (hk : IsPullback i (toUnit _) q η[B]) :
    IsTorExt s s G B X (fun A _ _ => IsMonHom.monoidHom q (overAt s A))
      (fun A _ _ => (IsMonHom.monoidHom i (overAt s A)).comp (torPt s X A).symm.toMonoidHom) := by
  refine ⟨fun A A' _ _ _ _ f x => Category.assoc _ x q, fun A A' _ _ _ _ f χ => ?_, fun A _ _ χ χ' h => ?_,
    fun A _ _ x => ⟨fun h => ?_, ?_⟩, fun A _ _ π hn y hy => ?_⟩
  · obtain ⟨t, rfl⟩ := (torPt s X A).surjective χ
    rw [← torPt_nat]
    change (torPt s X A').symm _ ≫ i = _ ≫ (torPt s X A).symm _ ≫ i
    rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, Category.assoc]
  · exact (torPt s X A).symm.injective (hk.hom_ext h (toUnit_unique _ _))
  · refine ⟨torPt s X A (hk.lift x (toUnit _) h), ?_⟩
    change (torPt s X A).symm _ ≫ i = _
    rw [MulEquiv.symm_apply_apply]
    exact hk.lift_fst _ _ _
  · rintro ⟨χ, rfl⟩
    change (_ ≫ i) ≫ q = toUnit _ ≫ η[B]
    rw [Category.assoc, hk.w, ← Category.assoc, toUnit_unique (_ ≫ _) (toUnit _)]
  · have h1 : (1 : overAt s Ω ⟶ G) ≫ q = homAt s π ≫ y := (map_one (IsMonHom.monoidHom q _)).trans hy.symm
    obtain ⟨x, hx, hq⟩ := exists_lift q.left π hn y.left (1 : overAt s Ω ⟶ G).left (congrArg (·.left) h1)
    exact ⟨Over.homMk x (by rw [← Over.w q, reassoc_of% hq]; exact Over.w y), Over.OverMorphism.ext hx,
      Over.OverMorphism.ext hq⟩

theorem exists_ptEquiv {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G f φ) (T : Over S') {t : T.left ⟶ S} (ht : t = T.hom ≫ f) :
    ∃ E : (T ⟶ G') ≃* (Over.mk t ⟶ G), ∀ x, (E x).left = x.left ≫ φ := by
  subst ht
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun x y e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun x => ?_⟩, fun _ => rfl⟩
  exact ⟨Over.homMk (h.1.lift x.left T.hom (Over.w x)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem exists_isTorExt_of_pullback {G B : Over S} {G' B' : Over S'} [GrpObj G] [GrpObj G'] [GrpObj B] [GrpObj B']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {ψ : B'.left ⟶ B.left} (hG : IsGrpPullback G' G f φ)
    (hB : IsGrpPullback B' B f ψ) {s' : Sp Ω ⟶ S'} {s : Sp Ω ⟶ S} (hs : s' ≫ f = s) {X : Type} [AddCommGroup X]
    {τ' : PtHom s' s' G' B'} {io' : TorHom s' G' X} (h : IsTorExt s' s' G' B' X τ' io') :
    ∃ (τ : PtHom s s G B) (io : TorHom s G X), IsTorExt s s G B X τ io ∧
      ∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt s A ⟶ G), ∃ x' : overAt s' A ⟶ G',
        x'.left ≫ φ = x.left ∧ (τ A x).left = (τ' A x').left ≫ ψ := by
  have ht : ∀ (A : Type) [CommRing A] [Algebra Ω A], spMap (algebraMap Ω A) ≫ s = (overAt s' A).hom ≫ f :=
    fun A _ _ => by rw [← hs]; exact (Category.assoc _ _ _).symm
  choose E hE using fun (A : Type) [CommRing A] [Algebra Ω A] => exists_ptEquiv hG (overAt s' A) (ht A)
  choose F hF using fun (A : Type) [CommRing A] [Algebra Ω A] => exists_ptEquiv hB (overAt s' A) (ht A)
  have nE : ∀ (A A' : Type) [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A'] (g : A →ₐ[Ω] A')
      (x : overAt s' A ⟶ G'), E A' (homAt s' g ≫ x) = homAt s g ≫ E A x := fun A A' _ _ _ _ g x =>
    Over.OverMorphism.ext ((hE A' _).trans ((Category.assoc _ x.left φ).trans
      (congrArg (spMap (g : A →+* A') ≫ ·) (hE A x).symm)))
  have nF : ∀ (A A' : Type) [CommRing A] [Algebra Ω A] [CommRing A'] [Algebra Ω A'] (g : A →ₐ[Ω] A')
      (x : overAt s' A ⟶ B'), F A' (homAt s' g ≫ x) = homAt s g ≫ F A x := fun A A' _ _ _ _ g x =>
    Over.OverMorphism.ext ((hF A' _).trans ((Category.assoc _ x.left ψ).trans
      (congrArg (spMap (g : A →+* A') ≫ ·) (hF A x).symm)))
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨fun A _ _ => ((F A).toMonoidHom.comp (τ' A)).comp (E A).symm.toMonoidHom,
    fun A _ _ => (E A).toMonoidHom.comp (io' A),
    ⟨fun A A' _ _ _ _ g x => ?_, fun A A' _ _ _ _ g χ => ?_, fun A _ _ => (E A).injective.comp (h₃ A),
      fun A _ _ x => ?_, fun A _ _ π hn y hy => ?_⟩, fun A _ _ x => ?_⟩
  · obtain ⟨x, rfl⟩ := (E A).surjective x
    change F A' (τ' A' ((E A').symm _)) = _ ≫ F A (τ' A ((E A).symm _))
    rw [← nE, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, h₁, nF]
  · change E A' (io' A' _) = _ ≫ E A (io' A χ)
    rw [h₂, nE]
  · obtain ⟨x, rfl⟩ := (E A).surjective x
    change F A (τ' A ((E A).symm _)) = 1 ↔ ∃ χ, E A (io' A χ) = _
    rw [MulEquiv.symm_apply_apply, MulEquiv.map_eq_one_iff, h₄]
    exact exists_congr fun χ => (E A).injective.eq_iff.symm
  · obtain ⟨y, rfl⟩ := (F A).surjective y
    rw [← nF, MulEquiv.map_eq_one_iff] at hy
    obtain ⟨x, hx, rfl⟩ := h₅ A π hn y hy
    refine ⟨E A x, by rw [← nE, hx, map_one], ?_⟩
    change F A (τ' A ((E A).symm _)) = _
    rw [MulEquiv.symm_apply_apply]
  · refine ⟨(E A).symm x, (hE A _).symm.trans ?_, hF A _⟩
    rw [MulEquiv.apply_symm_apply]

theorem exists_isTorExt : ∀ (W : Type) [CommRing W] [IsDomain W] (I : Ideal W) (D : Out.DegPre W) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (gt : Out.GtCoord I D 0 G) (Ω : Type) [Field Ω] (β : W →+* Ω), (∀ a ∈ I, β a = 0) → ∃ (τ : PtHom (spMap β) (spMap β) G D.P.A) (io : TorHom (spMap β) G D.X), IsTorExt (spMap β) (spMap β) G D.P.A D.X τ io ∧ ∀ (A : Type) [CommRing A] [Algebra Ω A] (x : overAt (spMap β) A ⟶ G) (x₀ : Sp A ⟶ (Out.thickObj W I 0 G).left), x₀ ≫ (Out.fstG I 0 G).left = x.left → (τ A x).left = x₀ ≫ gt.pG.left := by
  intro W _ _ I D G _ _ g Ω _ β hβ
  let β₀ : W ⧸ I ^ (0 + 1) →+* Ω := Ideal.Quotient.lift _ β (by simpa using hβ)
  have e : spMap β₀ ≫ Out.thick W I 0 = spMap β := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    rfl
  have := g.q_hom
  have := g.i_hom
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have := (H1.torus_dim (Sp (W ⧸ I ^ (0 + 1))) D.X).smooth
  have : Smooth g.q.left := by
    refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((H1.torsor_pullback g.i g.q g.isKernel).map (Over.forget _)).flip
      ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact g.q.left)⟩ ?_
    exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  obtain ⟨τ, io, h, hτ⟩ := exists_isTorExt_of_pullback (isGrpPullback_pullback G (Out.thick W I 0))
    (isGrpPullback_pullback D.P.A (Out.thick W I 0)) e (isTorExt_of_kernel (spMap β₀) g.i g.q g.isKernel)
  refine ⟨τ, io, h, fun A _ _ x x₀ hx => ?_⟩
  obtain ⟨x', h₁, h₂⟩ := hτ A x
  have : IsClosedImmersion (Out.thick W I 0) := .spec_of_surjective _ Ideal.Quotient.mk_surjective
  obtain rfl : x₀ = x'.left := (cancel_mono (pullback.fst G.hom (Out.thick W I 0))).1 (hx.trans h₁.symm)
  exact h₂.trans (Category.assoc _ _ _)

end GlobalTheory.TorExtPoints
end
