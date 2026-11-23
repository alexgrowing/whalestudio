import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalLiftOfSmooth
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.SpecialTorsion

section General
variable {S S' : Scheme.{0}}

def Killed (G : Over S) [GrpObj G] (n : ℕ) {Y : Scheme.{0}} (c : Y ⟶ G.left) : Prop :=
  c ≫ (𝟙 G ^ n : G ⟶ G).left = c ≫ (1 : G ⟶ G).left

theorem pow_eq_one_iff {G T : Over S} [GrpObj G] (n : ℕ) (x : T ⟶ G) :
    x ^ n = 1 ↔ Killed G n x.left := by
  have h1 : x ^ n = x ≫ (𝟙 G ^ n : G ⟶ G) := by rw [comp_pow, Category.comp_id]
  have h2 : (1 : T ⟶ G) = x ≫ (1 : G ⟶ G) := by rw [comp_one]
  rw [h1, h2]
  exact ⟨fun h => congrArg Over.Hom.left h, fun h => Over.OverMorphism.ext h⟩

theorem Killed.comp {G : Over S} [GrpObj G] {n : ℕ} {Y Y' : Scheme.{0}} {c : Y ⟶ G.left}
    (h : Killed G n c) (t : Y' ⟶ Y) : Killed G n (t ≫ c) := by
  unfold Killed at h ⊢
  rw [Category.assoc, h, Category.assoc]

theorem killed_comp_iff {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℕ) {Y : Scheme.{0}} (c : Y ⟶ G'.left) :
    Killed G n (c ≫ φ) ↔ Killed G' n c := by
  let x : Over.mk (c ≫ G'.hom) ⟶ G' := Over.homMk c rfl
  have hinj : Function.Injective (pushHom h (Over.mk (c ≫ G'.hom))) := fun a b hab =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg (·.left) hab) ((Over.w a).trans (Over.w b).symm))
  refine (pow_eq_one_iff n (pushHom h _ x)).symm.trans (Iff.trans ?_ (pow_eq_one_iff n x))
  rw [← map_pow, map_eq_one_iff _ hinj]

theorem killed_comp_iso_iff {G G' : Over S} [GrpObj G] [GrpObj G'] (e : G' ≅ G) [IsMonHom e.hom]
    (n : ℕ) {Y : Scheme.{0}} (c : Y ⟶ G'.left) :
    Killed G n (c ≫ e.hom.left) ↔ Killed G' n c := by
  let x : Over.mk (c ≫ G'.hom) ⟶ G' := Over.homMk c rfl
  refine (pow_eq_one_iff n (x ≫ e.hom)).symm.trans (Iff.trans ?_ (pow_eq_one_iff n x))
  rw [← pow_comp, ← one_comp e.hom, cancel_mono]

theorem Killed.of_dominant {G : Over S} [GrpObj G] [IsSeparated G.hom] {n : ℕ} {Y Y' : Scheme.{0}}
    [IsReduced Y] (t : Y' ⟶ Y) [IsDominant t] {c : Y ⟶ G.left} (h : Killed G n (t ≫ c)) :
    Killed G n c := by
  refine ext_of_isDominant_of_isSeparated G.hom ?_ t ?_
  · rw [Category.assoc, Category.assoc, Over.w, Over.w]
  · simpa only [Killed, Category.assoc] using h

theorem exists_affine_fac {O : Type} [CommRing O] [IsLocalRing O] {X : Scheme.{0}} (c : Sp O ⟶ X) :
    ∃ (R : CommRingCat.{0}) (i : Spec R ⟶ X) (_ : IsOpenImmersion i) (g : R ⟶ CommRingCat.of O),
      Spec.map g ≫ i = c := by
  obtain ⟨R, i, hi, hx⟩ : ∃ (R : CommRingCat.{0}) (i : Spec R ⟶ X) (_ : IsOpenImmersion i),
      c (IsLocalRing.closedPoint O) ∈ Set.range i :=
    ⟨_, X.affineOpenCover.f (X.affineOpenCover.idx (c (IsLocalRing.closedPoint O))), inferInstance,
      X.affineOpenCover.covers _⟩
  have h := Scheme.preimage_eq_top_of_closedPoint_mem c (U := i.opensRange) hx
  have hr : Set.range c ⊆ Set.range i := by
    rintro _ ⟨y, rfl⟩
    exact (show y ∈ c ⁻¹ᵁ i.opensRange from h ▸ trivial)
  exact ⟨R, i, hi, Spec.preimage (IsOpenImmersion.lift i c hr), by
    rw [Spec.map_preimage, IsOpenImmersion.lift_fac]⟩

theorem exists_descent {V K O C : Type} [CommRing V] [Field K] [CommRing O] [IsLocalRing O] [Field C]
    (a : V →+* K) (ha : Function.Injective a) (b : K →+* C) (d : O →+* C)
    (hV : ∀ x : K, b x ∈ Set.range d → x ∈ Set.range a) {X : Scheme.{0}} (c : Sp O ⟶ X) (x : Sp K ⟶ X)
    (h : spMap d ≫ c = spMap b ≫ x) : ∃ y : Sp V ⟶ X, spMap a ≫ y = x := by
  obtain ⟨R, i, hi, g, rfl⟩ := exists_affine_fac c
  have hr : Set.range x ⊆ Set.range i := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨z⟩ : Nonempty (Sp C) := inferInstance
    have hy : y = spMap b z := Subsingleton.elim (α := PrimeSpectrum K) _ _
    refine ⟨(spMap d ≫ Spec.map g) z, ?_⟩
    rw [hy, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Category.assoc, h]
  obtain ⟨g', hg'⟩ := Spec.map_surjective (IsOpenImmersion.lift i x hr)
  have hx : Spec.map g' ≫ i = x := by rw [hg', IsOpenImmersion.lift_fac]
  subst hx
  rw [← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp] at h
  have h' := Spec.map_injective h
  have hm : ∀ r, g'.hom r ∈ a.range := fun r => hV _ ⟨g.hom r, congrArg (fun f => f.hom r) h'⟩
  let e : V ≃+* a.range := RingEquiv.ofBijective a.rangeRestrict
    ⟨fun _ _ h => ha (congrArg Subtype.val h), a.rangeRestrict_surjective⟩
  refine ⟨Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp (g'.hom.codRestrict _ hm))) ≫ i, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext r
  exact congrArg Subtype.val (e.apply_symm_apply ⟨_, hm r⟩)

end General

section Test
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ}
  [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem isUnit_OO (h : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) : IsUnit ((S.r * S.N : ℕ) : OO p) := by
  simpa only [map_natCast] using
    S.unit.map ((y₀.comp (algebraMap o S.R)).codRestrict (OO p) fun a => (mem_OO_iff _).2 (h a))

theorem isUnit_V {n : ℕ} (h : IsUnit (n : OO p)) : IsUnit (n : u.V) := by
  obtain ⟨m, hm⟩ := h.exists_right_inv
  have hm' : (n : PadicAlgCl p) * (m : PadicAlgCl p) = 1 := by
    simpa using congrArg (OO p).subtype hm
  have h0 : (n : FractionRing u.V) ≠ 0 := fun h0 => by
    have := congrArg (algebraMap (FractionRing u.V) (PadicAlgCl p)) h0
    rw [map_natCast, map_zero] at this
    simp [this] at hm'
  obtain ⟨v, hv⟩ := (u.norm_le (n : FractionRing u.V)⁻¹).1 (by
    rw [map_inv₀, map_natCast, ← eq_inv_of_mul_eq_one_right hm']
    exact (mem_OO_iff _).1 m.2)
  refine IsUnit.of_mul_eq_one v (IsFractionRing.injective u.V (FractionRing u.V) ?_)
  rw [map_mul, map_natCast, hv, map_one, mul_inv_cancel₀ h0]

theorem gPt_j : gPt p ≫ spMap u.j =
    spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ spMap (algebraMap u.V (FractionRing u.V)) := by
  rw [← spMap_comp, ← spMap_comp]
  rfl

theorem spMap_y₀ : spMap y₀ = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ spMap u.yK := by
  rw [← spMap_comp, u.fac]

theorem isPullback_gen : IsPullback (u.U.gen.hom.left ≫ u.φ) (pullback.snd u.G.hom (jK u.V))
    ρ.P.A.hom (spMap u.yK) := by
  have : IsIso (show pullback u.G.hom (jK u.V) ⟶ u.A.A.left from u.U.gen.hom.left) :=
    ((Over.forget _).mapIso u.U.gen).isIso_hom
  have h : IsPullback u.U.gen.hom.left (pullback.snd u.G.hom (jK u.V)) u.A.A.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨(Over.w u.U.gen.hom).trans (Category.comp_id _).symm⟩
  simpa only [Category.id_comp] using h.paste_horiz u.cart.1

theorem killed_gen_iff (n : ℕ) {Y : Scheme.{0}} (t : Y ⟶ pullback u.G.hom (jK u.V)) :
    Killed ρ.P.A n (t ≫ u.U.gen.hom.left ≫ u.φ) ↔ Killed u.G n (t ≫ pullback.fst u.G.hom (jK u.V)) := by
  have := u.U.gen_hom
  have h1 := killed_comp_iff u.cart n (t ≫ u.U.gen.hom.left)
  rw [Category.assoc] at h1
  exact h1.trans ((killed_comp_iso_iff u.U.gen n t).trans
    (killed_comp_iff (Pdiv.PullbackComparison.isGrpPullback (jK u.V) u.G) n t).symm)

theorem killed_pt (ρ : S.Real) (a : S.Gam) : Killed ρ.P.A (S.r * S.N) (ρ.pt a).left := by
  let f : Multiplicative S.Gam →* (baseOver (Sp S.R) ⟶ ρ.P.A) :=
    MonoidHom.mk' (fun a => ρ.pt a.toAdd) fun a b => ρ.pt_add _ _
  refine (pow_eq_one_iff _ (f (Multiplicative.ofAdd a))).1 ?_
  rw [← map_pow, ← ofAdd_nsmul, show (S.r * S.N) • a = 0 from ?_, ofAdd_zero, map_one]
  funext i
  rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]

theorem isDominant_jK : IsDominant (jK u.V) :=
  ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap u.V (FractionRing u.V))).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective _ _)]
    exact bot_le)⟩

theorem integral_of (a : S.Gam) (c : Sp (OO p) ⟶ u.G.left) (a' : u.PtC) (h₂ : gPt p ≫ c = u.toG a')
    (h₃ : u.toA a' = spMap y₀ ≫ (ρ.pt a).left) : u.Integral a := by
  have hw : (spMap u.yK ≫ (ρ.pt a).left) ≫ ρ.P.A.hom = 𝟙 _ ≫ spMap u.yK := by
    rw [Category.assoc, Over.w, Category.id_comp]
    exact Category.comp_id _
  let x := (isPullback_gen u).lift _ _ hw
  have hx : spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ x = a'.left := by
    refine (isPullback_gen u).hom_ext ?_ ?_
    · rw [Category.assoc, IsPullback.lift_fst, ← Category.assoc, ← spMap_y₀]
      exact h₃.symm
    · rw [Category.assoc, IsPullback.lift_snd, Category.comp_id]
      exact (Over.w a').symm
  obtain ⟨h, hh⟩ := exists_descent (algebraMap u.V (FractionRing u.V)) (IsFractionRing.injective _ _)
    (algebraMap (FractionRing u.V) (PadicAlgCl p)) (OO p).subtype
    (fun z ⟨w, hw⟩ => (u.norm_le z).1 ((mem_OO_iff _).1 (hw ▸ w.2))) c
    (x ≫ pullback.fst u.G.hom (jK u.V)) (by rw [← Category.assoc, hx]; exact h₂)
  refine ⟨h, x, ?_, hh.symm, IsPullback.lift_snd _ _ _ _, IsPullback.lift_fst _ _ _ _⟩
  have := isDominant_jK u
  refine ext_of_isDominant (jK u.V) ?_
  rw [← Category.assoc, hh, Category.assoc, pullback.condition, ← Category.assoc,
    IsPullback.lift_snd, Category.id_comp, Category.comp_id]

theorem exists_lift (hn : IsUnit ((S.r * S.N : ℕ) : u.V)) (x : Sp (kb p) ⟶ u.G.left)
    (hx : x ≫ u.G.hom = rPt p ≫ spMap u.j) (hk : Killed u.G (S.r * S.N) x) :
    ∃ a, u.Integral a ∧ ∃ (c : Sp (OO p) ⟶ u.G.left) (a' : u.PtC), c ≫ u.G.hom = spMap u.j ∧
      gPt p ≫ c = u.toG a' ∧ u.toA a' = spMap y₀ ≫ (ρ.pt a).left ∧ rPt p ≫ c = x := by
  have := u.U.smooth
  have : Etale (𝟙 u.G ^ (S.r * S.N) : u.G ⟶ u.G).left := GrpTangent.etale_id_pow u.G (by
    simpa only [map_natCast] using hn.map (Scheme.ΓSpecIso (CommRingCat.of u.V)).inv.hom)
  have h1 : (1 : u.G ⟶ u.G).left = u.G.hom ≫ η[u.G].left := by
    rw [Hom.one_def, Over.comp_left, show (toUnit u.G).left = u.G.hom from Over.w (toUnit u.G)]
  obtain ⟨c, hc, hc'⟩ := ZJ.exists_classical_lift_of_smooth p _ _
    (𝟙 u.G ^ (S.r * S.N) : u.G ⟶ u.G).left (spMap u.j ≫ η[u.G].left) x
    (by rw [hk, h1, ← Category.assoc, hx, Category.assoc])
  have hcj : c ≫ u.G.hom = spMap u.j := by
    rw [← Over.w (𝟙 u.G ^ (S.r * S.N) : u.G ⟶ u.G), ← Category.assoc, hc, Category.assoc, Over.w]
    exact Category.comp_id _
  have hck : Killed u.G (S.r * S.N) c := by
    rw [Killed, hc, h1, ← Category.assoc, hcj]
  have hw : (gPt p ≫ c) ≫ u.G.hom = spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V := by
    rw [Category.assoc, hcj, gPt_j]
  let a' : u.PtC := Over.homMk (pullback.lift _ _ hw) (pullback.lift_snd _ _ _)
  have h₂ : gPt p ≫ c = u.toG a' := (pullback.lift_fst _ _ _).symm
  have hA : Killed ρ.P.A (S.r * S.N) (u.toA a') :=
    (killed_gen_iff u _ a'.left).2 (show Killed _ _ (u.toG a') from h₂ ▸ hck.comp _)
  have hz : u.toA a' ≫ ρ.P.A.hom = spMap y₀ := by
    rw [spMap_y₀ u, ThetaSys.Real.UTest.toA, Category.assoc, (isPullback_gen u).w, ← Category.assoc]
    congr 1
    exact Over.w a'
  obtain ⟨a, ha, -⟩ := ρ.pt_bij (PadicAlgCl p) (spMap y₀) (Over.homMk (u.toA a') hz)
    ((pow_eq_one_iff _ _).2 hA)
  have h₃ : u.toA a' = spMap y₀ ≫ (ρ.pt a).left := (congrArg Over.Hom.left ha).symm
  exact ⟨a, integral_of u a c a' h₂ h₃, c, a', hcj, h₂, h₃, hc'⟩

theorem exists_of_integral (a : S.Gam) (ha : u.Integral a) :
    ∃ (c : Sp (OO p) ⟶ u.G.left) (a' : u.PtC), c ≫ u.G.hom = spMap u.j ∧ gPt p ≫ c = u.toG a' ∧
      u.toA a' = spMap y₀ ≫ (ρ.pt a).left ∧ Killed u.G (S.r * S.N) c := by
  obtain ⟨h, x, h₁, h₂, h₃, h₄⟩ := ha
  have := u.U.separated
  have := isDominant_jK u
  have hk : Killed u.G (S.r * S.N) h := by
    refine Killed.of_dominant (jK u.V) ?_
    rw [← h₂, ← killed_gen_iff, h₄]
    exact (killed_pt ρ a).comp _
  refine ⟨spMap u.j ≫ h, Over.homMk (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ x) ?_,
    ?_, ?_, ?_, hk.comp _⟩
  · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₃).trans (Category.comp_id _))
  · rw [Category.assoc, h₁, Category.comp_id]
  · rw [← Category.assoc, gPt_j, Category.assoc, ← h₂]
    exact (Category.assoc _ _ _).symm
  · refine (Category.assoc _ _ _).trans ?_
    rw [h₄, ← Category.assoc, ← spMap_y₀]

end Test

end GlobalTheory.SpecialTorsion

namespace GlobalTheory
open SpecialTorsion

theorem ZH.special_torsion_eq_reduction :
    GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (md : Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ((S.r * S.N : ℕ) : kb p) ≠ 0 ∧ (∀ x : md.Φ.Pt, x ^ (S.r * S.N) = 1 → ∃ a ∈ l.yy.ker, ∃ (c : Sp (OO p) ⟶ u.G.left) (a' : u.PtC), c ≫ u.G.hom = spMap u.j ∧ gPt p ≫ c = u.toG a' ∧ u.toA a' = spMap y₀ ≫ (ρ.pt a).left ∧ rPt p ≫ c = x.left ≫ md.r) ∧ ∀ a ∈ l.yy.ker, ∃ (c : Sp (OO p) ⟶ u.G.left) (a' : u.PtC) (x : md.Φ.Pt), c ≫ u.G.hom = spMap u.j ∧ gPt p ≫ c = u.toG a' ∧ u.toA a' = spMap y₀ ≫ (ρ.pt a).left ∧ rPt p ≫ c = x.left ≫ md.r ∧ x ^ (S.r * S.N) = 1 := by
  intro _ o Ω _ _ _ _ S ρ p _ y₀ u l σ cls md h
  have hO := isUnit_OO h
  refine ⟨?_, fun x hx => ?_, fun a ha => ?_⟩
  · simpa only [map_natCast] using (hO.map (IsLocalRing.residue (OO p))).ne_zero
  · obtain ⟨a, ha, h'⟩ := exists_lift u (isUnit_V u hO) (x.left ≫ md.r)
      (by rw [Category.assoc, md.cart.1.w, ← Category.assoc, Over.w x]; exact Category.id_comp _)
      ((killed_comp_iff md.cart _ _).2 ((pow_eq_one_iff _ x).1 hx))
    exact ⟨a, (l.ker_iff a).2 ha, h'⟩
  · obtain ⟨c, a', h₁, h₂, h₃, hk⟩ := exists_of_integral u a ((l.ker_iff a).1 ha)
    have hw : (rPt p ≫ c) ≫ u.G.hom = 𝟙 _ ≫ rPt p ≫ spMap u.j := by
      rw [Category.assoc, h₁, Category.id_comp]
    let x : md.Φ.Pt := Over.homMk (md.cart.1.lift _ _ hw) (md.cart.1.lift_snd _ _ _)
    have hx : rPt p ≫ c = x.left ≫ md.r := (md.cart.1.lift_fst _ _ _).symm
    exact ⟨c, a', x, h₁, h₂, h₃, hx,
      (pow_eq_one_iff _ x).2 ((killed_comp_iff md.cart _ _).1 (hx ▸ hk.comp _))⟩

end GlobalTheory
