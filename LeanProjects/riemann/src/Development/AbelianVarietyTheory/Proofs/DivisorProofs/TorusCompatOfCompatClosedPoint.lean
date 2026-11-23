import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCommGroupSchemeEqOfPowEqOfClosedPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

noncomputable section

namespace GlobalTheory.Poinc.FibLat.ClosedLift

open GlobalTheory.SplitTorus (torusMap bcMap)

theorem endo_of_closed {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsSeparated G.hom] {V : Type} [CommRing V]
    [IsDomain V] {ξ : Sp V ⟶ S} {G₁ : Over (Sp V)} [GrpObj G₁] {φ₁ : G₁.left ⟶ G.left}
    (h : IsGrpPullback G₁ G ξ φ₁) {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (j : splitTorus (Sp V) X ⟶ G₁) [IsMonHom j] {GK : Over (Sp (FractionRing V))} [GrpObj GK]
    {ψ : GK.left ⟶ G₁.left} (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ)
    (hK : IsTorPart (pullTorus hψ j)) {κ : Type} [Field κ] {b : V →+* κ} {G₀ : Over (Sp κ)} [GrpObj G₀]
    {ψ₀ : G₀.left ⟶ G₁.left} (hψ₀ : IsGrpPullback G₀ G₁ (spMap b) ψ₀) (h0 : IsTorPart (pullTorus hψ₀ j))
    (u : G ⟶ G) [IsMonHom u] (r : X →+ X)
    (hr : (pullTorus hψ₀ j).left ≫ (ψ₀ ≫ φ₁) ≫ u.left = (torusMap _ r ≫ pullTorus hψ₀ j).left ≫ ψ₀ ≫ φ₁) :
    j.left ≫ φ₁ ≫ u.left = (torusMap _ r ≫ j).left ≫ φ₁ := by
  obtain ⟨u₁, hu₁, pa⟩ := GlobalTheory.SymBaseChange.exists_endo h u
  have hw : u₁.left ≫ φ₁ = φ₁ ≫ u.left := by
    have := congrArg CommaMorphism.left (pa (𝟙 G₁))
    simpa [pushPt] using this
  haveI := hu₁
  obtain ⟨s, hs⟩ := hK.factor (pullTorus hψ (j ≫ u₁)) inferInstance
  rw [← pullTorus_torusMap_comp] at hs
  obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap V (FractionRing V))) ∧
      IsSchemeTheoreticallyDominant (spMap (algebraMap V (FractionRing V))) :=
    GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)
  haveI : IsSeparated G₁.hom := MorphismProperty.of_isPullback h.1 ‹_›
  have key : j ≫ u₁ = torusMap _ s ≫ j :=
    GlobalTheory.ExtUnique.over_hom_ext_of_isPullback
      (GlobalTheory.SplitTorus.isPullback_bcMap (spMap (algebraMap V (FractionRing V))) X)
      (by rw [← pullTorus_left hψ, ← pullTorus_left hψ, hs])
  have k0 : torusMap _ s ≫ pullTorus hψ₀ j = torusMap _ r ≫ pullTorus hψ₀ j := by
    apply hom_ext_of_pullback (hψ₀.comp h)
    have e1 := pullTorus_left hψ₀ (j ≫ u₁)
    have e2 := pullTorus_left hψ₀ j
    calc (torusMap _ s ≫ pullTorus hψ₀ j).left ≫ ψ₀ ≫ φ₁
        = ((pullTorus hψ₀ (j ≫ u₁)).left ≫ ψ₀) ≫ φ₁ := by
          rw [← pullTorus_torusMap_comp, ← key, Category.assoc]
      _ = bcMap (spMap b) X ≫ j.left ≫ φ₁ ≫ u.left := by
          rw [e1]; simp [Category.assoc, hw]
      _ = ((pullTorus hψ₀ j).left ≫ ψ₀) ≫ φ₁ ≫ u.left := by
          rw [e2]; simp only [Category.assoc]
      _ = (torusMap _ r ≫ pullTorus hψ₀ j).left ≫ ψ₀ ≫ φ₁ := by
          rw [← hr]; simp only [Category.assoc]
  have hsr : s = r := h0.cancel k0
  subst hsr
  rw [← key, Over.comp_left, Category.assoc, hw]

theorem compat_of_closed : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → IsUnit (L : o) → (∀ e, IsMonHom (f e)) → (∀ t, gγ t ^ L = 1) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : I → X →+ X) (c : T → X →+ ZMod L) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ M.Z) (a : o →+* V) (G₁ : Over (Sp V)) [GrpObj G₁] (φ₁ : G₁.left ⟶ G.left), IsGrpPullback G₁ G ξ φ₁ → ∀ (j : splitTorus (Sp V) X ⟶ G₁), IsMonHom j → (∀ t, ExtNear (gγ t) (ξ (closedPoint V))) → ∀ (GK : Over (Sp (FractionRing V))) [GrpObj GK] (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), IsTorPart (pullTorus hψ j) → ∀ (κ : Type) [Field κ] (b : V →+* κ), IsLocalHom b → ∀ (G₀ : Over (Sp κ)) [GrpObj G₀] (ψ₀ : G₀.left ⟶ G₁.left) (hψ₀ : IsGrpPullback G₀ G₁ (spMap b) ψ₀), IsTorPart (pullTorus hψ₀ j) → Compat f gγ ζ L m c (spMap b ≫ ξ) (b.comp a) (ψ₀ ≫ φ₁) (pullTorus hψ₀ j) → Compat f gγ ζ L m c ξ a φ₁ j := by
  intro o Ω _ _ _ M G _ _ hG I T f gγ ζ L hL hζ hLu hf hgγ X _ _ _ m c V _ _ _ ξ a G₁ _ φ₁ h j hj hext GK _ ψ hψ hK
    κ _ b hb G₀ _ ψ₀ hψ₀ h0 hC
  haveI := hG.separated
  haveI := hj
  haveI : NeZero L := ⟨hL.ne'⟩
  refine ⟨fun e => ?_, fun t => ?_⟩
  · haveI := hf e
    exact endo_of_closed h j hψ hK hψ₀ h0 (f e) (m e) (hC.1 e)
  obtain ⟨z₀, hz₀, hv₀⟩ := hC.2 t
  have hζV : (Units.map a.toMonoidHom ζ) ^ L = 1 := by rw [← map_pow, hζ, map_one]
  have hpow : ∀ k : ℕ, ((Units.map a.toMonoidHom ζ) ^ k) ^ L = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, hζV, one_pow]
  let F : Multiplicative X →* Γ(Sp V, ⊤)ˣ :=
    { toFun := fun χ => unitOn (Units.map a.toMonoidHom ζ ^ (c t (Multiplicative.toAdd χ)).val)
      map_one' := by simp [unitOn]
      map_mul' := fun x y => by
        rw [toAdd_mul, map_add, ZMod.val_add, ← pow_eq_pow_mod _ hζV, pow_add]
        simp [unitOn] }
  let Z1 : Over (Sp V) := Over.mk (𝟙 (Sp V))
  obtain ⟨z, hz⟩ : ∃ z : Z1 ⟶ splitTorus (Sp V) X, GlobalTheory.splitTorusPointsEquiv (Sp V) X Z1 z = F :=
    ⟨_, MulEquiv.apply_symm_apply _ _⟩
  have hzχ : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (Units.map a.toMonoidHom ζ ^ (c t χ).val) := fun χ => by
    show GlobalTheory.splitTorusPointsEquiv (Sp V) X Z1 z (Multiplicative.ofAdd χ) = _
    rw [hz]; rfl
  have hzL : z ^ L = 1 := by
    apply (GlobalTheory.splitTorusPointsEquiv (Sp V) X Z1).injective
    rw [map_pow, hz, map_one]
    refine MonoidHom.ext fun χ => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    show unitOn _ ^ L = 1
    rw [unitOn, ← map_pow, hpow, map_one]

  let x : Over.mk (Z1.hom ≫ ξ) ⟶ G := pushPt h.1.w (z ≫ j)
  have hxL : x ^ L = 1 := by
    have e1 : pushPt h.1.w ((z ≫ j) ^ L) = x ^ L := map_pow (pushHom h Z1) (z ≫ j) L
    rw [← e1, ← pow_comp, hzL, one_comp]
    exact map_one (pushHom h Z1)

  obtain ⟨v, hv⟩ := ExtNear.exists_valAt ξ (hext t)
  have hvb : spMap b ≫ v = (z₀ ≫ pullTorus hψ₀ j).left ≫ ψ₀ ≫ φ₁ := ValAt.unique (hv.comp (spMap b)) hv₀
  obtain ⟨W, hW, s', ⟨hW1, hW2⟩, hs', hsv⟩ := hv
  let H : Over.mk W.ι ⟶ G := Over.homMk hW hW1
  have hne : (W : Set M.Z).Nonempty := ⟨ξ (closedPoint V), by rw [← hs']; exact (s' (closedPoint V)).2⟩
  haveI : Nonempty W.toScheme := ⟨⟨_, hne.some_mem⟩⟩
  haveI : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  have hr : Set.range M.pt ⊆ Set.range W.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hne (x := w) trivial
  let x₀ := IsOpenImmersion.lift W.ι M.pt hr
  have hx₀ : x₀ ≫ W.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  haveI : IsDominant (x₀ ≫ W.ι) := hx₀ ▸ M.isDominant_pt
  haveI : IsDominant x₀ := IsDominant.of_comp_of_isOpenImmersion x₀ W.ι
  have hHL : H ^ L = 1 := by
    let u : Over.mk M.pt ⟶ Over.mk W.ι := Over.homMk x₀ hx₀
    have hu : u ≫ H = gγ t := Over.OverMorphism.ext (hW2 x₀ hx₀)
    have e : u ≫ H ^ L = u ≫ 1 := by rw [comp_pow, hu, hgγ t, comp_one]
    apply Over.OverMorphism.ext
    haveI : IsReduced (Over.mk W.ι).left := inferInstanceAs (IsReduced W.toScheme)
    refine ext_of_isDominant_of_isSeparated (s := G.hom) ?_ x₀ ?_
    · rw [Over.w, Over.w]
    · exact congrArg CommaMorphism.left e
  let σ : Over.mk (Z1.hom ≫ ξ) ⟶ Over.mk W.ι := Over.homMk s' (by
    show s' ≫ W.ι = 𝟙 _ ≫ ξ
    rw [hs', Category.id_comp])
  let y : Over.mk (Z1.hom ≫ ξ) ⟶ G := σ ≫ H
  have hyL : y ^ L = 1 := by
    show (σ ≫ H) ^ L = 1
    rw [← comp_pow, hHL, comp_one]

  have hw' : (spMap b ≫ z.left) ≫ (splitTorus (Sp V) X).hom = 𝟙 _ ≫ spMap b := by
    rw [Category.assoc, Over.w z]; simp [Z1]
  let z' : Over.mk (𝟙 (Sp κ)) ⟶ splitTorus (Sp κ) X :=
    Over.homMk ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift (spMap b ≫ z.left) (𝟙 _) hw')
      ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_snd _ _ _)
  have hz'l : z'.left ≫ bcMap (spMap b) X = spMap b ≫ z.left :=
    (GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_fst _ _ _
  have hz'χ : ∀ χ, GlobalTheory.UU.chV z' χ = unitOn (Units.map (b.comp a).toMonoidHom ζ ^ (c t χ).val) := fun χ => by
    ext
    have e := congrArg Units.val (hzχ χ)
    rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val] at e ⊢
    rw [← GlobalTheory.SplitTorus.bcMap_appTop_chi (spMap b), ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hz'l,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    erw [e]
    simp only [unitOn, Units.coe_map]
    have := congrArg (fun k => k.hom ((Units.map a.toMonoidHom ζ ^ (c t χ).val : Vˣ) : V))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom b))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    refine this.symm.trans ?_
    simp
  have hzz : z₀ = z' := by
    apply (GlobalTheory.splitTorusPointsEquiv (Sp κ) X _).injective
    refine MonoidHom.ext fun χ => ?_
    exact (hz₀ (Multiplicative.toAdd χ)).trans (hz'χ (Multiplicative.toAdd χ)).symm
  have hcl : spMap b ≫ x.left = spMap b ≫ y.left := by
    show spMap b ≫ (z ≫ j).left ≫ φ₁ = spMap b ≫ s' ≫ hW
    rw [hsv, hvb, hzz]
    simp only [Over.comp_left, Category.assoc]
    rw [reassoc_of% (pullTorus_left hψ₀ j), reassoc_of% hz'l]
  have hLV : IsUnit (L : V) := by simpa using hLu.map a
  have hxy : x = y := GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint M.Z G hG.smooth V (Z1.hom ≫ ξ) L hLV x y
    (by rw [hxL, hyL]) κ b hb hcl
  refine ⟨z, hzχ, ?_⟩
  have e' : (z ≫ j).left ≫ φ₁ = v := (congrArg CommaMorphism.left hxy).trans hsv
  rw [e']
  exact ⟨W, hW, s', ⟨hW1, hW2⟩, hs', hsv⟩

end GlobalTheory.Poinc.FibLat.ClosedLift
