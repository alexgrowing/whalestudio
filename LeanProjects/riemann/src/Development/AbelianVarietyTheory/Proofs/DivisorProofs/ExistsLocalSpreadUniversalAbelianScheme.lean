import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSysUOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitIntCastStalkIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartRatLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonBaseChangeOfUOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticLevelExtendsNoetherianNormalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingOnAffineOpenFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolAVDimEqOfGrpPullbackField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisExtendsNormalAffineC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianVarietyPullbackAffineOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomLift
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCovSep.LocalSpread

open GlobalTheory.Points

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_chart (C : UCompact Xo c) {o₁ Ω : Type} [CommRing o₁] [Field Ω] [Algebra o₁ Ω] [CharZero Ω]
    (M : RatModel o₁ Ω) (π : M.Z ⟶ C.Z) (uη : Sp Ω ⟶ Xo.XF c) (hπ : M.pt ≫ π = uη ≫ C.i) (w : M.Z)
    (hw : π w ∈ Set.range C.i) :
    ∃ (U₀ : M.Z.Opens) (u₀ : Sp (ratHull (M.ringOn U₀)) ⟶ Xo.XF c), w ∈ U₀ ∧
      spMap (ratHull (M.ringOn U₀)).val.toRingHom ≫ u₀ = uη := by
  haveI := C.iF_open
  haveI := C.ded
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hemb := Scheme.Hom.isEmbedding (pullback.fst C.z (spMap C.b))
  obtain ⟨V, hVo, hV⟩ := hemb.isInducing.isOpen_iff.1 C.iF.isOpenEmbedding.isOpen_range
  have hwV : w ∈ π ⁻¹ᵁ ⟨V, hVo⟩ := by
    obtain ⟨x, hx⟩ := hw
    show π w ∈ V
    have : C.iF x ∈ pullback.fst C.z (spMap C.b) ⁻¹' V := hV ▸ ⟨x, rfl⟩
    rw [← hx]
    simpa using this
  obtain ⟨U, hU, hwU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := M.Z) hwV
  have hne : ((U : M.Z.Opens) : Set M.Z).Nonempty := ⟨w, hwU⟩
  let R₀ := M.ringOn U
  let φ : Γ(M.Z, U) ⟶ CommRingCat.of R₀ := CommRingCat.ofHom (M.sectionsEquiv U hne).toRingHom
  let f : Sp R₀ ⟶ M.Z := Spec.map φ ≫ hU.fromSpec
  let g : Sp (ratHull R₀) ⟶ C.Z := spMap (toRat R₀) ≫ f ≫ π
  have hgV : ∀ y, g y ∈ V := by
    intro y
    have hy : hU.fromSpec (Spec.map φ (spMap (toRat R₀) y)) ∈ Set.range hU.fromSpec := ⟨_, rfl⟩
    rw [hU.range_fromSpec] at hy
    exact hUV hy
  let ψ : C.o →+* ratHull R₀ := (Spec.preimage (g ≫ C.z)).hom
  have hψ : ∀ a : nonZeroDivisors C.o, IsUnit (ψ a) := by
    rintro ⟨a, ha⟩
    obtain ⟨n, hn, hdvd⟩ := ChartAt.exists_int_dvd C (nonZeroDivisors.ne_zero ha)
    exact isUnit_of_dvd_unit (map_dvd ψ hdvd) (by simpa using isUnit_intCast_ratHull R₀ hn)
  let θ : c.F →+* ratHull R₀ := IsLocalization.lift (M := nonZeroDivisors C.o) hψ
  have hθ : θ.comp (algebraMap C.o c.F) = ψ := IsLocalization.lift_comp hψ
  have hw' : g ≫ C.z = spMap θ ≫ spMap C.b := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    change _ = Spec.map (CommRingCat.ofHom (θ.comp (algebraMap C.o c.F)))
    rw [hθ]
    exact (Spec.map_preimage _).symm
  let g' : Sp (ratHull R₀) ⟶ pullback C.z (spMap C.b) := pullback.lift g (spMap θ) hw'
  have hrange : Set.range g' ⊆ Set.range C.iF := by
    rintro _ ⟨y, rfl⟩
    rw [← hV]
    show pullback.fst C.z (spMap C.b) (g' y) ∈ V
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    exact hgV y
  refine ⟨U, IsOpenImmersion.lift C.iF g' hrange, hwU, ?_⟩
  have hpt : ⊤ ≤ M.pt ⁻¹ᵁ U := M.top_le_preimage_pt hne
  have hφ : φ ≫ CommRingCat.ofHom R₀.val.toRingHom = valMap M.pt U hpt := by
    ext a
    show ((M.sectionsEquiv U hne a : M.ringOn U) : Ω) = _
    rw [RatModel.coe_sectionsEquiv, ← valR_eq, valF_eq_valR]
  have hf : spMap R₀.val.toRingHom ≫ f = M.pt := by
    simp only [f, ← Category.assoc]
    rw [spMap, ← Spec.map_comp, hφ, specMap_valMap_fromSpec]
  haveI := C.isPreimmersion_i
  rw [← cancel_mono C.i, ← hπ, Category.assoc, UCompact.i, ← Category.assoc (IsOpenImmersion.lift _ _ _),
    IsOpenImmersion.lift_fac, pullback.lift_fst]
  show spMap (ratHull R₀).val.toRingHom ≫ spMap (toRat R₀) ≫ f ≫ π = _
  rw [← Category.assoc, spMap_val_toRat, ← Category.assoc, hf]

theorem isUnit_intCast (C : UCompact Xo c) {o₁ Ω : Type} [CommRing o₁] [Field Ω] [Algebra o₁ Ω]
    (M : RatModel o₁ Ω) (π : M.Z ⟶ C.Z) (w : M.Z) (hw : π w ∈ Set.range C.i) (n : ℤ) (hn : n ≠ 0) :
    IsUnit (n : M.O w) := by
  obtain ⟨x, hx⟩ := hw
  rw [← map_intCast (M.stalkEquiv w) n, MulEquiv.isUnit_map, LocSpread.isUnit_intCast_stalk_iff π, ← hx,
    ← LocSpread.isUnit_intCast_stalk_iff C.i,
    LocSpread.isUnit_intCast_stalk_iff (pullback.snd _ _ : Xo.XF c ⟶ Sp c.F)]
  have h : IsUnit (n : c.F) := IsUnit.mk0 _ (Int.cast_ne_zero.2 hn)
  have h' := (h.map (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom).map
    ((Sp c.F).presheaf.germ ⊤ ((pullback.snd _ _ : Xo.XF c ⟶ Sp c.F) x) trivial).hom
  rwa [map_intCast, map_intCast] at h'

theorem exists_uAct {R R' Ω : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CommRing R']
    [Field Ω] [Algebra R Ω] [IsFractionRing R Ω] {σ : R →+* R'} (τ : R' →+* Ω) (hτ : Function.Injective τ)
    (e : τ.comp σ = algebraMap R Ω) {P : PolAV (Sp R)} {u : Sp R' ⟶ Xo.XF c} (h : UOver Xo c P σ u) :
    ∃ act : 𝓞 E → (P.A ⟶ P.A), (∀ a, IsMonHom (act a)) ∧ UAct Xo c P act σ u := by
  obtain ⟨G, _, α, β, hα, hβ, hL⟩ := h
  have e' : spMap τ ≫ spMap σ = spMap (algebraMap R Ω) := by rw [← Spec.map_comp, ← e]; rfl
  have hG := isGrpPullback_pullback G (spMap τ)
  have hGP := (hG.comp hα).congr e' rfl
  have hs := GlobalTheory.isSemiAbelian_of_isAbelianScheme _ P.isAb
  haveI := P.isAb.proper
  haveI := (PolPull.isAbelianScheme_of_isGrpPullback P.isAb hα).smooth
  haveI : IsSchemeTheoreticallyDominant (spMap τ) := ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hτ
  haveI : IsSchemeTheoreticallyDominant (pullback.fst G.hom (spMap τ)) := .of_isPullback hG.1.flip
  have key : ∀ a : 𝓞 E, ∃ F : P.A ⟶ P.A, IsMonHom F ∧ ∃ f : G ⟶ G, f.left ≫ α = α ≫ F.left ∧
      f.left ≫ β = β ≫ (Xo.univ.t.act.act (H.bar a)).left := fun a => by
    have w : (β ≫ (Xo.univ.t.act.act (H.bar a)).left) ≫ Xo.univ.t.G.hom = G.hom ≫ u ≫ pullback.fst _ _ := by
      rw [Category.assoc, Over.w, hβ.1.w]
    let f : G ⟶ G := Over.homMk (hβ.1.lift _ _ w) (hβ.1.lift_snd _ _ w)
    have hf : f.left ≫ β = β ≫ (Xo.univ.t.act.act (H.bar a)).left := hβ.1.lift_fst _ _ w
    haveI := Xo.univ.t.act.hom (H.bar a)
    haveI : IsMonHom f := GlobalTheory.SharpPull.isMonHom_lift hβ hβ hf
    obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.fractionField_of_isGrpPullback hs hs hGP hGP
      ((Over.pullback (spMap τ)).map f)
    refine ⟨F, hF, f, ExtUnique.hom_ext_of_dominant P.A.hom ?_ (pullback.fst G.hom (spMap τ)) ?_, hf⟩
    · rw [Category.assoc, Category.assoc, Over.w, hα.1.w, Over.w_assoc]
    · rw [← Category.assoc, ← ExtUnique.pullback_map_left_fst, Category.assoc]
      exact hF'.trans (Category.assoc _ _ _)
  choose act h₁ h₂ using key
  exact ⟨act, h₁, G, _, α, β, hα, hβ, hL, h₂⟩

theorem exists_local_spread : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (o₁ Ω : Type) [CommRing o₁] [Field Ω] [Algebra o₁ Ω] [ArithBase o₁ Ω] (M : RatModel o₁ Ω) (π : M.Z ⟶ C.Z) (uη : Sp Ω ⟶ Xo.XF c), GlobalTheory.IsNormalScheme M.Z → M.pt ≫ π = uη ≫ C.i → ∀ (A₁ : PolAV (Sp Ω)) (m : ℕ) (ze : o₁ˣ), IsUnit (m : o₁) → UOver Xo c A₁ (RingHom.id Ω) uη → Out.Level A₁ m (unitOn (Units.map (algebraMap o₁ Ω).toMonoidHom ze)) → ∀ (K : Type) [Field K] (yM : Sp K ⟶ M.Z) (y : Sp K ⟶ Xo.XF c), yM ≫ π = y ≫ C.i → ∃ (R : Subalgebra o₁ Ω) (P : PolAV (Sp R)) (act : 𝓞 E → (P.A ⟶ P.A)) (u : Sp (ratHull R) ⟶ Xo.XF c) (𝔭 : Ideal R), R.FG ∧ (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧ P.g = A₁.g ∧ HypS P.A P.L ∧ Nonempty (Out.Level P m (unitOn (Units.map (algebraMap o₁ R).toMonoidHom ze))) ∧ (∀ a, IsMonHom (act a)) ∧ GlobalTheory.UCovSep.UAct Xo c P act (toRat R) u ∧ spMap (ratHull R).val.toRingHom ≫ u = uη ∧ 𝔭.IsPrime ∧ ∀ a b : R, b ∉ 𝔭 → (a : Ω) / (b : Ω) ∈ M.O (yM (closedPoint K)) := by
  intro E _ _ _ H Dw _ l Xo c C o₁ Ω _ _ _ hb M π uη hM hπ A₁ m ze hm hU₁ lev K _ yM y hy
  haveI := hb.char
  haveI := hb.ded
  let w : M.Z := yM (closedPoint K)
  have hw : π w ∈ Set.range C.i := ⟨y (closedPoint K), (congrArg (fun χ : Sp K ⟶ C.Z => χ (closedPoint K)) hy).symm⟩
  obtain ⟨U₀, u₀, hw₀, hu₀⟩ := exists_chart C M π uη hπ w hw
  obtain ⟨U, hle, P₁, -, hU, hwU, hP₁⟩ := LocSpread.exists_model (isUnit_intCast C M π w hw) hw₀ u₀
  have hne : ((U : M.Z.Opens) : Set M.Z).Nonempty := ⟨w, hwU⟩
  let u : Sp (ratHull (M.ringOn U)) ⟶ Xo.XF c := spMap (Subalgebra.inclusion (ratHull_mono hle)).toRingHom ≫ u₀
  have hu : spMap (ratHull (M.ringOn U)).val.toRingHom ≫ u = uη := by
    rw [← hu₀, ← Category.assoc, ← Spec.map_comp]; rfl
  have gen : ∀ P : PolAV (Sp (M.ringOn U)), UOver Xo c P (toRat (M.ringOn U)) u →
      UOver Xo c P (M.ringOn U).val.toRingHom uη := fun P hP => by
    have := hP.comp (ratHull (M.ringOn U)).val.toRingHom
    rw [hu] at this
    exact this
  haveI := RatModel.isFractionRing_ringOn hU hne
  haveI := GlobalTheory.Poinc.TorsExtend.isIntegrallyClosed_ringOn M ((isNormalScheme_iff_pred _).1 hM) hU hne
  have fg : (M.ringOn U).FG := GlobalTheory.Poinc.fg_ringOn_of_isAffineOpen _ _ M U hU hne
  haveI : IsNoetherianRing (M.ringOn U) := isNoetherianRing_of_fg fg

  obtain ⟨Q, a, a', ha, ha', hL, hL'⟩ :=
    exists_common_baseChange_of_uOver E H Dw l Xo c Ω _ _ A₁ P₁ _ _ uη hU₁ (gen P₁ hP₁)
  have g₁ := GlobalTheory.polAV_g_eq_of_isGrpPullback Ω _ A₁ Q _ a ha
  have g₂ := GlobalTheory.polAV_g_eq_of_isGrpPullback Ω _ P₁ Q _ a' ha'
  obtain ⟨levQ, -⟩ := exists_level_baseChange GlobalTheory.abelianSchemeLaws_all.1 _ _ _ A₁ Q a ha hL g₁ _ _
    (unitOn (Units.map (algebraMap o₁ Ω).toMonoidHom ze)) (by rw [GSetup.map_unitOn']; rfl) lev.prim lev
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm.ne_zero Nat.cast_zero)
  obtain ⟨P, ψ, hg, hψ, hψL, hlev⟩ := GlobalTheory.SympLevelExt.level_extends P₁ (M.ringOn U) Ω (RingHom.id _) Q a' m
    (Units.map (algebraMap o₁ (M.ringOn U)).toMonoidHom ze) hm0
    (by simpa using hm.map (algebraMap o₁ (M.ringOn U))) g₂ ha' hL' ⟨levQ⟩
  have hP : UOver Xo c P (toRat (M.ringOn U)) u := (uOver_baseChange_iff hψ hψL _).2 hP₁

  obtain ⟨A₀, hS₀, hU₀⟩ := GSetup.exists_fibre Xo c uη
  obtain ⟨Q', b, b', hb₁, hb₂, hb₃, hb₄⟩ :=
    exists_common_baseChange_of_uOver E H Dw l Xo c Ω _ _ A₀ P _ _ uη hU₀ (gen P hP)
  have hS := GlobalTheory.Poinc.hypS_of_generic_ringOn o₁ Ω M U hU hne hM Ω A₀ P Q' _ b b' hb₁ hb₂ hb₃ hb₄ hS₀

  obtain ⟨act, hact, hA⟩ := exists_uAct (ratHull (M.ringOn U)).val.toRingHom Subtype.val_injective rfl hP
  let j : M.ringOn U →+* M.O w := (Subalgebra.inclusion (RatModel.ringOn_le_O hwU)).toRingHom
  refine ⟨M.ringOn U, P, act, u, (maximalIdeal (M.O w)).comap j, fg, fun x => ?_, hg.trans (g₂.symm.trans g₁), hS, hlev,
    hact, hA, hu, inferInstance, fun p q hq => ?_⟩
  · obtain ⟨p, q, -, e⟩ := RatModel.exists_eq_div hU hne x
    exact ⟨_, (RatModel.mem_ringOn_iff_exists hne).2 ⟨p, rfl⟩, _, (RatModel.mem_ringOn_iff_exists hne).2 ⟨q, rfl⟩, e⟩
  · have hq' : IsUnit (j q) := by
      by_contra h
      exact hq h
    rw [div_eq_mul_inv]
    exact mul_mem (j p).2 ((RatModel.isUnit_O_iff _).1 hq').2

end GlobalTheory.UCovSep.LocalSpread
