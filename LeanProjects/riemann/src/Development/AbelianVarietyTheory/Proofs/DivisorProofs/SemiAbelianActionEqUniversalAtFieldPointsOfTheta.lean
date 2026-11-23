import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsActionPullbackUniversalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsoAbelianSchemeSemiAbelianOfCommonGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.ActField

theorem exists_factor_localRing : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (Y : RatModel o Ω) (K : Type) [Field K]
    (s : Sp K ⟶ Y.Z), ∃ (z : Y.Z) (j : Sp (Y.O z) ⟶ Y.Z) (s' : Sp K ⟶ Sp (Y.O z)),
      spMap (algebraMap (Y.O z) Ω) ≫ j = Y.pt ∧ s' ≫ j = s ∧ j (IsLocalRing.closedPoint (Y.O z)) = z ∧ ∀ w, s w = z := by
  intro o Ω _ _ _ Y K _ s
  have hsz : ∀ w, s w = s (IsLocalRing.closedPoint K) := fun w => by
    rw [Subsingleton.elim w (IsLocalRing.closedPoint K)]
  let z := s (IsLocalRing.closedPoint K)
  let e := Y.stalkEquiv z
  let E : Y.Z.presheaf.stalk z ⟶ CommRingCat.of (Y.O z) := CommRingCat.ofHom e.toRingHom
  let E' : CommRingCat.of (Y.O z) ⟶ Y.Z.presheaf.stalk z := CommRingCat.ofHom e.symm.toRingHom
  have hEE : E ≫ E' = 𝟙 _ := by ext a; exact e.symm_apply_apply a
  refine ⟨z, Spec.map E ≫ Y.Z.fromSpecStalk z, Spec.map (E' ≫ Scheme.stalkClosedPointTo s), ?_, ?_, ?_, hsz⟩
  · have h1 : E ≫ CommRingCat.ofHom (algebraMap (Y.O z) Ω) =
        Y.Z.presheaf.stalkSpecializes (Y.pt_specializes (IsLocalRing.closedPoint Ω) z) ≫
          Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) Y.pt := by
      ext a; rfl
    show Spec.map _ ≫ _ = _
    rw [← Category.assoc, ← Spec.map_comp, h1, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, hEE, Category.id_comp,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · haveI : IsLocalHom E.hom := ⟨fun a ha => by
      have h := ha.map e.symm.toRingHom
      have h' : e.symm.toRingHom (E.hom a) = a := e.symm_apply_apply a
      rwa [h'] at h⟩
    change Y.Z.fromSpecStalk z ((Spec.map E) (IsLocalRing.closedPoint (CommRingCat.of (Y.O z)))) = z
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

theorem exists_factor_i : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (O : Type) [CommRing O] [IsLocalRing O] (g : Sp O ⟶ C.Z),
      g (IsLocalRing.closedPoint O) ∈ Set.range C.i → ∃ v : Sp O ⟶ Xo.XF c, g = v ≫ C.i := by
  intro E _ _ _ H Dw l Xo c C O _ _ g hg
  letI := C.b.toAlgebra
  haveI := C.isFractionRing
  haveI := C.ded
  obtain ⟨x, hx⟩ := hg
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (g ≫ C.z)
  have hpt : (Spec.map φ) (IsLocalRing.closedPoint O) =
      (spMap C.b) ((pullback.snd C.z (spMap C.b)) (C.iF x)) := by
    rw [hφ]
    change C.z (g _) = _
    rw [← hx]
    change ((C.iF ≫ pullback.fst C.z (spMap C.b)) ≫ C.z) x = ((C.iF ≫ pullback.snd C.z (spMap C.b)) ≫ spMap C.b) x
    rw [Category.assoc, pullback.condition, Category.assoc]
  have hbot : Ideal.comap φ.hom (IsLocalRing.maximalIdeal O) = ⊥ := by
    have hc := congrArg PrimeSpectrum.asIdeal hpt
    change Ideal.comap φ.hom (IsLocalRing.maximalIdeal O) = Ideal.comap C.b _ at hc
    haveI := ((pullback.snd C.z (spMap C.b)) (C.iF x)).isPrime
    rw [hc, Ideal.eq_bot_of_prime ((pullback.snd C.z (spMap C.b)) (C.iF x)).asIdeal]
    exact Ideal.comap_bot_of_injective _ C.inj
  have hunit : ∀ y : nonZeroDivisors C.o, IsUnit (φ.hom y) := fun y => by
    by_contra hy
    have hm : (y : C.o) ∈ Ideal.comap φ.hom (IsLocalRing.maximalIdeal O) := (IsLocalRing.mem_maximalIdeal _).2 hy
    rw [hbot, Ideal.mem_bot] at hm
    exact nonZeroDivisors.ne_zero y.2 hm
  let ψF : c.F →+* O := IsLocalization.lift (M := nonZeroDivisors C.o) (S := c.F) hunit
  have hψF : ψF.comp C.b = φ.hom := IsLocalization.lift_comp hunit
  have w : g ≫ C.z = Spec.map (CommRingCat.ofHom ψF) ≫ spMap C.b := by
    rw [← hφ]
    show _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact (RingHom.congr_fun hψF a).symm
  let g' : Sp O ⟶ pullback C.z (spMap C.b) := pullback.lift g _ w
  have hg'1 : g' ≫ pullback.fst _ _ = g := pullback.lift_fst _ _ _
  haveI : IsPreimmersion (spMap C.b) := IsPreimmersion.of_isLocalization (nonZeroDivisors C.o)
  have hinj : Function.Injective (pullback.fst C.z (spMap C.b)) := (pullback.fst C.z (spMap C.b)).isEmbedding.injective
  have hcl : g' (IsLocalRing.closedPoint O) ∈ Set.range C.iF := ⟨x, hinj (by
    change (C.iF ≫ pullback.fst _ _) x = (g' ≫ pullback.fst _ _) _
    rw [hg'1]; exact hx)⟩
  have hrange : Set.range g' ⊆ Set.range C.iF := by
    haveI := C.iF_open
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint p).map g'.continuous).mem_open C.iF.isOpenEmbedding.isOpen_range hcl
  haveI := C.iF_open
  refine ⟨IsOpenImmersion.lift C.iF g' hrange, ?_⟩
  rw [← Category.assoc, IsOpenImmersion.lift_fac, hg'1]

theorem isNoetherianRing_O : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] (Y : RatModel o Ω)
    (z : Y.Z), IsNoetherianRing (Y.O z) := by
  intro o Ω _ _ _ _ Y z
  haveI := Y.lft
  haveI : IsLocallyNoetherian Y.Z := LocallyOfFiniteType.isLocallyNoetherian Y.s
  exact isNoetherianRing_of_ringEquiv _ (Y.stalkEquiv z)

set_option maxHeartbeats 4000000 in

theorem exists_action_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∀ wi : UWit X₁, ∃ (f : 𝓞 E → (out.G ⟶ out.G)) (ψ : wi.G.left ⟶ out.G.left), (∀ a, IsMonHom (f a)) ∧ IsGrpPullback wi.G out.G Y.pt ψ ∧ (∀ (T : Scheme.{0}) (w : T ⟶ wi.G.left), ∃ x' : T ⟶ pullback X₁.ρ.P.A.hom out.u₀, x' ≫ out.φ = w ≫ ψ ∧ x' ≫ pullback.fst _ _ = w ≫ wi.α) ∧ (∀ (a : 𝓞 E) (e : wi.G ⟶ wi.G), e.left ≫ wi.β = wi.β ≫ (Xo.univ.t.act.act a).left → e.left ≫ ψ = ψ ≫ (f a).left) ∧ ∀ (K : Type) [Field K] (s : Sp K ⟶ Y.Z) (y : Sp K ⟶ Xo.XF c), s ≫ r = y ≫ C.i → ∀ (tK : SAB H (Sp K)), Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∃ γ : tK.G.left ⟶ out.G.left, IsGrpPullback tK.G out.G s γ ∧ LBIso tK.PP.L (out.L.L.pull γ) ∧ ∀ a, (tK.act.act a).left ≫ γ = γ ≫ (f a).left := by
  intro E _ _ _ H Dw l Xo c C X₁ Y U₀ EE out r hO hr wi

  have hrange : Set.range Y.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact Y.top_le_preimage_pt hO.ne (x := w) trivial
  let xU : Sp X₁.Ω₁ ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι Y.pt hrange
  have hxU : xU ≫ U₀.ι = Y.pt := IsOpenImmersion.lift_fac _ _ _
  have hu₀ : xU ≫ out.u₀ = spMap X₁.S.R.val.toRingHom := out.u₀_gen xU hxU
  have wℓ : wi.α ≫ X₁.ρ.P.A.hom = (wi.G.hom ≫ xU) ≫ out.u₀ := by
    rw [Category.assoc, hu₀]; exact wi.hα.1.w
  let ℓ : wi.G.left ⟶ pullback X₁.ρ.P.A.hom out.u₀ := pullback.lift wi.α (wi.G.hom ≫ xU) wℓ
  have hℓα : ℓ ≫ pullback.fst _ _ = wi.α := pullback.lift_fst _ _ _
  have hℓ : IsGrpPullback wi.G ((Over.pullback out.u₀).obj X₁.ρ.P.A) xU ℓ :=
    (isGrpPullback_pullback X₁.ρ.P.A out.u₀).cancel (wi.hα.congr hu₀.symm hℓα.symm)
      (pullback.lift_snd _ _ _)
  let ψ : wi.G.left ⟶ out.G.left := ℓ ≫ out.φ
  have hψ : IsGrpPullback wi.G out.G Y.pt ψ := (hℓ.comp out.cart).congr hxU rfl

  obtain ⟨f₀, hf₀, -⟩ := GlobalTheory.T.exists_action_pullback_universalUnitary E H Dw l Xo c (Sp X₁.Ω₁) X₁.uΩ wi.G wi.β wi.hβ
  obtain ⟨e, he, heψ⟩ := grpPullback_iso hψ (isGrpPullback_pullback out.G Y.pt)
  haveI := he
  have hf' : ∀ a, IsMonHom (e.inv ≫ f₀ a ≫ e.hom) := fun a => by
    haveI := (hf₀ a).1
    infer_instance
  have hF : ∀ a, ∃ F : out.G ⟶ out.G, IsMonHom F ∧ (Over.pullback Y.pt).map F = e.inv ≫ f₀ a ≫ e.hom :=
    fun a => (out.endo _ (hf' a)).exists
  choose F hFm hFe using hF
  have hmap : ∀ {S' : Scheme.{0}} (q : S' ⟶ Y.Z) (a : 𝓞 E),
      ((Over.pullback q).map (F a)).left ≫ pullback.fst out.G.hom q = pullback.fst out.G.hom q ≫ (F a).left :=
    fun q a => pullback.lift_fst _ _ _
  have hei : e.hom.left ≫ e.inv.left = 𝟙 _ := by rw [← Over.comp_left, e.hom_inv_id, Over.id_left]
  have gen₀ : ∀ a, (f₀ a).left ≫ ψ = ψ ≫ (F a).left := fun a => by
    have key : e.hom.left ≫ ((Over.pullback Y.pt).map (F a)).left = (f₀ a).left ≫ e.hom.left := by
      rw [hFe a, Over.comp_left, Over.comp_left, ← Category.assoc, hei, Category.id_comp]
    calc (f₀ a).left ≫ ψ = ((f₀ a).left ≫ e.hom.left) ≫ pullback.fst _ _ := by rw [← heψ, Category.assoc]
      _ = (e.hom.left ≫ ((Over.pullback Y.pt).map (F a)).left) ≫ pullback.fst _ _ := by rw [key]
      _ = ψ ≫ (F a).left := by rw [Category.assoc, hmap, ← Category.assoc, heψ]
  have uniq : ∀ (a : 𝓞 E) (e' : wi.G ⟶ wi.G), e'.left ≫ wi.β = wi.β ≫ (Xo.univ.t.act.act a).left → e' = f₀ a :=
    fun a e' h => Over.OverMorphism.ext (wi.hβ.1.hom_ext (h.trans (hf₀ a).2.symm) (by rw [Over.w, Over.w]))
  refine ⟨F, ψ, hFm, hψ, fun T w => ⟨w ≫ ℓ, Category.assoc _ _ _, by rw [Category.assoc, hℓα]⟩,
    fun a e' h => (uniq a e' h) ▸ gen₀ a, ?_⟩

  intro K _ s y hsy tK ⟨mm⟩
  haveI : IsNoetherianRing X₁.o₁ := by haveI := X₁.ar.ded; infer_instance
  obtain ⟨z₀, j, s', hj, hs', hjz, hsz⟩ := exists_factor_localRing _ _ Y K s
  haveI := isNoetherianRing_O _ _ Y z₀
  haveI := RatModel.isIntegrallyClosed_O hO.normal z₀
  have hpt : (j ≫ r) (IsLocalRing.closedPoint (Y.O z₀)) = C.i (y (IsLocalRing.closedPoint K)) := by
    change r (j (IsLocalRing.closedPoint (Y.O z₀))) = _
    rw [hjz, ← hsz (IsLocalRing.closedPoint K)]
    change (s ≫ r) _ = (y ≫ C.i) _
    rw [hsy]
  obtain ⟨v, hv⟩ := exists_factor_i E H Dw l Xo c C (Y.O z₀) (j ≫ r) ⟨_, hpt.symm⟩
  haveI := C.isPreimmersion_i
  have hsv : s' ≫ v = y := (cancel_mono C.i).1 (by rw [Category.assoc, ← hv, ← Category.assoc, hs', hsy])
  have hgv : spMap (algebraMap (Y.O z₀) X₁.Ω₁) ≫ v = X₁.uΩ :=
    (cancel_mono C.i).1 (by rw [Category.assoc, ← hv, ← Category.assoc, hj, hr])
  haveI : IsCommMonObj ((Over.pullback j).obj out.G) := Functor.isCommMonObj_obj
  have hAb : IsAbelianScheme ((Over.pullback (v ≫ pullback.fst _ _)).obj Xo.univ.t.G) :=
    PolPull.isAbelianScheme_of_isGrpPullback (Obj.toPolAV Xo.univ).isAb (isGrpPullback_pullback _ _)
  have hSe := IsSemiAbelian.pullback j out.G out.semi
  have wa : wi.β ≫ Xo.univ.t.G.hom = (wi.G.hom ≫ spMap (algebraMap (Y.O z₀) X₁.Ω₁)) ≫ v ≫ pullback.fst _ _ := by
    rw [wi.hβ.1.w, ← hgv]; simp only [Category.assoc]
  let aa := pullback.lift _ _ wa
  have haa : aa ≫ pullback.fst _ _ = wi.β := pullback.lift_fst _ _ _
  have ha : IsGrpPullback wi.G ((Over.pullback (v ≫ pullback.fst _ _)).obj Xo.univ.t.G)
      (spMap (algebraMap (Y.O z₀) X₁.Ω₁)) aa :=
    (isGrpPullback_pullback Xo.univ.t.G _).cancel (wi.hβ.congr (by rw [← hgv, Category.assoc]) haa.symm)
      (pullback.lift_snd _ _ _)
  have wg : ψ ≫ out.G.hom = (wi.G.hom ≫ spMap (algebraMap (Y.O z₀) X₁.Ω₁)) ≫ j := by
    rw [hψ.1.w, Category.assoc, hj]
  let gg := pullback.lift _ _ wg
  have hgg : gg ≫ pullback.fst _ _ = ψ := pullback.lift_fst _ _ _
  have hg : IsGrpPullback wi.G ((Over.pullback j).obj out.G) (spMap (algebraMap (Y.O z₀) X₁.Ω₁)) gg :=
    (isGrpPullback_pullback out.G j).cancel (hψ.congr hj.symm hgg.symm) (pullback.lift_snd _ _ _)
  obtain ⟨i, hi, hai, hLi, hEi⟩ := GlobalTheory.T.iso_abelianScheme_semiAbelian_of_common_genericFibre (Y.O z₀) _ ((Over.pullback j).obj out.G) hAb hSe X₁.Ω₁ wi.G aa gg ha hg
  haveI := hi
  obtain ⟨f₁, hf₁, hT⟩ := GlobalTheory.T.exists_action_pullback_universalUnitary E H Dw l Xo c (Sp (Y.O z₀)) v ((Over.pullback (v ≫ pullback.fst _ _)).obj Xo.univ.t.G) (pullback.fst _ _)
    (isGrpPullback_pullback Xo.univ.t.G (v ≫ pullback.fst _ _))
  have mm' : SABMap tK Xo.univ.t ((s' ≫ v) ≫ pullback.fst _ _) := hsv ▸ mm
  obtain ⟨γ₀, hγ₀, -, hLγ, hactγ⟩ := hT (Sp K) s' tK mm'
  refine ⟨γ₀ ≫ i.hom.left ≫ pullback.fst out.G.hom j, ?_, ?_, ?_⟩
  · exact (hγ₀.comp ((isGrpPullback_of_iso i).comp (isGrpPullback_pullback out.G j))).congr
      (by rw [Category.id_comp, hs']) rfl
  · have hU := Xo.univ.t.PP.isLB
    have hP := X₁.ρ.P.isLB
    have hOL := out.L.isLB
    have sA : LBIso (X₁.ρ.P.L.pull wi.α) (out.L.L.pull ψ) :=
      GenSpread.lbIso_pull_comp ℓ hℓα.symm rfl (LBIso.symm ⟨out.w, out.w_gen⟩)
    have sB : LBIso (Xo.univ.t.PP.L.pull wi.β) (out.L.L.pull ψ) :=
      LBIso.trans (pull_isLB hU _) (pull_isLB hP _) (pull_isLB hOL _) wi.hL.symm sA
    have sC : LBIso ((Xo.univ.t.PP.L.pull (pullback.fst _ _)).pull aa)
        ((out.L.L.pull (pullback.fst out.G.hom j)).pull gg) :=
      LBIso.trans (pull_isLB (pull_isLB hU _) _) (pull_isLB hU _) (pull_isLB (pull_isLB hOL _) _)
        (GenSpread.lbIso_pull_pull hU aa haa.symm).symm
        (LBIso.trans (pull_isLB hU _) (pull_isLB hOL _) (pull_isLB (pull_isLB hOL _) _) sB
          (GenSpread.lbIso_pull_pull hOL gg hgg.symm))
    have sD := hLi _ _ (pull_isLB hU _) (pull_isLB hOL _) sC
    exact LBIso.trans tK.PP.isLB (pull_isLB (pull_isLB hU _) _) (pull_isLB hOL _) hLγ
      (LBIso.trans (pull_isLB (pull_isLB hU _) _) (pull_isLB (pull_isLB (pull_isLB hOL _) _) _) (pull_isLB hOL _)
        (GenSpread.lbIso_pullback sD γ₀)
        (LBIso.trans (pull_isLB (pull_isLB (pull_isLB hOL _) _) _) (pull_isLB (pull_isLB hOL _) _) (pull_isLB hOL _)
          (GenSpread.lbIso_pull_pull (pull_isLB hOL _) γ₀ rfl).symm
          (GenSpread.lbIso_pull_pull hOL (γ₀ ≫ i.hom.left) (Category.assoc _ _ _).symm).symm))
  · intro a
    have h1 : (f₀ a).left ≫ aa = aa ≫ (f₁ a).left := by
      apply pullback.hom_ext
      · rw [Category.assoc, haa, Category.assoc, (hf₁ a).2, ← Category.assoc, haa, (hf₀ a).2]
      · have w1 := Over.w (f₁ a)
        have w0 := Over.w (f₀ a)
        erw [Category.assoc, pullback.lift_snd, Category.assoc, w1, pullback.lift_snd, ← Category.assoc, w0]
    have h2 : (f₀ a).left ≫ gg = gg ≫ ((Over.pullback j).map (F a)).left := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hmap, hgg, ← Category.assoc gg, hgg, gen₀]
      · have w1 := Over.w ((Over.pullback j).map (F a))
        have w0 := Over.w (f₀ a)
        erw [Category.assoc, pullback.lift_snd, Category.assoc, w1, pullback.lift_snd, ← Category.assoc, w0]
    have h3 := congrArg Over.Hom.left (hEi (f₁ a) ((Over.pullback j).map (F a)) (f₀ a) h1 h2)
    rw [Over.comp_left, Over.comp_left] at h3
    rw [← Category.assoc, hactγ a]
    simp only [Category.assoc]
    rw [← Category.assoc (f₁ a).left, h3, Category.assoc, hmap]

end GlobalTheory.UPoinc.ActField
