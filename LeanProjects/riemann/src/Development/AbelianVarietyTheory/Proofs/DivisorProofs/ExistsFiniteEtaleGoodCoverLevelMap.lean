import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.EvNatPf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePointsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyModuliOfLevelDvd
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GaloisCoverDescentAndCartesianSquares
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliRepOfBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfBaseEq
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ExistsNotIntegralLie
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverGood

theorem hom_spQ_ext {X : Scheme.{0}} (f g : X ⟶ Sp ℚ) : f = g := by
  have key : ∀ h : X ⟶ Sp ℚ, h = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ h.appTop) := by
    intro h
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [key f, key g]
  congr 2
  ext1
  exact RingHom.ext_rat _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}

theorem exists_objMap_lower' {l l₂ : Level H} {B B' : Type} [CommRing B] [CommRing B'] {b : Base l B}
    {b' : Base l B'} {b₂ : Base l₂ B} {S S₂ T : Scheme.{0}}
    {s : S ⟶ Sp B'} {s₂ : S₂ ⟶ Sp B} {t : T ⟶ Sp B} {o : Obj Dw l b' s} {o₂ : Obj Dw l₂ b₂ s₂} {o' : Obj Dw l₂ b₂ t}
    (h : l.Dvd l₂) (hρ : b.ρ = b₂.ρ) (hζ : b.ζ = b₂.ζ ^ (l₂.A / l.A)) {π : S₂ ⟶ S} (m : SABMap o₂.t o.t π)
    (h₁ : ∀ a, (o₂.eta a ^ (l₂.M / l.M)).left ≫ m.φ = π ≫ (o.eta a).left)
    (h₂ : ∀ a, (o₂.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = π ≫ (o.etaA a).left)
    {g : T ⟶ S₂} (u : ObjMap o' o₂ g) :
    Nonempty (ObjMap (GlobalTheory.ObjLower.lower o' h hρ hζ) o (g ≫ π)) := by
  obtain ⟨n, hn⟩ := GlobalTheory.ObjMaps.exists_sab_comp m u.toSABMap
  have hn' : n.cm.F = u.cm.F ≫ m.cm.F := hn
  refine ⟨⟨n, fun a => ?_, fun a => ?_⟩⟩
  · change (o'.eta a ^ (l₂.M / l.M)).left ≫ n.cm.F = _
    rw [hn']
    refine GlobalTheory.ObjComp.sec_comp (h₁ a) ?_
    rw [← GlobalTheory.ObjLower.map_nsmul_of_add _ o'.eta_add, ← GlobalTheory.ObjLower.map_nsmul_of_add _ o₂.eta_add]
    exact u.eta _
  · change (o'.etaA a ^ (l₂.A / l.A)).left ≫ n.cm.F = _
    rw [hn']
    refine GlobalTheory.ObjComp.sec_comp (h₂ a) ?_
    rw [← GlobalTheory.ObjLower.map_nsmul_of_add _ o'.etaA_add, ← GlobalTheory.ObjLower.map_nsmul_of_add _ o₂.etaA_add]
    exact u.etaA _

theorem eq_of_levelMaps {l l₂ : Level H} {Xo : Moduli Dw l} {Xo₂ : Moduli Dw l₂} (hd : l.Dvd l₂)
    (jK : KA l →+* KA l₂) (hjK : ∀ x, ((jK x : KA l₂) : ℂ) = ((x : KA l) : ℂ))
    {r r' : Xo₂.X ⟶ Xo.X} (m : SABMap Xo₂.univ.t Xo.univ.t r) (m' : SABMap Xo₂.univ.t Xo.univ.t r')
    (he : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m.φ = r ≫ (Xo.univ.eta a).left)
    (heA : ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m.φ = r ≫ (Xo.univ.etaA a).left)
    (he' : ∀ a, (Xo₂.univ.eta a ^ (l₂.M / l.M)).left ≫ m'.φ = r' ≫ (Xo.univ.eta a).left)
    (heA' : ∀ a, (Xo₂.univ.etaA a ^ (l₂.A / l.A)).left ≫ m'.φ = r' ≫ (Xo.univ.etaA a).left)
    {T : Scheme.{0}} [IsReduced T] (iU : T ⟶ Xo₂.X) (h : iU ≫ r ≫ Xo.s = iU ≫ Xo₂.s ≫ spMap jK)
    (h' : iU ≫ r' ≫ Xo.s = iU ≫ Xo₂.s ≫ spMap jK) : iU ≫ r = iU ≫ r' := by
  have hA : l.A ∣ l₂.A := hd.2.2
  obtain ⟨o', ⟨u⟩⟩ := GlobalTheory.obj_pull E H Dw l₂ (KA l₂) (KA l₂) (baseKA l₂) (baseKA l₂) (RingHom.id _) Xo₂.X T Xo₂.s
    (iU ≫ Xo₂.s) iU rfl rfl (by simp [spMap]) Xo₂.univ
  obtain ⟨w⟩ := exists_objMap_lower' hd (GlobalTheory.baseOfFinerLevel_rho hA) (GlobalTheory.baseOfFinerLevel_zeta hA)
    (o := Xo.univ) m he heA u
  obtain ⟨w'⟩ := exists_objMap_lower' hd (GlobalTheory.baseOfFinerLevel_rho hA) (GlobalTheory.baseOfFinerLevel_zeta hA)
    (o := Xo.univ) m' he' heA' u
  have hρ : jK (baseKA l).ρ = (GlobalTheory.baseOfFinerLevel hA).ρ :=
    Subtype.ext ((hjK _).trans ((GlobalTheory.coe_baseKA_rho l).trans (GlobalTheory.coe_baseKA_rho l₂).symm))
  have hζ : jK (baseKA l).ζ = (GlobalTheory.baseOfFinerLevel hA).ζ :=
    Subtype.ext ((hjK _).trans (GlobalTheory.coe_levelFieldIncl hA _).symm)
  have hu := GlobalTheory.moduli_rep_of_base GlobalTheory.ObjMaps.id_comp_cancel E H Dw l Xo (KA l₂) (GlobalTheory.baseOfFinerLevel hA) jK T
    (iU ≫ Xo₂.s) (GlobalTheory.ObjLower.lower o' hd (GlobalTheory.baseOfFinerLevel_rho hA) (GlobalTheory.baseOfFinerLevel_zeta hA))
    inferInstance hρ hζ
  exact hu.unique ⟨by rw [Category.assoc, h, Category.assoc], ⟨w⟩⟩ ⟨by rw [Category.assoc, h', Category.assoc], ⟨w'⟩⟩

theorem formallyUnramified_spQ (l : Level H) : FormallyUnramified (spMap (algebraMap ℚ (KA l))) := by
  rw [HasRingHomProperty.Spec_iff (P := @FormallyUnramified)]
  have := GlobalTheory.LevelUp.finiteDimensional_KA l
  exact Algebra.FormallyUnramified.of_isSeparable ℚ (KA l)

theorem locallyOfFiniteType_spQ (l : Level H) : LocallyOfFiniteType (spMap (algebraMap ℚ (KA l))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  have := GlobalTheory.LevelUp.finiteDimensional_KA l
  exact RingHom.finiteType_algebraMap.mpr inferInstance

end GlobalTheory.CoverGood

theorem GlobalTheory.CoverGood.exists_good_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (d : DeltaDat Xo c 0), 1 ≤ Dw.p + Dw.q → d.IsLev →
    ∃ (Z : Scheme.{0}) (π : Z ⟶ Xo.XF c) (z₂ : Z ⟶ d.Xo₂.X), IsFinite π ∧ Etale π ∧ Surjective π ∧
      z₂ ≫ d.r = π ≫ pullback.fst _ _ ∧
      z₂ ≫ d.Xo₂.s = π ≫ pullback.snd _ _ ≫
        spMap ((d.eF.symm : d.c₂.F →+* c.F).comp (IntermediateField.inclusion d.c₂.le).toRingHom) := by
  intro E _ _ _ H Dw l Xo c d hpq hl
  obtain ⟨hdvd, hM, -, -, -, ⟨he, heA⟩, hlift, -, -⟩ := hl
  obtain ⟨r₀, jK, m₀, hjK, hr₀s, he₀, heA₀, -, hrF⟩ := (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.2 E H Dw hpq).1 l d.l₂ Xo d.Xo₂ hdvd
  obtain ⟨rF, h₁, h₂, hfin, het, -, -⟩ := hrF c d.c₂ d.hF.symm
  have hdiv : d.l₂.M / l.M = d.pd := by
    rw [hM]; exact Nat.mul_div_cancel_left _ (by have := l.three_le; omega)
  rw [← hdiv] at he

  have hab : (d.r ≫ Xo.s) ≫ spMap (algebraMap ℚ (KA l)) = (d.Xo₂.s ≫ spMap jK) ≫ spMap (algebraMap ℚ (KA l)) :=
    GlobalTheory.CoverGood.hom_spQ_ext _ _
  have := GlobalTheory.CoverGood.formallyUnramified_spQ l
  have := GlobalTheory.CoverGood.locallyOfFiniteType_spQ l
  have hop : IsOpenImmersion (equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK)) :=
    GlobalTheory.isOpenImmersion_equalizer_ι_of_unramified _ hab
  have hcl : IsClosedImmersion (equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK)) :=
    GlobalTheory.isClosedImmersion_equalizer_ι_of_isSeparated _ hab
  have hred₂ : IsReduced d.Xo₂.X := by
    haveI := d.Xo₂.smooth
    exact (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ d.Xo₂.s
      (SmoothOfRelativeDimension.smooth Dw.dim d.Xo₂.s)).1
  have hredU : IsReduced (equalizer (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK)) :=
    isReduced_of_isOpenImmersion (equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK))
  have hagree : equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK) ≫ d.r =
      equalizer.ι (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK) ≫ r₀ :=
    GlobalTheory.CoverGood.eq_of_levelMaps hdvd jK hjK d.m m₀ he heA he₀ heA₀ _
      (equalizer.condition (d.r ≫ Xo.s) (d.Xo₂.s ≫ spMap jK))
      (by rw [hr₀s])

  obtain ⟨U, iU, hop', hcl', hagree', hlU⟩ : ∃ (U : Scheme.{0}) (iU : U ⟶ d.Xo₂.X), IsOpenImmersion iU ∧
      IsClosedImmersion iU ∧ iU ≫ d.r = iU ≫ r₀ ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ d.Xo₂.X),
        x ≫ d.r ≫ Xo.s = x ≫ d.Xo₂.s ≫ spMap jK → ∃ u : Sp K ⟶ U, u ≫ iU = x :=
    ⟨_, _, hop, hcl, hagree, fun K _ x hx =>
      ⟨equalizer.lift x (by simpa only [Category.assoc] using hx), equalizer.lift_ι _ _⟩⟩
  clear hop hcl hagree hredU
  haveI := hop'; haveI := hcl'; haveI := hfin; haveI := het
  have hsp : spMap (IntermediateField.inclusion d.hF.symm.le).toRingHom ≫
      spMap ((d.eF.symm : d.c₂.F →+* c.F).comp (IntermediateField.inclusion d.c₂.le).toRingHom) =
      spMap (IntermediateField.inclusion d.c₂.le).toRingHom := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  refine ⟨pullback iU (pullback.fst d.Xo₂.s (spMap (IntermediateField.inclusion d.c₂.le).toRingHom)),
    pullback.snd _ _ ≫ rF, pullback.fst _ _ ≫ iU, inferInstance, inferInstance, ?_, ?_, ?_⟩
  · refine ⟨fun x => ?_⟩
    obtain ⟨K, _, _, j, ⟨k0, hk0⟩⟩ := GlobalTheory.ZM.IsGaloisCover.exists_algClosed_point (Xo.XF c) x
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (j ≫ pullback.snd _ _ : Sp K ⟶ Sp c.F)
    letI : Algebra c.F K := φ.hom.toAlgebra
    letI : Algebra d.c₂.F K := ((algebraMap c.F K).comp (d.eF.symm : d.c₂.F →+* c.F)).toAlgebra
    have hk : ∀ a : c.F, algebraMap d.c₂.F K (d.eF a) = algebraMap c.F K a := fun a => by
      show algebraMap c.F K (d.eF.symm (d.eF a)) = _
      rw [AlgEquiv.symm_apply_apply]
    have hjs : j ≫ pullback.snd _ _ = spMap (algebraMap c.F K) := hφ.symm
    have hx₀ : (j ≫ pullback.fst _ _) ≫ Xo.s = sOf c K := by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hjs, sOf, spMap, spMap, ← Spec.map_comp]
      rfl
    obtain ⟨y, hy⟩ := GlobalTheory.NonIntegralFrameExample.exists_framed _ hx₀
    obtain ⟨y₂, hy₂⟩ := hlift K hk y
    have hyr : y₂.x ≫ d.r = y.x := hy₂.1
    have hgood : y₂.x ≫ d.r ≫ Xo.s = y₂.x ≫ d.Xo₂.s ≫ spMap jK := by
      rw [reassoc_of% hyr, y.x_over, reassoc_of% y₂.x_over, sOf, sOf]
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext t
      show algebraMap c.F K (IntermediateField.inclusion c.le t) =
        algebraMap c.F K (d.eF.symm (IntermediateField.inclusion d.c₂.le (jK t)))
      exact congrArg (algebraMap c.F K) (Subtype.ext (hjK t).symm)
    obtain ⟨u, hu⟩ := hlU K y₂.x hgood
    have hw : y₂.x ≫ d.Xo₂.s =
        spMap (algebraMap d.c₂.F K) ≫ spMap (IntermediateField.inclusion d.c₂.le).toRingHom := by
      rw [y₂.x_over, sOf, spMap, spMap, spMap, ← Spec.map_comp]
      rfl
    have hr₀ : y₂.x ≫ r₀ = y.x := by
      rw [← hu, Category.assoc, ← hagree', ← Category.assoc, hu, hyr]
    obtain ⟨w, hw₁, hw₂⟩ : ∃ w : Sp K ⟶ d.Xo₂.XF d.c₂, w ≫ pullback.fst _ _ = y₂.x ∧
        w ≫ pullback.snd _ _ = spMap (algebraMap d.c₂.F K) :=
      ⟨pullback.lift _ _ hw, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    obtain ⟨z, hz⟩ : ∃ z : Sp K ⟶ pullback iU (pullback.fst d.Xo₂.s
        (spMap (IntermediateField.inclusion d.c₂.le).toRingHom)), z ≫ pullback.snd _ _ = w :=
      ⟨pullback.lift u w (by rw [hu, hw₁]), pullback.lift_snd _ _ _⟩
    have e : z ≫ pullback.snd _ _ ≫ rF = j := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, h₁, reassoc_of% hz, reassoc_of% hw₁, hr₀, hy]
      · rw [Category.assoc, Category.assoc, h₂, reassoc_of% hz, reassoc_of% hw₂, hjs, spMap, spMap,
          spMap, ← Spec.map_comp]
        rfl
    exact ⟨z k0, by rw [← Scheme.Hom.comp_apply, e, hk0]⟩
  · simp only [Category.assoc]
    rw [hagree', h₁, pullback.condition_assoc]
  · simp only [Category.assoc]
    rw [pullback.condition_assoc, reassoc_of% h₂, hsp, pullback.condition]
