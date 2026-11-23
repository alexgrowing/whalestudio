import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjectiveLatticeCoordMapEquivariantDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndomorphismCharacterActionConjugateStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelOverOpenPartSubsetAbelianLocusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointCompletionPositiveResidueCharStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationPulledBackTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAdicCompletion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ArcGenericPointDescendsToPowerSeries
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianOfIsGrpPullbackSquare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc.TraitAtClosed

theorem exists_trait_lattice_map : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → ∀ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) → (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∃ β : T.t.G.left ⟶ out.G.left, IsGrpPullback T.t.G out.G ξ β ∧ LBIso T.t.PP.L (out.L.L.pull β) ∧ ∀ a, (T.t.act.act a).left ≫ β = β ≫ (f a).left) → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ out.G.left), IsGrpPullback G out.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (out.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus out.G)) → ∀ m : 𝓞 E → (D.toPre.X →+ D.toPre.X), (∀ a, ∃ fR : G ⟶ G, IsMonHom fR ∧ fR.left ≫ gm = gm ≫ (f a).left ∧ EndChar U fR (m a)) → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (h : T.V →+* V') (g' : R →+* V') (ρT : D.toPre.X →+ T.P.D.toPre.X), Function.Injective h ∧ Irreducible (h T.ϖ) ∧ spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ ∧ Function.Surjective ρT ∧ (∀ y r, PsiCoord D.toPre y r → 0 ≤ T.be (ρT y) (ρT y) ∧ Associated (g' r ^ 2) (h T.ϖ ^ (T.be (ρT y) (ρT y)).toNat)) ∧ ∀ a y, ρT (m a y) = H.bar a • ρT y := by
  intro E _ _ _ H Dw l Xo c C X₁ M U₀ EE out hAdm f hf hT x hx R _ _ _ j hR hj G _ _ gm hgm D A U hLB hPsi m hm T ξ hξ hsp
  obtain ⟨hft, hcpl⟩ := GlobalTheory.T.closedPoint_completion_positive_residueChar X₁.o₁ X₁.Ω₁ M x hx
  obtain ⟨-, p, hp, hpR⟩ := hcpl R j hj
  haveI := hft
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  haveI : CharZero T.V := T.cdvr.2.2
  let f₀ : M.Z.presheaf.stalk x →+* T.V := (M.Z.presheaf.stalkSpecializes hsp ≫ Scheme.stalkClosedPointTo ξ).hom
  have hf₀ : spMap f₀ ≫ M.Z.fromSpecStalk x = ξ := by
    have e : spMap f₀ = Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (M.Z.presheaf.stalkSpecializes hsp) := by
      simp only [f₀, spMap, CommRingCat.ofHom_hom, Spec.map_comp]
    rw [e, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  obtain ⟨V', _, _, _, h, g', hcomp, hinj, hloc, hgj, hirr⟩ :=
    GlobalTheory.TraitLift.exists_lift_of_isCpl (M.Z.presheaf.stalk x) R T.V j hj f₀
  have eq1 : spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ := by
    have e : spMap g' ≫ spMap j = spMap h ≫ spMap f₀ := by
      simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hgj]
    rw [← hf₀, ← Category.assoc, e, Category.assoc]
  haveI hch : CharZero V' := charZero_of_injective_ringHom hinj
  have hV' : GlobalTheory.Mum.Base V' := ⟨GlobalTheory.ArcPointDescent.admissibleBase_maximalIdeal_completeDVR ⟨inferInstance, hcomp, hch⟩, hch⟩
  obtain ⟨tW, mW, PW, e, he⟩ := GlobalTheory.T.exists_linear_uniformisation_pulled_back_trait E H Dw l Xo c T V' hV' inferInstance h hinj hloc
  obtain ⟨βT, hβT, hLT, hactT⟩ := hT T ξ hξ
  have hβ' : IsGrpPullback tW.G out.G (spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x)) (mW.φ ≫ βT) := by
    rw [eq1]; exact mW.cart.comp hβT
  have w : (mW.φ ≫ βT) ≫ out.G.hom = (tW.G.hom ≫ spMap g') ≫ (spMap j ≫ M.Z.fromSpecStalk x) := by
    rw [hβ'.1.w, Category.assoc]
  let β : tW.G.left ⟶ G.left := hgm.1.lift (mW.φ ≫ βT) (tW.G.hom ≫ spMap g') w
  have hβgm : β ≫ gm = mW.φ ≫ βT := hgm.1.lift_fst _ _ _
  have hβG : β ≫ G.hom = tW.G.hom ≫ spMap g' := hgm.1.lift_snd _ _ _
  have hβ : IsGrpPullback tW.G G (spMap g') β := hgm.cancel (by rw [hβgm]; exact hβ') hβG
  have hLBW : LBIso PW.U.LG.L (U.LG.L.pull β) := by
    rw [PW.bundle]
    exact LBIso.trans tW.PP.isLB (pull_isLB out.L.isLB _) (pull_isLB U.LG.isLB _)
      (LBIso.trans tW.PP.isLB (pull_isLB T.t.PP.isLB _) (pull_isLB out.L.isLB _)
        (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap mW) (GlobalTheory.LN.GenericPoint.lbIso_pull hLT mW.φ rfl))
      (GlobalTheory.LN.GenericPoint.lbIso_pull hLB β hβgm.symm).symm
  have hGs : IsSemiAbelian G := GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square _ _ _ out.G G gm hgm out.semi
  obtain ⟨hker, hU₀ab⟩ := GlobalTheory.T.kernel_over_openPart_subset_abelianLocus E H Dw l Xo c C X₁ M U₀ EE out hAdm T ξ hξ R
    (spMap j ≫ M.Z.fromSpecStalk x) V' h g' hinj eq1
  have hWo : IsOpen ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' (U₀ : Set M.Z)) :=
    U₀.isOpen.preimage (spMap j ≫ M.Z.fromSpecStalk x).continuous
  have hPsiW : ∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' (U₀ : Set M.Z)) :=
    fun y jj V hV hVU => hPsi y jj V hV (hVU.trans (Set.preimage_mono hU₀ab))
  obtain ⟨ρ, hρs, hρc, hρe⟩ := GlobalTheory.T.exists_surjective_lattice_coordMap_equivariant_dvr R hR G hGs D A U V' hV' inferInstance tW.G tW.semi PW.D PW.A PW.U g' β p hp
    hpR _ hWo hPsiW hker hβ hLBW
  refine ⟨V', inferInstance, inferInstance, inferInstance, h, g', e.toAddEquiv.toAddMonoidHom.comp ρ, hinj, hirr T.ϖ T.irr,
    eq1, e.surjective.comp hρs, ?_, ?_⟩
  · intro y r hr
    obtain ⟨h0, r', hr', hass⟩ := he (ρ y)
    exact ⟨h0, ((hρc y r r' hr hr').pow_pow (n := 2)).trans hass⟩
  · intro a y
    obtain ⟨fR, hfRmon, hfRgm, hfRchar⟩ := hm a
    have hcompat : (tW.act.act a).left ≫ β = β ≫ fR.left := by
      apply hgm.1.hom_ext
      · calc ((tW.act.act a).left ≫ β) ≫ gm = (tW.act.act a).left ≫ mW.φ ≫ βT := by rw [Category.assoc, hβgm]
          _ = mW.φ ≫ (T.t.act.act a).left ≫ βT := by rw [← Category.assoc, mW.act a, Category.assoc]
          _ = mW.φ ≫ βT ≫ (f a).left := by rw [hactT a]
          _ = (β ≫ fR.left) ≫ gm := by rw [Category.assoc, hfRgm, reassoc_of% hβgm]
      · rw [Category.assoc, hβG, Category.assoc, Over.w fR, hβG, ← Category.assoc, Over.w (tW.act.act a)]
    have key := hρe fR (tW.act.act a) hfRmon (tW.act.hom a) hcompat (m a) _ hfRchar (GlobalTheory.T.endomorphism_characterAction_conjugate E H V' hV' tW PW a) y
    show e (ρ (m a y)) = H.bar a • e (ρ y)
    rw [key]
    exact e.map_smul _ _

end GlobalTheory.UPoinc.TraitAtClosed
