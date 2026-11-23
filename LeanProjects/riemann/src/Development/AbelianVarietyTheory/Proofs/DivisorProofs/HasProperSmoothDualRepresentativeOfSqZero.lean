import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThickId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveLineBundleFamilyOfGeometricFibresStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentingSchemeOfFiniteSurjectiveLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianStructureCohomologyStatementStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveClassDegreeTwoStructureSheafVanishStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegreeTwoExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveClassDegreeTwoVanishAffineBasesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatCoefficientExtensionH2ClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleCorrectionSquareZeroIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallAffineBasisAndTransitionUnitsLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftOfStrictCocycleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeRelationOfPullbackIsoThickeningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartSmoothLiftSqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyReductionLiftsLineBundleStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBLift

section
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.Obs

theorem abLift_of_prim (hP : PrimitiveExtendedDegTwoVanish) : AbLift := by
  intro R _ I hI A _ g hA hg X₀ Y₀ i i' ψ₀ ψ₁ ψ₂ hi hi' e₀ e₁ e₂ c hc
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨hB, ⟨u, hu⟩, hall⟩ := GlobalTheory.T.small_affine_basis_and_transition_units_lift R I hI _ _ A.hom i L hi hL
  obtain ⟨hun, hdef, hnear⟩ := hall u hu
  obtain ⟨T, _, _, H, K₀, K₁, K₂, le₀, le₁, le₂, v, hH, hv, hrel⟩ := GlobalTheory.T.multiplicative_relation_of_pullback_iso_thickening R I hI _ _ _ _ A.hom (A ⊗ A).hom i i'
    _ _ _ (overW μ[A]) (overW (fst A A)) (overW (snd A A)) ψ₀ ψ₁ ψ₂ L hL u hi' hB hu e₀ e₁ e₂ hc
  obtain ⟨R₁, _, _, q, hq, hprim⟩ := GlobalTheory.T.flat_coefficient_extension_H2_class R I
  haveI : Smooth A.hom := SmoothOfRelativeDimension.smooth g _
  haveI : Smooth (A ⊗ A).hom := by
    rw [← Over.w (fst A A)]
    haveI : Smooth (fst A A).left := inferInstanceAs (Smooth (pullback.fst A.hom A.hom))
    infer_instance
  have hpi := hprim _ _ _ _ (pullMap (overW μ[A]) _ H K₀ le₀) (pullMap (overW (fst A A)) _ H K₁ le₁)
    (pullMap (overW (snd A A)) _ H K₂ le₂)
    (fun t ↦ haveI := GlobalTheory.LiftSys.smooth_sec_affine A.hom ((smallG i L).obj t).unop
      inferInstanceAs (Module.Flat R (Sec A.hom ((smallG i L).obj t).unop.1)))
    (fun t ↦ haveI := GlobalTheory.LiftSys.smooth_sec_affine (A ⊗ A).hom (H.obj t).unop
      inferInstanceAs (Module.Flat R (Sec (A ⊗ A).hom (H.obj t).unop.1)))
    (GlobalTheory.T.additiveClassDegreeTwo_vanish_affineBases_alt hP R R₁ q hq A g hA hg _ T _ H K₀ K₁ K₂ le₀ le₁ le₂ hB hH)
  obtain ⟨u', h1, h2⟩ := GlobalTheory.T.exists_cocycle_correction_square_zero_ideal R I hI _ _ _ _ _ _ _ hpi u v hun hdef hv hrel
  exact GlobalTheory.T.exists_lineBundle_lift_of_strict_cocycle R _ _ A.hom i L hL u' hB (hnear u' h1) (hall u' (hnear u' h1)).1 h2

theorem abLift : AbLift :=
  abLift_of_prim (GlobalTheory.T.primitive_degree_two_extension (GlobalTheory.T.additiveClassDegreeTwo_structureSheaf_vanish fun R _ A _ g hA hg ↦
    ⟨(GlobalTheory.T.abelian_structure_cohomology_statement R A g hA hg).1, (GlobalTheory.T.abelian_structure_cohomology_statement R A g hA hg).2.1⟩))

end

theorem exists_fac_quot {R K : Type} [CommRing R] [Field K] (J : Ideal R) (hJ : J ^ 2 = ⊥) (s : Sp K ⟶ Sp R) :
    ∃ s' : Sp K ⟶ Sp (R ⧸ J), s' ≫ spMap (Ideal.Quotient.mk J) = s := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  have h : ∀ a ∈ J, φ.hom a = 0 := fun a ha ↦ by
    have h2 : a ^ 2 = 0 := by simpa [hJ] using Ideal.pow_mem_pow ha 2
    have := congrArg φ.hom h2
    rw [map_pow, map_zero] at this
    exact pow_eq_zero_iff two_ne_zero |>.1 this
  refine ⟨spMap (Ideal.Quotient.lift J φ.hom h), ?_⟩
  rw [← Spec.map_comp]
  rfl

theorem exists_fam {S : Scheme.{0}} {A U T : Over S} [GrpObj A] [IsLocallyNoetherian U.left] (hA : IsAbelianScheme A)
    (p : T ⟶ U) (hp : ∀ (K : Type) [Field K] (s : Sp K ⟶ S) (t : Over.mk s ⟶ U), ∃ t' : Over.mk s ⟶ T, t' ≫ p = t)
    {N : LB (A ⊗ T).left} (hN : N.IsLB) (ha : IsAdditive N) (c : Pic (A ⊗ U).left)
    (hc : CechPic.pull (A ◁ p).left c = cls N hN) :
    ∃ (M : LB (A ⊗ U).left) (hM : M.IsLB), IsAdditive M ∧
      ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ T), evc hM a (t ≫ p) = evc hN a t := by
  obtain ⟨M, hM, e⟩ := cls_surj (c - CechPic.pull (lift 1 (snd A U)).left c)
  have k : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ U), evc hM a t =
      CechPic.pull (lift a t).left c - CechPic.pull (lift (1 : Y ⟶ A) t).left c := fun Y a t ↦ by
    rw [evc, e, map_sub, ← CechPic.pull_comp, ← Over.comp_left, comp_lift, MonObj.comp_one, lift_snd]
  have k' : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ T), CechPic.pull (lift a (t ≫ p)).left c = evc hN a t :=
    fun Y a t ↦ by
    rw [evc, ← hc, ← CechPic.pull_comp, ← Over.comp_left, lift_whiskerLeft]
  have key : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ T), evc hM a (t ≫ p) = evc hN a t := fun Y a t ↦ by
    rw [k, k', k', ha.evc_one hN, sub_zero]
  refine ⟨M, hM, GlobalTheory.T.isAdditive_lineBundleFamily_of_geometricFibres S A U hA M hM ((triv_ev_iff hM _ _).2 (by rw [k, sub_self])) fun K _ _ s t ↦ ?_, key⟩
  obtain ⟨t', rfl⟩ := hp K s t
  refine (isAdditive_iff (pull_isLB hM _)).2 fun Y a a' y ↦ ?_
  simp only [evc_ev hM, lift_fst, lift_snd_assoc]
  simp only [← Category.assoc, key]
  exact (isAdditive_iff hN).1 ha Y a a' _

theorem hasRep_of_sqZero : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ J : Ideal R, J ^ 2 = ⊥ → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk J))) → HasRep A g (𝟙_ _) := by
  intro R _ _ A _ g hA hg J hJ ⟨B, b, P, hP, hb⟩
  refine GlobalTheory.T.representingScheme_of_finite_surjective_lift R A g hA hg B _ b P ?_ ?_ hP hb fun x ↦ ?_
  · haveI : IsClosedImmersion (spMap (Ideal.Quotient.mk J)) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    exact inferInstanceAs (IsFinite (spMap (Ideal.Quotient.mk J)))
  · exact GlobalTheory.LiftSys.surjective_spMap_sqZero _ Ideal.Quotient.mk_surjective hJ
      fun _ h ↦ Ideal.Quotient.eq_zero_iff_mem.1 h
  obtain ⟨C, _, σ, j, hs, hj, ho, hx⟩ := GlobalTheory.T.exists_affine_chart_smooth_lift_sqZero R J hJ g B b hb.smooth x
  have hN : (ev P (fst A _) (snd A _ ≫ j)).IsLB := pull_isLB hP.fam.isLB _
  have ha : IsAdditive (ev P (fst A _) (snd A _ ≫ j)) := (isAdditive_iff hN).2 fun Y a a' y ↦ by
    simp only [evc_ev hP.fam.isLB, lift_fst, lift_snd_assoc]
    exact (isAdditive_iff hP.fam.isLB).1 hP.fam.add Y a a' _
  obtain ⟨c, hc⟩ := GlobalTheory.T.additiveFamily_reduction_lifts_lineBundle abLift R J hJ A g hA hg C σ _ hN ha
  haveI : Smooth (spMap σ) := SmoothOfRelativeDimension.smooth g _
  haveI : IsLocallyNoetherian (Over.mk (spMap σ)).left :=
    LocallyOfFiniteType.isLocallyNoetherian (spMap σ)
  obtain ⟨M, hM, hMa, key⟩ := exists_fam hA (fst (Over.mk (spMap σ)) (Over.mk (spMap (Ideal.Quotient.mk J))))
    (fun K _ s t ↦ by
      obtain ⟨s', hs'⟩ := exists_fac_quot J hJ s
      exact ⟨lift t (Over.homMk s' hs'), lift_fst _ _⟩) hN ha c hc
  refine ⟨_, M, j, ⟨hM, hMa⟩, hs, hj, ho, hx, (same_iff hM hP.fam.isLB _ _).2 ?_⟩
  rw [key, evc_ev hP.fam.isLB, lift_fst, lift_snd_assoc]

end GlobalTheory.LBLift
