import Mathlib
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuotientIsAbelianSchemeOfQuotientScheme
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFlatSubgroupSchemeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SeparatedOfFiniteSurjectiveQuotientStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormMapRestrictionCompatibleStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyOfFinitePresentationOfCancelStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormLineBundleDescentStatement

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GR.QuotSide

section Act
variable {S : Scheme.{0}} {G A : Over S} [GrpObj G] [GrpObj A] (h : G ⟶ A) [IsMonHom h]

abbrev act : ModObj G A :=
  letI := ModObj.regular A
  Mod.scalarRestriction h A

lemma act_smul : (act h).smul = (fst G A ≫ h) * snd G A := by
  rw [Hom.mul_def]
  change h ▷ A ≫ μ[A] = _
  congr 1

end Act

theorem quotientByFiniteFlat_of_freeQuotient (hF : GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuotientScheme) :
    QuotientByFiniteFlatStatement := by
  intro R _ A _ L hA hL hamp B _ _ h hsub
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  obtain ⟨_, hmon, hmono⟩ := GlobalTheory.T.finite_flat_subgroup_scheme R A B h hsub
  letI := act h
  have hgam : (γ[sp (R₀ := R) B, A] : sp (R₀ := R) B ⊗ A ⟶ A) = (fst _ A ≫ h) * snd _ A := act_smul h
  have hsmul : ∀ {T : Over (Spec (CommRingCat.of R))} (g : T ⟶ sp (R₀ := R) B) (x : T ⟶ A),
      g • x = (g ≫ h) * x := by
    intro T g x
    rw [Hom.smul_def, hgam, comp_mul]
    simp
  have hample : GlobalTheory.IsAmpleLB L := GlobalTheory.isAmpleLB_of_relAmple_of_isAffine A hL hamp
  have hG : GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFiniteLocallyFree (sp (R₀ := R) B).hom := by
    have e : (sp (R₀ := R) B).hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) := rfl
    have := hsub.proj
    have := hsub.fin
    have : Module.FinitePresentation R B := Module.finitePresentation_of_projective R B
    have hfp : (algebraMap R B).FinitePresentation :=
      RingHom.finitePresentation_algebraMap.2 (Algebra.FinitePresentation.of_finitePresentation R B)
    rw [e]
    refine ⟨(IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance),
      Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance), ?_⟩
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2 hfp
  have hfree : GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFreeAction (sp (R₀ := R) B) A := by
    intro T g x hx
    rw [hsmul] at hx
    have h1 : g ≫ h = 1 := mul_eq_right.mp hx
    rw [← cancel_mono h, h1, MonObj.one_comp]
  have horb : ∀ x : A.left, ∃ U : A.left.Opens, IsAffineOpen U ∧
      GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.orbit (sp (R₀ := R) B) A x ⊆ U := by
    intro x
    have hf : IsFinite (sp (R₀ := R) B).hom := hG.1
    have hs : IsFinite (snd (sp (R₀ := R) B) A).left := by
      rw [Over.snd_left]; infer_instance
    have hfin : (GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.orbit (sp (R₀ := R) B) A x).Finite :=
      (Scheme.Hom.finite_preimage_singleton _ x).image _
    obtain ⟨n, -, s, h₁, -, h₂⟩ := hample.exists_affine_finite_subset hfin
      (U := ⊤) (fun _ _ => trivial)
    exact ⟨_, h₂, h₁⟩
  obtain ⟨Y, q, -, hT⟩ := hF _ (sp (R₀ := R) B) A hG hfree horb
  obtain ⟨hq1, hq2, hq3⟩ := hT.isFiniteLocallyFree hG
  have hq4 := hT.surjective
  have hq : IsPullback ((fst _ A ≫ h) * snd _ A) (snd _ A) q q := hgam ▸ hT.1
  have hqc : QuasiCompact q.left := inferInstance
  obtain ⟨inst, hcomm, hhom, hker⟩ := GlobalTheory.AbelianQuotient.exists_grpObj h q hq
  have hw : q.left ≫ Y.hom = A.hom := Over.w q
  have hsnd : IsFinite (snd (sp (R₀ := R) B) A).left := by
    have hf : IsFinite (sp (R₀ := R) B).hom := hG.1
    rw [Over.snd_left]; infer_instance
  have hab : IsAbelianScheme Y := by
    have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth
      hA.geomConnected
    have : IsSeparated Y.hom := GlobalTheory.T.separated_of_finite_surjective_quotient q _ _ hq hsnd inferInstance hq1 hq4
    have : Flat (q.left ≫ Y.hom) := by rw [hw]; infer_instance
    have : UniversallyClosed (q.left ≫ Y.hom) := by rw [hw]; infer_instance
    have : GeometricallyReduced (q.left ≫ Y.hom) := by rw [hw]; infer_instance
    have : GeometricallyConnected (q.left ≫ Y.hom) := by rw [hw]; infer_instance
    have := GlobalTheory.flat_of_comp_of_flat_of_surjective q.left Y.hom
    have := UniversallyClosed.of_comp_surjective q.left Y.hom
    have := GlobalTheory.AbelianQuotient.geometricallyReduced_of_comp q.left Y.hom
    have : LocallyOfFinitePresentation Y.hom :=
      GlobalTheory.T.locallyOfFinitePresentation_of_cancel q.left Y.hom hq1 hq2 hq3 hq4 (by rw [hw]; infer_instance)
    exact ⟨hcomm, GlobalTheory.AbelianQuotient.smooth_of_grpObj_of_flat Y, ⟨⟩,
      GlobalTheory.AbelianQuotient.geometricallyConnected_of_comp q.left Y.hom⟩
  have := hab.proper
  obtain ⟨N, hN₁, hN₂⟩ := GlobalTheory.T.norm_map_restriction_compatible q.left hq1 hq2 hq3
  obtain ⟨L', hL', hN⟩ := GlobalTheory.T.norm_line_bundle_descent q.left hq1 N hN₁ hN₂ L hL (by
    intro y
    obtain ⟨W, -, h₁, -, t⟩ := hample.exists_affine_finite_subset_trivial hL
      (Scheme.Hom.finite_preimage_singleton q.left y) (U := ⊤) (fun _ _ => trivial)
    exact ⟨W, fun x hx => h₁ hx, t⟩)
  refine ⟨Y, inst, L', q, hab, hL', ?_, hhom, hq1, hq2, hq4, ?_⟩
  · have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
    have : CompactSpace Y.left := q.left.surjective.compactSpace q.left.continuous
    refine (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine Y hL').2
      (GlobalTheory.isAmpleLB_of_forall_le hL' fun y U hy => ?_)
    obtain ⟨n, hn, s, h₁, h₂, -⟩ := hample.exists_affine_finite_subset
      (Scheme.Hom.finite_preimage_singleton q.left y) (U := q.left ⁻¹ᵁ U)
      (fun x hx => show q.left x ∈ U from (show q.left x = y from hx) ▸ hy)
    obtain ⟨σ, hσ⟩ := hN n s
    refine ⟨n, hn, σ, (hσ y).2 fun x hx => h₁ hx, fun y' hy' => ?_⟩
    obtain ⟨x, rfl⟩ := q.left.surjective y'
    exact h₂ ((hσ _).1 hy' x rfl)
  · intro S _ _ z
    have hhq : h ≫ q = 1 := hker.w.trans Hom.one_def.symm
    constructor
    · intro hz
      let y : sp (R₀ := R) S ⟶ sp (R₀ := R) B :=
        hker.lift z (toUnit _) (by rw [hz, Hom.one_def])
      have hy : y ≫ h = z := hker.lift_fst _ _ _
      obtain ⟨ψ, hψ⟩ := Spec.map_surjective y.left
      have hc : CommRingCat.ofHom (algebraMap R B) ≫ ψ = CommRingCat.ofHom (algebraMap R S) := by
        apply Spec.map_injective
        rw [Spec.map_comp, hψ]
        exact Over.w y
      let φ : B →ₐ[R] S := { ψ.hom with
        commutes' := fun r => congr($hc r) }
      have hφ : spMap φ = y := Over.OverMorphism.ext hψ
      exact ⟨φ, by rw [hφ, hy]⟩
    · rintro ⟨φ, rfl⟩
      rw [Category.assoc, hhq, comp_one]

end GlobalTheory.CompanionTheory.Ar.GR.QuotSide
