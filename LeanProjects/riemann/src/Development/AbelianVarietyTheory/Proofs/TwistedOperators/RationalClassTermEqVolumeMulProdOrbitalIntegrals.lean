import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NonFieldTypeVanishing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasOrbIntTensorOfHasOrbInt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalStableOrbitalIntegralsWellDefinedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusCompactQuotientFiniteVolumeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassTermEqVolumeMulOrbitalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCentralizerMeasuresFromUnitaryTorusStatement

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrClassTerm

theorem integrable_descend_of_stdDom {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ]
    {μ : Measure G} {φ : G → ℂ} (hi : LeftInv Γ φ) (h : IntegrableOn φ (stdDom Γ) μ) :
    Integrable (descend Γ φ) (quotMeasure Γ μ) ∧
      ∫ q, descend Γ φ q ∂quotMeasure Γ μ = ∫ x in stdDom Γ, φ x ∂μ := by
  have e : descend Γ φ = φ ∘ sec Γ := funext fun q => by
    rw [Function.comp_apply, ← hi.descend_mk, mk_sec]
  rw [e]
  exact ⟨(measurePreserving_sec.integrable_comp_emb measurableEmbedding_sec).2 h,
    measurePreserving_sec.integral_comp measurableEmbedding_sec φ⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem continuous_tensor {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsLattice E L]
    {fa : ∀ w, GArch σ J w → ℂ} {ff : ∀ v, GLoc σ J v → ℂ}
    (ha : ∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w)) (hf : IsFinFamily σ J L ff) :
    Continuous (tensor σ J fa ff) ∧ HasCompactSupport (tensor σ J fa ff) := by
  have hb := hf.tensorFin_mem
  have h1 : Continuous (tensorInf σ J fa) :=
    continuous_finset_prod _ fun w _ => (ha w).1.comp (continuous_projInfArch σ J w)
  have h2 : HasCompactSupport (tensorInf σ J fa) := by
    refine .intro ((infContEquivPi σ J).toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_univ_pi fun w => (ha w).2)) fun g hg => ?_
    by_contra hne
    exact hg fun w _ => subset_tsupport _ (Finset.prod_ne_zero_iff.1 hne w (Finset.mem_univ w))
  rw [tensor_eq_infFin]
  refine ⟨(h1.comp (continuous_projInf σ J)).mul (hb.1.continuous.comp (continuous_projFin σ J)), .intro
    ((infFinEquiv σ J).toHomeomorph.isClosedEmbedding.isCompact_preimage (IsCompact.prod h2 hb.2)) fun g hg => ?_⟩
  by_contra hne
  exact hg ⟨subset_tsupport _ (left_ne_zero_of_mul hne), subset_tsupport _ (right_ne_zero_of_mul hne)⟩

theorem isMulCommutative_cent_ratEmb {γ : GRat σ J} (hγ : IsRegSS γ.1.1) : IsMulCommutative (cent (ratEmb σ J γ)) :=
  ⟨⟨fun a b => Subtype.ext (GAd_ext σ J
    (fun w => by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val
        ((isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hγ w)).1.1
          (centMap (projArch σ J w) _ a) (centMap (projArch σ J w) _ b)))
    fun v => by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val
        ((isMulCommutative_cent_HA (isRegSS_proj_ratEmb hγ v)).1.1
          (centMap (proj σ J v) _ a) (centMap (proj σ J v) _ b)))⟩⟩

theorem class_term : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsLattice E L], ∀ μa μf μ, IsRestrictedProd σ J L μa μf μ → ∀ fa ff, (∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w)) → IsFinFamily σ J L ff → ∀ dta dtf dt, IsTorusMeas P dta dtf dt → ∀ γ : GRat σ J, γ.1.1.charpoly = P.1 → ∀ (qf : ∀ v : HeightOneSpectrum (𝓞 F), XSet P (Fv F v) J) (qa : ∀ w : InfinitePlace F, XSet P w.Completion J), (∀ v, HasCls P _ J (proj σ J v (ratEmb σ J γ)) (qf v).1) → (∀ w, HasCls P _ J (projArch σ J w (ratEmb σ J γ)) (qa w).1) → Integrable (descend (ratPts σ J) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (ratPts σ J) (ratEmb σ J γ) (tensor σ J fa ff))) (quotMeasure (ratPts σ J) μ) ∧ ∫ q, descend (ratPts σ J) (GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel (ratPts σ J) (ratEmb σ J γ) (tensor σ J fa ff)) q ∂quotMeasure (ratPts σ J) μ = ((torVol P dt).toReal : ℂ) * ((∏ᶠ v, orbCls (μf v) (dtf v) (ff v) (qf v)) * ∏ w, orbCls (μa w) (dta w) (fa w) (qa w)) := by
  intro F E _ _ _ _ _ σ hcm r P J hJ L _ μa μf μ hμ fa ff hfa hff dta dtf dt hdt γ hγ qf qa hqf hqa
  have hreg : IsRegSS γ.1.1 := by
    rw [IsRegSS, hγ]; exact P.2.2.1.separable
  obtain ⟨ea, ef, e, hc, ⟨𝓣, h𝓣, hvol⟩, hf, ha⟩ := GlobalTheory.T.exists_centralizer_measures_from_unitaryTorus F E σ hcm r P J hJ L γ hγ dta dtf dt hdt
  obtain ⟨pf, pa⟩ := GlobalTheory.T.local_stable_orbital_integrals_well_defined F E σ hcm r r P J hJ
  have := hμ.haar
  have := hc.1
  have := hc.2.1
  have := hc.2.2.1
  have : ∀ w, (ea w).IsMulRightInvariant := fun w =>
    isMulRightInvariant_cent (isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hreg w)) _
  have : ∀ v, (ef v).IsMulRightInvariant := fun v =>
    isMulRightInvariant_cent (isMulCommutative_cent_HA (isRegSS_proj_ratEmb hreg v)) _
  have hf' : ∀ v, HasOrbInt (μf v) (proj σ J v (ratEmb σ J γ)) (ef v) (ff v) (orbCls (μf v) (dtf v) (ff v) (qf v)) :=
    fun v => by
      obtain ⟨x, φ, h, e1, e2⟩ := hqf v
      have := (pf v (μf v) (dtf v) (ff v) (hμ.haar_loc v) (IsRestrictedProd.haar_loc hdt v) (hff.1 v).1.continuous
        (hff.1 v).2).2 x φ h
      rw [show qf v = ⟨QuotientGroup.mk x, x, φ, rfl, h⟩ from Subtype.ext e1.symm]
      exact (hf v x φ h e2 _ _ _).1 this
  have ha' : ∀ w, HasOrbInt (μa w) (projArch σ J w (ratEmb σ J γ)) (ea w) (fa w)
      (orbCls (μa w) (dta w) (fa w) (qa w)) := fun w => by
    obtain ⟨x, φ, h, e1, e2⟩ := hqa w
    have := (pa w (μa w) (dta w) (fa w) (hμ.haar_arch w) (IsRestrictedProd.haar_arch hdt w) (hfa w).1
      (hfa w).2).2 x φ h
    rw [show qa w = ⟨QuotientGroup.mk x, x, φ, rfl, h⟩ from Subtype.ext e1.symm]
    exact (ha w x φ h e2 _ _ _).1 this
  have hO := (hasOrbInt_tensor_of_hasOrbInt hμ hc hff.2 (eventually_conj_mem_stabLoc hcm hJ L hreg) ha' hf').2
  have hfin := (GlobalTheory.T.unitaryTorus_compact_quotient_finite_volume F E σ hcm r P).2 dt (IsRestrictedProd.haar hdt)
  have ht := continuous_tensor hfa hff
  obtain ⟨-, h1, h2⟩ := GlobalTheory.T.classTerm_eq_volume_mul_orbitalIntegral (GAd σ J) (ratPts σ J) (ratEmb σ J γ) (range_ratEmb σ J ▸ ⟨γ, rfl⟩)
    (isMulCommutative_cent_ratEmb hreg) μ e 𝓣 h𝓣 (hvol ▸ hfin.lt_top) _ _ ht.1 ht.2 hO _
    (isFundamentalDomain_stdDom _ μ)
  obtain ⟨h3, h4⟩ := integrable_descend_of_stdDom
    (fun g hg x => GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.classKernel_mul (ratEmb σ J γ) (tensor σ J fa ff) hg x) h1
  refine ⟨h3, ?_⟩
  rw [h4, h2, Measure.real, hvol, mul_comm (∏ w, _)]

end GlobalTheory.TrClassTerm
