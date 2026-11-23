import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisationCompleteLocalNormalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegDataPsiOfSectionNonzeroFibres
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueExpansionSectionAdmissibleBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitMapSnd
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPsiThetaExpansionPsiRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUnitValEqMul
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EgaBundleFromLaws
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiRelOfExpTStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ForallTermNeZeroOfPsiRelationStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RigidificationComparisonUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiCmpOfSecCmpStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiEvenDescendBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TauBimultOfBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSectionNonzeroFibresLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTwistedSectionThetaTranslateCoefStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiScalarMemOfPsiMemIdealStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiScalarEqExpansionCoefRatioStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionPreUniformisedCompleteNormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackNonzeroSectionInjectiveDomainMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroExpansionTermCompleteDVRStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiScalarNsmulEqUnitMulPowSqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatedThetaCoefficientSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecIsMulOfBaseMultipleThetaSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecIsMulOfTranslatedThetaCoefficientProportionalStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

theorem integral_of_sqPow_bdd (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (y : FractionRing R) (r : R) (hr : r ≠ 0)
    (h : ∀ n : ℕ, ∃ s : R, algebraMap R (FractionRing R) r * y ^ (n ^ 2) = algebraMap R _ s) :
    ∃ s : R, y = algebraMap R _ s := by
  set c : FractionRing R := algebraMap R (FractionRing R) r with hc
  have hc0 : c ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr
  have hall : ∀ k : ℕ, ∃ s : R, c ^ 4 * y ^ k = algebraMap R _ s := by
    intro k
    obtain ⟨p, q, u, v, hk⟩ := Nat.sum_four_squares k
    obtain ⟨s1, h1⟩ := h p
    obtain ⟨s2, h2⟩ := h q
    obtain ⟨s3, h3⟩ := h u
    obtain ⟨s4, h4⟩ := h v
    refine ⟨s1 * s2 * s3 * s4, ?_⟩
    rw [← hk, map_mul, map_mul, map_mul, ← h1, ← h2, ← h3, ← h4, pow_add, pow_add, pow_add]
    ring
  let S : Subalgebra R (FractionRing R) := Algebra.adjoin R {y}
  have hle : Subalgebra.toSubmodule S ≤ Submodule.span R {(c ^ 4)⁻¹} := by
    show Subalgebra.toSubmodule (Algebra.adjoin R {y}) ≤ _
    rw [Algebra.adjoin_eq_span, Submodule.span_le]
    intro z hz
    obtain ⟨k, rfl⟩ := Submonoid.mem_closure_singleton.mp hz
    obtain ⟨s, hs⟩ := hall k
    have hc4 : c ^ 4 ≠ 0 := pow_ne_zero _ hc0
    have : y ^ k = s • (c ^ 4)⁻¹ := by
      rw [Algebra.smul_def, ← hs]; field_simp
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ s (Submodule.mem_span_singleton_self _)
  have hfg : (Subalgebra.toSubmodule S).FG := by
    haveI := isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span_singleton (R := R) ((c ^ 4)⁻¹ : FractionRing R))
    have h1 : ((Subalgebra.toSubmodule S).comap (Submodule.span R {(c ^ 4)⁻¹}).subtype).FG := IsNoetherian.noetherian _
    have h2 := h1.map (Submodule.span R {(c ^ 4)⁻¹}).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at h2
  have hint : IsIntegral R y := IsIntegral.of_mem_of_fg S hfg y (Algebra.self_mem_adjoin_singleton R y)
  obtain ⟨s, hs⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨s, hs.symm⟩

theorem exists_coefData_of_ne_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : GlobalTheory.UU.PreU (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V) (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'] (U' : GlobalTheory.UU.PreU (maximalIdeal V) D'.toPre A' G') (U₀ : Unif (maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left), GlobalTheory.LN.Cmp φ U U' F → GlobalTheory.LN.CDvr V → Function.Injective φ → (maximalIdeal V).comap φ = maximalIdeal R → GlobalTheory.LN.Under U' U₀.toUnifPre → ∃ (σ : U.SecGT (𝟙_ _) 1) (f g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α) (q : R), q ≠ 0 ∧ U.ExpT (𝟙_ _) 1 σ f ∧ (∀ α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom q (f α) (g α)) ∧ GlobalTheory.PsiRing.FibNZ (𝟙_ _ ⊗ D.P.A).hom (g 0) ∧ ∀ α, α ≠ 0 → ∃ a ∈ maximalIdeal R, ∃ h : GlobalTheory.UU.SecBT D (𝟙_ _) 1 α, ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom a (g α) h := by

  intro R _ _ _ hB D A G _ _ U V _ _ _ φ D' A' G' _ _ U' U₀ F C hV hφ hI hU
  obtain ⟨⟨h₁, h₂, -, -, -⟩, -⟩ := GlobalTheory.lawsAndExpansions
  have hE := GlobalTheory.LN.ega_of_laws h₁ h₂
  have hR : AdmBase R (maximalIdeal R) := hB.1
  haveI : IsNoetherianRing R := hR.1
  haveI : IsIntegrallyClosed R := hR.2.2.1
  have hmR : maximalIdeal R ≠ ⊤ := (maximalIdeal.isMaximal R).ne_top
  have := hV.1
  have hV' : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have hm : maximalIdeal V ≠ ⊤ := (maximalIdeal.isMaximal V).ne_top
  have hIm : (maximalIdeal R).map φ ≤ maximalIdeal V := Ideal.map_le_iff_le_comap.2 hI.ge
  obtain ⟨σ, hσ0⟩ := GlobalTheory.T.exists_nonzero_section_preUniformised_completeNormal R hB D A G U
  obtain ⟨f, hf, -⟩ := GlobalTheory.CompleteBaseExpansion.main h₁ h₂ hE R _ hR hmR D A G U 1 σ
  obtain ⟨σ', f', hf', hσσ, hff⟩ := GlobalTheory.ExpCmp.expT_cmp R V _ _ φ hIm D D'.toPre A A' G G' U U' F C 1 σ f hf
  have hcmp : GlobalTheory.PsiRing.SecCmp D D'.toPre C.β C.v C.xe f f' := hff
  have hrel' := GlobalTheory.T.psiRel_of_expT' h₁ h₂ V _ hV' D' A' G' U' U₀ hU σ' f' hf'
  have hσ'0 := GlobalTheory.T.pullback_nonzero_section_injective_domain_map R hB D A G U V φ D'.toPre A' G' U' F C hV hφ σ σ' hσσ hσ0
  have hne' : ∀ α, ∃ j, (f' α).f j ≠ 0 :=
    GlobalTheory.T.forall_term_ne_zero_of_psiRelation V D'.toPre f' hrel' (GlobalTheory.T.exists_nonzero_expansionTerm_completeDVR V hV D' A' G' U' U₀ hU σ' f' hf' hσ'0)
  have hne := GlobalTheory.PsiRing.ne_zero_of_secCmp C.pbB.1.w hcmp hne'
  obtain ⟨psi, h, hrel⟩ := GlobalTheory.exists_psi_psiRel h₁ h₂ R D f hne
  let E : DegPre R := GlobalTheory.LN.withPsi D psi h
  have hrelE : GlobalTheory.UU.PsiRel E (𝟙_ _) f := hrel
  have hrig : GlobalTheory.PsiRing.RigCmp φ E D'.toPre C.β C.v := GlobalTheory.T.rigidification_comparison_uniformisation R V _ _ φ hm hIm D D'.toPre A G A' G' U U' F C
  obtain ⟨gam, hgam⟩ := GlobalTheory.PsiRing.exists_generic_map hφ
  have hpsi : GlobalTheory.PsiRing.PsiCmp E D'.toPre C.β C.v C.xe gam :=
    GlobalTheory.T.psiCmp_of_secCmp' R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig f f' hcmp hrelE hrel' (hne' 0) gam hgam
  have hev : E.PsiEven :=
    GlobalTheory.T.psiEven_descend_baseChange h₁.globalFns R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr gam hgam hpsi D'.psi_even
  have hbi : E.TauBimult :=
    GlobalTheory.T.tauBimult_of_baseChange' h₁.globalFns R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig gam hgam hpsi D'.tau_bimult
  obtain ⟨ga, a, hS⟩ := GlobalTheory.exists_psiScal R E
  obtain ⟨th, hth, hmul⟩ := GlobalTheory.T.exists_thetaSection_nonzeroFibres_localRing h₂.secTwist R D
  obtain ⟨q, hq⟩ := hmul (f 0)
  choose b hb using fun χ : D.X => GlobalTheory.T.exists_twistedSection_thetaTranslate_coef R D th hmul χ (ga χ) (hS χ).1 (f χ)
  have hab : ∀ χ, algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) (b χ) := fun χ =>
    GlobalTheory.T.psiScalar_eq_expansionCoef_ratio R E ga a f th hS hrelE hth χ q (b χ) hq (hb χ)
  have hq0 : q ≠ 0 := by
    rintro rfl
    obtain ⟨j, hj⟩ := hne 0
    apply hj
    rw [GlobalTheory.T.secIsMul_of_baseMultiple_thetaSection R D th (f 0) 0 hq j]
    simp [scal]
  have hint : ∀ χ, ∃ c : R, ((a χ : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ c := fun χ => by
    refine integral_of_sqPow_bdd R _ q hq0 fun n => ?_
    obtain ⟨u, hu⟩ := GlobalTheory.T.psiScalar_nsmul_eq_unit_mul_pow_sq R E ga a hS hev hbi χ n
    refine ⟨((u⁻¹ : Rˣ) : R) * b (n • χ), ?_⟩
    rw [map_mul, ← hab, hu]
    have hu1 : algebraMap R (FractionRing R) ((u⁻¹ : Rˣ) : R) * algebraMap R _ (u : R) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    linear_combination (-(algebraMap R (FractionRing R) q * ((a χ : (FractionRing R)ˣ) : FractionRing R) ^ (n ^ 2))) * hu1
  choose c hc using hint
  have hbc : ∀ χ, b χ = q * c χ := fun χ => by
    apply IsFractionRing.injective R (FractionRing R)
    exact (hab χ).symm.trans (by rw [map_mul, ← hc χ])
  have hcm : ∀ χ : D.X, χ ≠ 0 → c χ ∈ maximalIdeal R := fun χ hχ => by
    obtain ⟨x, rfl⟩ := C.xe.surjective χ
    obtain ⟨m, hm₁, hm₂⟩ := GlobalTheory.T.psiScalar_mem_of_psi_mem_ideal R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr gam hgam hpsi ga a hS x _
      (D'.psi_pos x fun h0 => hχ (by rw [h0, map_zero])) _ q (hab _)
    have hm₃ : φ q * φ (c (C.xe x)) = φ q * m := by rw [← map_mul, ← hbc]; exact hm₂
    have hφq : φ q ≠ 0 := (map_ne_zero_iff _ hφ).2 hq0
    have e := mul_left_cancel₀ hφq hm₃
    have hmem : c (C.xe x) ∈ (maximalIdeal V).comap φ := Ideal.mem_comap.2 (by rw [e]; exact hm₁)
    exact (Set.ext_iff.1 (congrArg (fun J : Ideal R => (J : Set R)) hI) _).1 hmem
  choose G₁ hG₁ using fun χ : D.X => GlobalTheory.T.exists_translatedThetaCoefficient_section R D th χ (ga χ) (hS χ).1 (c χ)
  choose H₁ hH₁ using fun χ : D.X => GlobalTheory.T.exists_translatedThetaCoefficient_section R D th χ (ga χ) (hS χ).1 1
  classical
  let g : ∀ α, GlobalTheory.UU.SecBT D (𝟙_ _) 1 α := fun α => if h0 : α = 0 then h0 ▸ th else G₁ α
  refine ⟨σ, f, g, q, hq0, hf, fun α => ?_, ?_, fun α hα => ⟨c α, hcm α hα, H₁ α, ?_⟩⟩
  · by_cases h0 : α = 0
    · subst h0
      simp only [g, dif_pos rfl]
      exact GlobalTheory.T.secIsMul_of_baseMultiple_thetaSection R D th (f 0) q hq
    · simp only [g, dif_neg h0]
      exact GlobalTheory.T.secIsMul_of_translatedThetaCoefficient_proportional R D α (ga α) th (f α) (G₁ α) (b α) (c α) q (hb α) (hG₁ α) (hbc α)
  · simp only [g, dif_pos rfl]
    exact hth
  · simp only [g, dif_neg hα]
    exact GlobalTheory.T.secIsMul_of_translatedThetaCoefficient_proportional R D α (ga α) th (G₁ α) (H₁ α) (c α) 1 (c α) (hG₁ α) (hH₁ α) (_root_.mul_one _).symm

end GlobalTheory.Mum
end
