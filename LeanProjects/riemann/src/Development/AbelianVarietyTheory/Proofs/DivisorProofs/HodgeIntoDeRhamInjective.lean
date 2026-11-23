import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeIntoDeRhamInjectiveImports
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasicoherentHomFromAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeAffineBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeSubbundleCorrespondentExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCorrespondenceUniqueRightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCorrespondenceUniqueLeftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCorrespondenceSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemePullbackFstCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCorrespondenceLinearStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.LieVB

namespace GlobalTheory.HodgeSub

open GlobalTheory.Published

theorem main : GlobalTheory.CovTop.Hypotheses2 → ∀ (T : Scheme.{0}) (A : Over T) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (H : T.Modules) (e : ∀ (V : T.Opens) (hV : IsAffineOpen V),
        Γ(H, V) ≃ₗ[Γ(T, V)] GlobalTheory.DeRham.primDR (GlobalTheory.DeRhamSheaf.onAff A hV)),
      GlobalTheory.HodgeSeqSheaf.IsDRTriv A H e →
      ∃ i : GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A ⟶ H, ∀ (V : T.Opens) (hV : IsAffineOpen V),
        Function.Injective (GlobalTheory.QCoh.appLinear i V) ∧
        LinearMap.range ((e V hV).toLinearMap ∘ₗ GlobalTheory.QCoh.appLinear i V) =
          GlobalTheory.DeRham.PrimitiveSubmodule (GlobalTheory.DeRhamSheaf.onAff A hV) ∧
        ∃ N : Submodule Γ(T, V) Γ(H, V), IsCompl (LinearMap.range (GlobalTheory.QCoh.appLinear i V)) N := by
  intro P T A _ g hA hg H e he

  choose c hcF hc using GlobalTheory.T.hodge_subbundle_correspondent_exists P T A g hA hg
  have uniq := GlobalTheory.T.hodge_correspondence_unique_right P T A g hA hg
  let j : ∀ V : T.Opens, ∀ hV : IsAffineOpen V, Γ(GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A, V) →ₗ[Γ(T, V)] primDR (onAff A hV) :=
    fun V hV =>
      { toFun := c V hV
        map_add' := fun s s' => uniq V hV _ _ _ (hc V hV (s + s'))
          (GlobalTheory.T.hodge_correspondence_linear A V hV s s' _ _ 1 (hc V hV s) (hc V hV s')).1
        map_smul' := fun r s => uniq V hV _ _ _ (hc V hV (r • s))
          (GlobalTheory.T.hodge_correspondence_linear A V hV s s _ _ r (hc V hV s) (hc V hV s)).2 }
  have hj : ∀ V hV s, j V hV s = c V hV s := fun _ _ _ => rfl
  let j' : ∀ V : T.Opens, ∀ hV : IsAffineOpen V, Γ(GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A, V) →ₗ[Γ(T, V)] Γ(H, V) :=
    fun V hV => (e V hV).symm.toLinearMap ∘ₗ j V hV
  have compat : ∀ (V V' : T.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V)
      (s : Γ(GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A, V)),
      j' V' hV' (GlobalTheory.Twist.resM _ h s) = GlobalTheory.Twist.resM H h (j' V hV s) := by
    intro V V' hV hV' h s
    letI := resAlg h
    obtain ⟨φ, hφ, hfst⟩ := GlobalTheory.T.abelian_scheme_affine_base_change A V V' hV hV' h
    apply (e V' hV').injective
    change e V' hV' ((e V' hV').symm (c V' hV' _)) = _
    rw [LinearEquiv.apply_symm_apply, he V V' hV hV' h φ hφ hfst]
    change _ = (GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull (e V hV ((e V hV).symm (c V hV s)))
    rw [LinearEquiv.apply_symm_apply]
    exact uniq V' hV' _ _ _ (hc V' hV' _) (GlobalTheory.T.abelian_scheme_pullback_fst_comm P T A g hA hg V V' hV hV' h φ hφ hfst s _ (hc V hV s))
  obtain ⟨i, hi⟩ := GlobalTheory.T.quasicoherent_hom_from_affine T _ H j' compat
  refine ⟨i, fun V hV => ?_⟩
  have hjr : LinearMap.range (j V hV) = PrimitiveSubmodule (onAff A hV) := by
    apply le_antisymm
    · rintro _ ⟨s, rfl⟩
      exact hcF V hV s
    · intro x hx
      obtain ⟨s, hs⟩ := GlobalTheory.T.hodge_correspondence_surjective P T A g hA hg V hV x hx
      exact ⟨s, uniq V hV s _ _ (hc V hV s) hs⟩
  have hri : LinearMap.range ((e V hV).toLinearMap ∘ₗ GlobalTheory.QCoh.appLinear i V) = LinearMap.range (j V hV) := by
    rw [hi V hV]
    congr 1
    ext s
    simp [j']
  refine ⟨?_, hri.trans hjr, ?_⟩
  · rw [hi V hV]
    intro s s' hss
    have h1 : j V hV s = j V hV s' := (e V hV).symm.injective hss
    rw [hj, hj] at h1
    exact GlobalTheory.T.hodge_correspondence_unique_left P T A g hA hg V hV s s' _ (hc V hV s) (h1 ▸ hc V hV s')
  · have hA' : IsAbelianScheme (onAff A hV) := GlobalTheory.isAbelianScheme_pullback_obj _ A hA
    have hg' : SmoothOfRelativeDimension g (onAff A hV).hom :=
      (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg
    obtain ⟨-, ⟨N, hN⟩, -⟩ := P.p5.2.1 Γ(T, V) (onAff A hV) g hA' hg'
    refine ⟨N.map (e V hV).symm.toLinearMap, ?_⟩
    have hr : LinearMap.range (GlobalTheory.QCoh.appLinear i V) = (PrimitiveSubmodule (onAff A hV)).map (e V hV).symm.toLinearMap := by
      rw [← hjr, hi V hV, LinearMap.range_comp]
    rw [hr]
    exact ((Submodule.orderIsoMapComap (e V hV).symm).isCompl_iff).1 hN

end GlobalTheory.HodgeSub
