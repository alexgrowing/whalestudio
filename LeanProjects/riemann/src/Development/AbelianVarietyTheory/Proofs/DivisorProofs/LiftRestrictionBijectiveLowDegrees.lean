import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSectionsMonoReductionAffineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCohomologyComputedOnAffinePairsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineFormsRestrictionAffineLiftBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomSpecPointsLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineForgetFormsBijectiveSiteAndPairsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1BijectiveOfExhaustingFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BijectiveRestrictionFourTermComplexOfExhaustionStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem resMap_bij12_of_fnMap {C C' : Type 1} [Category.{0} C] [Category.{0} C'] (K : Cx C) (G : C' ⥤ C)
    (h : K.fnMap.PullbackBijectiveDegreesOneTwo) (h' : (K.res G).fnMap.PullbackBijectiveDegreesOneTwo) (h₀ : ((Cx.single K.M0).resMap G).PullbackBijectiveDegreesOneTwo) :
    (K.resMap G).PullbackBijectiveDegreesOneTwo := by
  constructor
  · have e : (K.res G).fnMap.h1 ∘ (K.resMap G).h1 = ((Cx.single K.M0).resMap G).h1 ∘ K.fnMap.h1 := by
      funext c
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
      rfl
    exact (Function.Bijective.of_comp_iff' h'.1 _).1 (e ▸ h₀.1.comp h.1)
  · have e : (K.res G).fnMap.h2 ∘ (K.resMap G).h2 = ((Cx.single K.M0).resMap G).h2 ∘ K.fnMap.h2 := by
      funext c
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
      rfl
    exact (Function.Bijective.of_comp_iff' h'.2 _).1 (e ▸ h₀.2.comp h.2)

theorem resMap_comp_bij12 {C C' : Type 1} {C'' : Type} [Category.{0} C] [Category.{0} C'] [Category.{0} C'']
    (K : Cx C) (G : C' ⥤ C) (H : C'' ⥤ C') (h : (K.resMap G).PullbackBijectiveDegreesOneTwo) (h' : ((K.res G).resMap H).PullbackBijectiveDegreesOneTwo) :
    (K.resMap (H ⋙ G)).PullbackBijectiveDegreesOneTwo := by
  constructor
  · have e : ⇑(K.resMap (H ⋙ G)).h1 = ((K.res G).resMap H).h1 ∘ (K.resMap G).h1 := by
      funext c
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
      rfl
    exact e ▸ h'.1.comp h.1
  · have e : ⇑(K.resMap (H ⋙ G)).h2 = ((K.res G).resMap H).h2 ∘ (K.resMap G).h2 := by
      funext c
      obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective c
      rfl
    exact e ▸ h'.2.comp h.2

theorem Lift.resMap_toE_pullbackBijectiveDegreesOneTwo (D : Data) (Λ : Lift D) :
    (((KK D.κ D.t).res (pE D.κ D.t D.i)).resMap Λ.toE).PullbackBijectiveDegreesOneTwo := by
  obtain ⟨N₀, hN₀⟩ := (GlobalTheory.T.hom_spec_points_levels D Λ).2.2.2
  have mono : ∀ m n T, m ≤ n → LevE D.κ D.t D.i m T → LevE D.κ D.t D.i n T := fun m n T hmn hT ↦
    le_bot_iff.1 (((fil_properties _ _ T.obj.T.δ).2.2.1 m n hmn).trans (le_of_eq hT))
  have exh : ∀ T, ∃ n, LevE D.κ D.t D.i n T := fun T ↦ (isDPNilpotent_iff_exists_isLevel T.obj.T.δ).1 T.obj.T.nil
  have lev : ∀ N, N₀ + 1 ≤ N → ∃ h : ∀ U, LevE D.κ D.t D.i N (Λ.toE.obj U),
      ((((KK D.κ D.t).res (pE D.κ D.t D.i)).res (LevE D.κ D.t D.i N).ι).resMap
        ((LevE D.κ D.t D.i N).lift Λ.toE h)).Bij := by
    intro N hN
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
    exact ⟨fun U ↦ hN₀ _ (by omega) U, GlobalTheory.T.crystallineForms_restriction_affineLift_bijective D Λ n _⟩
  exact ⟨GlobalTheory.T.h1_resMap_bijective_of_exhausting_properties _ _ _ _ Λ.toE (N₀ + 1) mono exh lev, GlobalTheory.T.bijective_restriction_fourTermComplex_of_exhaustion _ _ _ _ Λ.toE (N₀ + 1) mono exh lev⟩

theorem Lift.resMap_lift_pullbackBijectiveDegreesOneTwo : ∀ (D : Data) (Λ : Lift D), ((KK D.κ D.t).resMap Λ.L).PullbackBijectiveDegreesOneTwo := by
  intro D Λ
  have hp := GlobalTheory.T.fnMap_pullbackBijective12_kk_and_res D.R D.I D.κ _ D.t _ D.i
  have hg := GlobalTheory.T.pullbackBijective12_resMap_of_affine_inter D.R D.I D.κ _ D.t _ D.i D.smooth_mono_inf.2.2
  exact resMap_comp_bij12 (KK D.κ D.t) (pE D.κ D.t D.i) Λ.toE
    (resMap_bij12_of_fnMap _ _ hp.1 hp.2 hg) (Lift.resMap_toE_pullbackBijectiveDegreesOneTwo D Λ)

end GlobalTheory.PDForm
