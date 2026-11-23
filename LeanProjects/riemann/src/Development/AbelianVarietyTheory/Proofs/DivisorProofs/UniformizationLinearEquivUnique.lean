import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop

namespace GlobalTheory.UnifTransfer

theorem mul_comp_of_isGrpPullback {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] (c : G' ⟶ G)
    (h : IsGrpPullback G' G (𝟙 S) c.left) {T : Over S} (x y : T ⟶ G') :
    (x * y) ≫ c = (x ≫ c) * (y ≫ c) := by
  let i : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have e := h.2 T x y (i ≫ x ≫ c) (i ≫ y ≫ c) (by simp [i]) (by simp [i])
  rw [← MonObj.comp_mul] at e
  ext
  simpa [i] using e.symm

theorem isMonHom_of_isGrpPullback {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] (c : G' ⟶ G)
    (h : IsGrpPullback G' G (𝟙 S) c.left) : IsMonHom c := by
  constructor
  · have e := mul_comp_of_isGrpPullback c h (1 : 𝟙_ (Over S) ⟶ G') 1
    rw [_root_.mul_one] at e
    have e' : (1 : 𝟙_ (Over S) ⟶ G') ≫ c = 1 := left_eq_mul.1 e
    simpa [Hom.one_def] using e'
  · have e := mul_comp_of_isGrpPullback c h (fst G' G') (snd G' G')
    simp only [Hom.mul_def, lift_fst_snd, Category.id_comp] at e
    rw [e]
    congr 1

theorem exists_linearEquiv_of_isPolFibre : ∀ (R : Type) [CommRing R] (f : R →+* ℂ) (P₀ : Out.PolAV (Sp R)) (Q Q' : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ P₀.A.left) (ψ' : Q'.A.left ⟶ P₀.A.left) (g : ℕ) (u : HolUnif Q.A Q.L g) (u' : HolUnif Q'.A Q'.L g) (Hm Hm' : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (χ' : u'.Λ → ℂ), Q.g = g → Q'.g = g → GlobalTheory.IsPolFibre f P₀ Q ψ → GlobalTheory.IsPolFibre f P₀ Q' ψ' → u.IsAH Hm χ → u'.IsAH Hm' χ' → ∃ F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), (∀ z, F z ∈ u'.Λ ↔ z ∈ u.Λ) ∧ ∀ z w, hermForm Hm' (F z) (F w) = hermForm Hm z w := by
  intro R _ f P₀ Q Q' ψ ψ' g u u' Hm Hm' χ χ' hg hg' h h' hA hA'
  obtain ⟨φ, -, -, hφ, hL⟩ := GlobalTheory.CM.EllComp.exists_isPolFibre_lift (g := RingHom.id ℂ) h'
    (by rw [RingHom.id_comp]; exact h)
  have e0 : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id _
  have hφ' : IsGrpPullback Q.A Q'.A (𝟙 _) φ := hφ.congr e0 rfl
  let c : Q.A ⟶ Q'.A := Over.homMk φ (hφ'.1.w.trans (Category.comp_id _))
  haveI hc : IsMonHom c := isMonHom_of_isGrpPullback c hφ'
  haveI : IsIso φ := hφ'.1.isIso_fst_of_isIso
  haveI : IsIso c.left := this
  haveI : Mono c := Over.mono_of_mono_left c
  subst hg'
  obtain ⟨h1, h2, -⟩ := GlobalTheory.AnyUnif.tangent_and_unimodular GlobalTheory.thetaUnifAV_all Q' u'
  obtain ⟨F, hF, -⟩ := HomLinear.exists_linear_of_isMonHom Q.A Q'.A Q.isAb Q'.isAb Q.L Q'.L _ _ u u' h1 h2 c hc
  have hΛ : ∀ z, F z ∈ u'.Λ ↔ z ∈ u.Λ := fun z => by
    rw [← u'.ker, hF, ← u.ker, ← MonObj.one_comp c, cancel_mono]
  haveI := u.discrete
  have hinj := GlobalTheory.AnyUnif.injective_of_ker_le_discrete u.Λ F fun z hz => (hΛ z).1 (hz ▸ u'.Λ.zero_mem)
  refine ⟨LinearEquiv.ofInjectiveEndo F hinj, hΛ, fun z w => ?_⟩
  have hH := hermForm_pull_eq_of_lbIso_pow Q.A Q'.A Q.L Q'.L Q.isLB Q'.isLB _ _ u u' Hm χ Hm' χ' hA hA'
    c F hF 1 1 (by
      obtain ⟨w, hw⟩ := hL
      exact ⟨LB.linCombIso w _ _, DVR.linCombIso_isGen w hw _ _⟩) z w
  simpa using hH

end GlobalTheory.UnifTransfer
