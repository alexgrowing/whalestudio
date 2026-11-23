import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzPeriodsOfTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyOfForall
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEllipticCurvePolarisedLatticeFamily
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RescaledUniformization

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatticeFibre

open GlobalTheory.HolUnifScale in

theorem exists_holUnif_rescale {A : Over (Sp ℂ)} [GrpObj A] {Lb : LB A.left} {n : ℕ} (u : HolUnif A Lb n)
    (w₀ : Fin n → ℂ) (hn : n = 1) (v : epsR ℂ ⟶ A) (hw : u.IsDiff w₀ v) (hw0 : w₀ ≠ 0) (Λ : PeriodPair) {c : ℂ}
    (hc : c ≠ 0) (hL : ∀ z : ℂ, z ∈ Λ.lattice ↔ (c⁻¹ * z) • w₀ ∈ u.Λ) :
    ∃ u' : HolUnif A Lb 1, (∀ w, w ∈ u'.Λ ↔ w 0 ∈ Λ.lattice) ∧ u'.IsDiff (fun _ ↦ c) v := by
  subst hn
  have h0 : w₀ 0 ≠ 0 := fun h ↦ hw0 (funext fun j ↦ by rw [Subsingleton.elim j 0]; exact h)
  have h : ∀ j : Fin 1, (fun _ : Fin 1 ↦ w₀ 0 / c) j ≠ 0 := fun _ ↦ div_ne_zero h0 hc
  refine ⟨rescale u _ h, fun w ↦ ?_, ?_⟩
  · refine (mem_latPull u _ h w).trans ?_
    rw [hL, scale_apply]
    have e : (fun j : Fin 1 ↦ w₀ 0 / c * w j) = (c⁻¹ * w 0) • w₀ := by
      funext j
      rw [Subsingleton.elim j 0, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
  · have key : ∀ W, (rescale u _ h).IsDiff W v ↔ u.IsDiff (fun j ↦ w₀ 0 / c * W j) v := by
      intro W
      unfold HolUnif.IsDiff
      have hf : ∀ (U : A.left.Opens) (f : Γ(A.left, U)),
          (fun z ↦ valAt' ((rescale u _ h).ex z).left U f) = (fun z ↦ valAt' (u.ex z).left U f) ∘ scale _ h :=
        fun _ _ ↦ rfl
      simp only [hf, ContinuousLinearEquiv.comp_right_fderiv, map_zero]
      rfl
    rw [key]
    have e : (fun _ : Fin 1 ↦ w₀ 0 / c * c) = w₀ := by
      funext j
      rw [Subsingleton.elim j 0, div_mul_cancel₀ _ hc]
    rw [e]
    exact hw

theorem exists_fibre_holUnif : ∀ (R₁ : Subring ℂ) (W : WeierstrassCurve R₁), IsUnit W.Δ → ∀ (Λ : PeriodPair) (c : ℂ), c ≠ 0 →
    ((W.c₄ : R₁) : ℂ) = 12 * c ^ 4 * Λ.g₂ → ((W.c₆ : R₁) : ℂ) = 216 * c ^ 6 * Λ.g₃ →
      ∃ (P : Out.PolAV (Sp R₁)) (A' : Over (Sp ℂ)) (_ : GrpObj A') (φ' : A'.left ⟶ P.A.left) (L' : LB A'.left)
        (u : HolUnif A' L' 1) (v : epsR R₁ ⟶ P.A) (v' : epsR ℂ ⟶ A'),
        IsAbelianScheme A' ∧ SmoothOfRelativeDimension 1 A'.hom ∧ IsGrpPullback A' P.A (spMap R₁.subtype) φ' ∧
        (∀ w, w ∈ u.Λ ↔ w 0 ∈ Λ.lattice) ∧ IsTangent v ∧ IsTangent v' ∧
        v'.left ≫ φ' = spMap (Chart.dualMapR R₁.subtype) ≫ v.left ∧ u.IsDiff (fun _ ↦ c) v' := by
  intro R₁ W hΔ Λ c hc h4 h6
  obtain ⟨P, v, Lf, ⟨hg, hv, -, hs⟩, hinv⟩ :=
    GlobalTheory.exists_polAV_latticeFamily GlobalTheory.thetaUnifAV_all GlobalTheory.polBaseChange_holds R₁ W hΔ
  obtain ⟨P', φ', h⟩ := GlobalTheory.exists_isPolFibre GlobalTheory.polBaseChange_holds R₁.subtype P
  obtain ⟨v', hv', -⟩ := GlobalTheory.existsUnique_isVecOver h.2.1.1 v
  have ht : IsTangent v := hv.1 0
  have ht' : IsTangent v' := hv'.isTangent h.2.1 ht
  obtain ⟨rig, hrig⟩ := P'.rigid
  obtain ⟨u, Hm, χ, -, -, -, hd, -⟩ := GlobalTheory.thetaUnifAV_all P' rig hrig
  obtain ⟨w, hw, -⟩ := hd v' ht'
  obtain ⟨hw0, hL⟩ := hs R₁.subtype P' φ' v' u w h hv' hw
  obtain ⟨e4, e6, -⟩ := hinv R₁.subtype
  have H := GlobalTheory.isHomothetic_scalePeriods Λ c⁻¹ (inv_ne_zero hc)
  have e : (Lf R₁.subtype).lattice = (GlobalTheory.scalePeriods Λ c⁻¹ (inv_ne_zero hc)).lattice := by
    refine GlobalTheory.lattice_eq_of_g₂_eq_of_g₃_eq ?_ ?_
    · refine mul_left_cancel₀ (by norm_num : (12 : ℂ) ≠ 0) ?_
      rw [← e4, H.g₂_eq, inv_pow, inv_inv, ← _root_.mul_assoc]
      exact h4
    · refine mul_left_cancel₀ (by norm_num : (216 : ℂ) ≠ 0) ?_
      rw [← e6, H.g₃_eq, inv_pow, inv_inv, ← _root_.mul_assoc]
      exact h6
  have hg' : P'.g = 1 := h.1.trans hg
  obtain ⟨u', hu', hd'⟩ := exists_holUnif_rescale u w hg' v' hw hw0 Λ hc
    (fun z ↦ by rw [← hL, e]; exact (H z).symm)
  exact ⟨P, P'.A, inferInstance, φ', P'.L, u', v, v', P'.isAb, hg' ▸ P'.smoothDim, h.2.1, hu', ht, ht', hv', hd'⟩

end GlobalTheory.LatticeFibre
