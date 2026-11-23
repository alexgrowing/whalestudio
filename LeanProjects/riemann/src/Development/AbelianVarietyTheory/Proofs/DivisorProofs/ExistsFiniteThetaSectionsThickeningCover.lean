import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermRatioAgreeSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfIsDominant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaImmersionTorusExtensionProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralThetaFamilyPrescribedLeadingTermStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreSectionValueEqUnitMulFourierTermStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCoordsLiftImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenFractionsProjSpaceImmersionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreTorusCoordinatesIsImmersionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreThetaSectionGermEqFourierRatioMulStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ClosedGen

theorem cst_eq_baseRingHom {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens) :
    (GlobalTheory.QCoh.Qcqs.baseRingHom f W).hom = GlobalTheory.AbLaw.cst f W := by
  rfl

end GlobalTheory.Mum.ClosedGen

open GlobalTheory.Mum.ClosedGen in

theorem GlobalTheory.Mum.exists_ratio_gen_closed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∃ (n : ℕ) (τ : Fin n → H0 U.LG.L k), ∀ w : (thickObj R (maximalIdeal R) 0 G).left, ∃ (j : Fin n) (i : Fin 1 → U.LG.L.ι) (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (r : Fin n → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin n) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P := by
  intro R _ _ _ hB D A G _ _ hG U
  obtain ⟨Y⟩ : Nonempty (Ext D.toPre) := inferInstance
  obtain ⟨S, k₁, hk₁⟩ := GlobalTheory.T.exists_theta_immersion_torus_extension_projective R hB D Y
  choose k₀f hk₀f using (GlobalTheory.T.exists_integralThetaFamily_prescribed_leadingTerm R hB D).1
  refine ⟨max 3 (max k₁ (S.sup k₀f)), le_max_left _ _, ?_⟩
  intro k hk
  have hk3 : 3 ≤ k := le_trans (le_max_left _ _) hk
  have hkk₁ : k₁ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkS : S.sup k₀f ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  obtain ⟨N, α, b, τ, hτ, hαb, himm⟩ := hk₁ k hkk₁
  have hF : ∀ j, ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead (α j) (b j) := fun j =>
    hk₀f (α j) k (le_trans (Finset.le_sup (hαb j).1) hkS) (b j)
  choose F hF using hF
  have hs : ∀ j, ∃ σ : H0 U.LG.L k, ∀ e, U.ExpandsAt e k σ (F j).f := fun j =>
    IntFam.exists_expandsAt R hB D A G U hG k (by omega) (F j)
  choose s hs using hs
  let T : Over (Sp R) := Over.mk ((thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0)
  obtain ⟨ξ, hξ⟩ := GlobalTheory.TorusCoord.exists_isPointOf (U.gt 0) (T := T) (𝟙 (thickObj R (maximalIdeal R) 0 G).left)
    (Category.id_comp _)
  let ψ : T ⟶ Y.H := (Y.Φ T).symm ξ
  have hψ : GlobalTheory.TorusCoord.IsPointOf (U.gt 0) (𝟙 (thickObj R (maximalIdeal R) 0 G).left) (Y.Φ T ψ) := by
    simp only [ψ, Equiv.apply_symm_apply]; exact hξ
  haveI hψi : IsImmersion ψ.left := GlobalTheory.T.closedFibre_torusCoordinates_isImmersion R D A G U.toUnifPre Y ψ hψ
  set p₀ := (fstG (maximalIdeal R) 0 G).left with hp₀
  let φ := ψ.left ≫ GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ
  haveI : IsImmersion φ := IsImmersion.comp _ _
  have hpre : ∀ j, φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N j = ψ.left ⁻¹ᵁ nonzeroLocus (τ j) := fun j => by
    simp only [φ, Scheme.Hom.comp_preimage, GlobalTheory.ProjSpace.toProj_preimage_chart]
  have hstr : φ ≫ PSpace.str R N = p₀ ≫ G.hom := by
    simp only [φ, Category.assoc, GlobalTheory.ProjSpace.toProj_str]
    rw [Over.w ψ]
    exact (pullback.condition).symm
  refine ⟨N + 1, s, fun w => ?_⟩
  have hw : ψ.left w ∈ ⨆ i, nonzeroLocus (τ i) := by rw [hτ]; trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hw
  obtain ⟨J, hJ⟩ := GlobalTheory.TorusCoord.exists_good' U.LG.isLB w
  let i : Fin 1 → U.LG.L.ι := fun _ => J (p₀ ≫ 𝟙 G.left)
  have hi : p₀ w ∈ secChart U.LG.L i := hJ.mem (fun _ : Fin 1 => 𝟙 G.left) p₀
  have hφw : φ w ∈ GlobalTheory.ProjSpace.chart R N j := by
    show w ∈ φ ⁻¹ᵁ GlobalTheory.ProjSpace.chart R N j
    rw [hpre]; exact hj
  obtain ⟨W, hW, hwW, hWV, hWa, hgen⟩ := GlobalTheory.T.exists_affineOpen_fractions_projSpace_immersion R N _ φ inferInstance w (p₀ ⁻¹ᵁ secChart U.LG.L i) j hi hφw
  have hWψ : W ≤ ψ.left ⁻¹ᵁ nonzeroLocus (τ j) := hW.trans (hpre j).le
  have hr : ∀ l, GlobalTheory.ProjSpace.pullRatio φ W j hW l =
      (ψ.left.appLE (nonzeroLocus (τ j)) W hWψ).hom (GlobalTheory.ProjSpace.secRatio (τ j) (τ l)) := by
    intro l
    rw [← GlobalTheory.ProjSpace.pullRatio_toProj Y.H.hom τ hτ j l, GlobalTheory.ProjSpace.appLE_pullRatio]
  refine ⟨j, i, W, GlobalTheory.ProjSpace.pullRatio φ W j hW, hwW, hWa, hWV, fun y hy => ?_, fun g => ?_⟩
  · have hyψ : ψ.left y ∈ nonzeroLocus (τ j) := hWψ hy
    obtain ⟨hu, hl⟩ := GlobalTheory.T.closedFibre_thetaSectionGerm_eq_fourierRatio_mul R D A G U.toUnifPre Y ψ hψ k (N + 1) α b τ F s (fun j => (hαb j).2) hF
      (fun j => hs j 0) y j i hyψ (hWV hy)
    refine ⟨hu, fun l => ?_⟩
    rw [hl l, hr l, gs_appLE _ _ _ _ (𝟙 _) y hy, Category.id_comp]
  · obtain ⟨P, Q, hQ, hPQ⟩ := hgen g
    have hc : (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str R N) W).hom = GlobalTheory.AbLaw.cst (p₀ ≫ G.hom) W := by
      rw [hstr]; exact cst_eq_baseRingHom _ _
    rw [hc] at hQ hPQ
    exact ⟨P, Q, hQ, hPQ⟩

end
