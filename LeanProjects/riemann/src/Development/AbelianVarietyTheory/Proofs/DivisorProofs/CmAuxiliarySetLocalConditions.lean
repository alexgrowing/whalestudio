import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisFractionFieldIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearDualBasisBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearFiltrationBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmOrderUniformizationEndomorphismsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FilEig

theorem fil_baseChange_eq_iSup_eigK : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)),
      (Submodule.map eH.toLinearMap (Fil X₀.A)).baseChange (FractionRing R) =
        ⨆ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) := by
  intro hPC hDR hDC E _ _ _ _ I _ d φ hφ 𝔣 h𝔣 l _ Q hQ hQl y hy lam 𝔠 R _ hR X₀ X U p cm hpull hrm hα j hj φK hφK n eH
  choose α hαm hαp hαu using hα
  have hcm : ∀ a, IsMonHom (cm.act a) := cm.hom
  have hgrp : IsGrpPullback X.A X₀.A (spMap (algebraMap R ℂ)) p := hpull.grp
  obtain ⟨hbc, hF1⟩ := hDR.2.2.1 R X₀.A _ X₀.ab X₀.dim ℂ X.A p hgrp
  obtain ⟨hfin, hproj, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim hDR.1 X₀.ab X₀.dim
  obtain ⟨-, hcompl, -⟩ := hDR.2.1 R X₀.A _ X₀.ab X₀.dim
  have hcorr : ∀ (h : HdR X₀.A) c, hbc.bcMap h ((GlobalTheory.Published.AbelianDeRham.bcMor hgrp).pull c) = algebraMap R ℂ (h c) :=
    fun h c ↦ (hbc.corr_iff.2 rfl) c
  let β : (Fin n → R) →ₛₗ[algebraMap R ℂ] HdR X.A := hbc.bcMap.comp eH.symm.toLinearMap
  have hc0 : condQ 𝔣 Q ≠ ⊥ := by
    rw [condQ, Ne, Ideal.mul_eq_bot, not_or]
    refine ⟨h𝔣.1, ?_⟩
    rw [← Ideal.zero_eq_bot, Finset.prod_eq_zero_iff]
    push_neg
    intro q _
    rw [Ideal.zero_eq_bot]
    exact q.ne_bot
  have hC := GlobalTheory.T.cm_order_uniformization_endomorphisms hPC hDR E I φ hφ.2.2.2.2.2.2.1 (condQ 𝔣 Q) hc0 𝔠 _ X U α hαu
  refine GlobalTheory.T.lattice_basis_fraction_field_independent j hj β ?_ _ (fun a ↦ push (dp0 ℂ) (𝟙 _) (α a)) ?_ _ (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) ?_
  · exact GlobalTheory.T.semilinear_dual_basis_base_change (GlobalTheory.Published.AbelianDeRham.bcMor hgrp).pull hbc eH _ (fun k c ↦ hcorr _ c)
  · intro a x
    have e := GrpMor.Corr.push (GlobalTheory.Published.AbelianDeRham.bcMor hgrp) (cm.act a) (α a)
      (hαp a).symm (hbc.corr_iff.2 rfl : (GlobalTheory.Published.AbelianDeRham.bcMor hgrp).Corr (eH.symm x) (hbc.bcMap (eH.symm x)))
    have e2 := hbc.corr_iff.1 e
    simp only [β, LinearMap.comp_apply, LinearEquiv.coe_coe, RingEquiv.toRingHom_eq_coe, RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply]
    rw [act_apply]
    simpa [LinearEquiv.conjRingEquiv, LinearEquiv.conj_apply] using e2
  · have himg : β '' (Submodule.map eH.toLinearMap (Fil X₀.A) : Set (Fin n → R)) = hbc.bcMap '' (Fil X₀.A : Set (HdR X₀.A)) := by
      ext v
      simp [β]
    rw [himg, Fil, GlobalTheory.T.semilinear_filtration_base_change (GlobalTheory.Published.AbelianDeRham.bcMor hgrp).pull hbc _ hcompl _ hF1 hbc.bcMap hcorr]
    change Fil X.A = _
    rw [hC]
    congr 1
    ext i : 1
    congr 1
    ext a : 1
    congr 1
    show _ = j (φK i _)
    rw [← RingHom.comp_apply, hφK i]
    rfl

end GlobalTheory.FilEig
