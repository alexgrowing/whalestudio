import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealGeneratedPrimeToLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormExistsForCmObjectStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamRankEqCmDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationFormOverDvrPrimeToLStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetGaloisDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetLocalConditionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetLevelStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetReductionGoodStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

noncomputable section

namespace GlobalTheory.LatModel

theorem cmLattice_of_model : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
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
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i) →
    ∀ (hL : LieExact X₀.A) (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)),
    ∃ (c₀ : 𝔠.elt) (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)), (c₀ : FR E) ≠ 0 ∧
      (∀ c : 𝔠.elt, ∃ (n : ℕ) (t : 𝓞 (FR E)), n.Coprime l ∧ n • c = t • c₀) ∧
      IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) ((2 : R) • ψ₀) ∧
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.IsCMLattice (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (Submodule.map eH.toLinearMap (Fil X₀.A)) (ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap : LinearMap.BilinForm R (Fin n → R)) ∧
      ∀ i (g : Fin n → R), GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigLat (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) = Submodule.span R {g} →
        ∃ r : Rˣ, ∀ x, ψ₀ (eH.symm g) x = (r : R) * e i (hL.toLie X₀.rm x) := by
  intro hPC hDR hDC hPM E _ _ _ _ I _ d φ hφ 𝔣 h𝔣 l _ Q hQ hQl y hy lam 𝔠 R _ hR X₀ X U p cm hpull hcm hα j hj φK hφK
    e a he hL n eH
  obtain ⟨c₀, hc₀, hgen⟩ := GlobalTheory.T.fractional_ideal_generated_prime_to_l (FR E) 𝔠 l
  obtain ⟨ψ₀, hcorr, hpol⟩ := GlobalTheory.T.polarization_form_exists_for_cm_object hDR (FR E) 𝔠 R X₀ c₀
  have hunit : ∀ m : ℕ, m.Coprime l → IsUnit (m : R) := by
    intro m hm
    have hm0 : (m : ℚ) ≠ 0 := by
      have : m ≠ 0 := by
        rintro rfl
        exact (Fact.out : l.Prime).one_lt.ne' (Nat.coprime_zero_left l |>.mp hm)
      exact_mod_cast this
    have hv : 0 ≤ padicValRat l ((m : ℚ)⁻¹) := by
      rw [padicValRat.inv, padicValRat.of_nat]
      have : padicValNat l m = 0 :=
        padicValNat.eq_zero_of_not_dvd fun h ↦ (Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).1 hm.symm h
      simp [this]
    have hmem := hR.2.2.1 ((m : ℚ)⁻¹) hv
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
    have : ((m : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hm0
    simp only [Subring.coe_mul, Subring.coe_natCast, Subring.coe_one]
    rw [Rat.cast_inv, Rat.cast_natCast] at *
    exact mul_inv_cancel₀ (by simpa using this)
  have hbij : Function.Bijective ψ₀ := GlobalTheory.T.polarization_form_over_dvr_prime_to_l hDR hDC (FR E) 𝔠 l R hunit X₀ c₀ hc₀ hgen ψ₀ hcorr
  have hadj := GlobalTheory.T.cm_auxiliary_set_level_structure hPC hDR hDC E I d φ hφ 𝔣 h𝔣 l Q hQ hQl y hy lam 𝔠 R hR X₀ X U p cm hpull hcm hα j hj φK hφK c₀ ψ₀ hc₀ hpol
  have hFil := GlobalTheory.T.cm_auxiliary_set_local_conditions hPC hDR hDC E I d φ hφ 𝔣 h𝔣 l Q hQ hQl y hy lam 𝔠 R hR X₀ X U p cm hpull hcm hα j hj φK hφK n eH
  have h2 : (2 : R) ≠ 0 := two_ne_zero
  refine ⟨c₀, ψ₀, hc₀, hgen, hpol, ⟨inferInstance, inferInstance, ?_,
    GlobalTheory.T.cm_auxiliary_set_galois_descent hPC hDR hDC E I d φ hφ 𝔣 h𝔣 l Q hQ hQl y hy lam 𝔠 R hR X₀ X U p cm hpull hcm hα j hj φK hφK n eH, ?_, hFil, ?_, ?_, ?_⟩,
    GlobalTheory.T.cm_auxiliary_set_reduction_good hPC hDR hDC E I d φ hφ 𝔣 h𝔣 l Q hQ hQl y hy lam 𝔠 R hR X₀ X U p cm hpull hcm hα j hj φK hφK e a he hL n eH c₀ ψ₀
      hc₀ hpol hbij hadj hFil⟩
  · rw [Module.finrank_fin_fun]
    exact GlobalTheory.T.de_rham_rank_eq_cm_degree hDR E 𝔠 R X₀ n eH
  · intro x h hx hxh
    obtain ⟨k, hk, hkh⟩ := Submodule.mem_map.1 hxh
    refine Submodule.mem_map.2 ⟨eH.symm h, ?_, by simp⟩
    have hk' : k = x • eH.symm h := by
      apply eH.injective
      rw [map_smul, LinearEquiv.apply_symm_apply]
      exact hkh
    subst hk'
    rw [Fil, Submodule.mem_dualAnnihilator] at hk ⊢
    intro w hw
    have := hk w hw
    rw [LinearMap.smul_apply, smul_eq_mul] at this
    exact (mul_eq_zero.1 this).resolve_left hx
  · have : ⇑(ψ₀.compl₁₂ eH.symm.toLinearMap eH.symm.toLinearMap) =
        ⇑eH.symm.dualMap ∘ ⇑ψ₀ ∘ ⇑eH.symm := by
      funext x
      rfl
    rw [this]
    exact eH.symm.dualMap.bijective.comp (hbij.comp eH.symm.bijective)
  · intro x
    have := hpol.isAlt (eH.symm x)
    simp only [LinearMap.smul_apply, smul_eq_mul] at this
    simpa using (mul_eq_zero.1 this).resolve_left h2
  · intro a' b' hab h h'
    show ψ₀ (eH.symm (eH (act (dp0 R) (𝟙 _) cm a' (eH.symm h)))) (eH.symm h') =
      ψ₀ (eH.symm h) (eH.symm (eH (act (dp0 R) (𝟙 _) cm b' (eH.symm h'))))
    rw [eH.symm_apply_apply, eH.symm_apply_apply]
    exact hadj a' b' hab (eH.symm h) (eH.symm h')

end GlobalTheory.LatModel
