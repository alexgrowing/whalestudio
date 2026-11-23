import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XMemOne
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.Integral

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PD.XCover

namespace GlobalTheory.PD.XCover

attribute [local instance] MvPolynomial.gradedAlgebra

theorem injective_mvPolynomial_of_finite_of_ringKrullDim {k B : Type} [Field k] [CommRing B] {d : ℕ}
    (ψ : MvPolynomial (Fin d) k →+* B) (hψ : ψ.Finite) (hB : ringKrullDim B = d) :
    Function.Injective ψ := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  letI : Algebra (MvPolynomial (Fin d) k ⧸ RingHom.ker ψ) B := (RingHom.kerLift ψ).toAlgebra
  have hfin : (RingHom.kerLift ψ).Finite := by
    have e : ψ = (RingHom.kerLift ψ).comp (Ideal.Quotient.mk _) := by
      ext x <;> rfl
    exact RingHom.Finite.of_comp_finite (e ▸ hψ)
  haveI : Algebra.IsIntegral (MvPolynomial (Fin d) k ⧸ RingHom.ker ψ) B := ⟨hfin.to_isIntegral⟩
  have e1 : ringKrullDim B = ringKrullDim (MvPolynomial (Fin d) k ⧸ RingHom.ker ψ) :=
    ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective (RingHom.kerLift_injective ψ)
  have e2 : ringKrullDim (MvPolynomial (Fin d) k ⧸ RingHom.ker ψ) ≤
      ringKrullDim (MvPolynomial (Fin d) k ⧸ Ideal.span {r}) :=
    ringKrullDim_le_of_surjective _
      (Ideal.Quotient.factor_surjective (by rw [Ideal.span_singleton_le_iff_mem]; exact hr))
  have e3 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hr0)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at e3
  have e4 : (d : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin d) k ⧸ Ideal.span {r}) :=
    (hB.symm.trans e1).le.trans e2
  have h := (add_le_add e4 (le_refl (1 : WithBot ℕ∞))).trans e3
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h
  norm_cast at h
  omega

theorem ratioSec_eq_projSpace_ratio (d : ℕ) (i j : Fin (d + 1)) (h : j ≠ i) : ratioSec d i j = GlobalTheory.ProjSpace.ratio ℂ d i j := by
  have e := GlobalTheory.ProjSpace.chartAlgEquiv_X ℂ d i ⟨j, h⟩
  rw [GlobalTheory.ProjSpace.chartAlgEquiv_apply, GlobalTheory.ProjSpace.polyToAway, MvPolynomial.eval₂Hom_X'] at e
  exact e

theorem algebraicIndependent_rat : ∀ (d : ℕ) (Z : Scheme.{0}) [IsIntegral Z] (p : Z ⟶ Sp ℂ)
    [SmoothOfRelativeDimension d p] [inst : Algebra ℂ Z.functionField], inst = ffAlg p →
    ∀ (φ : Z ⟶ PSpace ℂ d) [IsFinite φ], φ ≫ PSpace.str ℂ d = p → (∀ i, genericPoint Z ∈ φ ⁻¹ᵁ chart d i) →
      AlgebraicIndependent ℂ (fun j : Fin d => rat φ 0 j.succ) := by
  intro d Z _ p _ inst hinst φ _ hφ hgen
  subst hφ
  obtain ⟨hU, hψ₀⟩ := (GlobalTheory.ProjSpace.isFinite_iff_pullRatio φ (U := fun i => φ ⁻¹ᵁ chart d i)
    (fun _ => rfl)).1 inferInstance 0
  set c := (GlobalTheory.QCoh.Qcqs.baseRingHom (φ ≫ PSpace.str ℂ d) (φ ⁻¹ᵁ chart d 0)).hom with hc
  set y := GlobalTheory.ProjSpace.pullRatio φ (φ ⁻¹ᵁ chart d 0) 0 le_rfl with hy
  let ψ : MvPolynomial (Fin d) ℂ →+* Γ(Z, φ ⁻¹ᵁ chart d 0) := MvPolynomial.eval₂Hom c (fun j => y j.succ)
  let σ : MvPolynomial (Fin (d + 1)) ℂ →+* MvPolynomial (Fin d) ℂ :=
    MvPolynomial.eval₂Hom MvPolynomial.C (Fin.cases 1 MvPolynomial.X)
  have hcomp : ψ.comp σ = MvPolynomial.eval₂Hom c y := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp [ψ, σ]
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [ψ, σ, y]
      · simp [ψ, σ]
  have hψ : ψ.Finite := RingHom.Finite.of_comp_finite (hcomp ▸ hψ₀)
  have hdim : ringKrullDim Γ(Z, φ ⁻¹ᵁ chart d 0) = d :=
    GlobalTheory.SmoothDim.ringKrullDim_affineOpen ℂ Z (φ ≫ PSpace.str ℂ d) d inferInstance _ hU ⟨_, hgen 0⟩
  have hinj : Function.Injective ψ := injective_mvPolynomial_of_finite_of_ringKrullDim ψ hψ hdim
  have hgerm : Function.Injective (Z.presheaf.germ (φ ⁻¹ᵁ chart d 0) (genericPoint Z) (hgen 0)).hom :=
    germ_injective_of_isIntegral Z _ (hgen 0)
  have key : (MvPolynomial.aeval (R := ℂ) (fun j : Fin d => rat φ 0 j.succ)).toRingHom =
      (Z.presheaf.germ (φ ⁻¹ᵁ chart d 0) (genericPoint Z) (hgen 0)).hom.comp ψ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_C, RingHom.comp_apply, ψ,
        MvPolynomial.eval₂Hom_C]
      subst hinst
      have e : (φ ≫ PSpace.str ℂ d).appLE ⊤ (φ ⁻¹ᵁ chart d 0) le_top =
          (φ ≫ PSpace.str ℂ d).appTop ≫ Z.presheaf.map (homOfLE le_top).op := by
        rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
        exact (Scheme.Hom.appLE_map _ _ _).symm
      rw [hc, GlobalTheory.QCoh.Qcqs.baseRingHom, CommRingCat.hom_comp, RingHom.comp_apply, e,
        CommRingCat.hom_comp, RingHom.comp_apply, TopCat.Presheaf.germ_res_apply]
      rfl
    · simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X, RingHom.comp_apply, ψ,
        MvPolynomial.eval₂Hom_X']
      rw [rat, dif_pos (hgen 0), hy, GlobalTheory.ProjSpace.pullRatio, ← ratioSec_eq_projSpace_ratio d 0 j.succ (Fin.succ_ne_zero j),
        Scheme.Hom.app_eq_appLE]
  rw [algebraicIndependent_iff_injective_aeval]
  have : ⇑(MvPolynomial.aeval (R := ℂ) (fun j : Fin d => rat φ 0 j.succ)) =
      ⇑((Z.presheaf.germ (φ ⁻¹ᵁ chart d 0) (genericPoint Z) (hgen 0)).hom.comp ψ) :=
    congrArg DFunLike.coe key
  rw [this]
  exact hgerm.comp hinj

end GlobalTheory.PD.XCover
