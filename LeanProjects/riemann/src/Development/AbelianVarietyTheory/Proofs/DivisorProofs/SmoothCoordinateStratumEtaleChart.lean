import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCoordinatesOnOpenOfIsTopFormFrameStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsWeaklyRegularMapCAppendMapLinForm
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
open GlobalTheory.LogPair TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PairStep

theorem smooth_quotient_of_isEtCoord (Y : Scheme.{0}) (q : Y ⟶ Sp ℂ) (n : ℕ) (U : Y.Opens) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n))
    (hE : IsEtCoord q U z) :
    ((Ideal.Quotient.mk (Ideal.span (z '' (J : Set (Fin n))))).comp (algX q U)).Smooth := by
  let A := MvPolynomial (Fin n) ℂ
  let B := Γ(Y, U)
  let φ : A →+* B := MvPolynomial.eval₂Hom (cstOn q U) z
  letI : Algebra A B := φ.toAlgebra
  haveI : Algebra.Etale A B := RingHom.etale_algebraMap.1 hE
  let I : Ideal A := Ideal.span (MvPolynomial.X '' (J : Set (Fin n)))
  have hI : I.map (algebraMap A B) = Ideal.span (z '' (J : Set (Fin n))) := by
    rw [Ideal.map_span, Set.image_image]
    congr 1
    ext x
    simp only [RingHom.algebraMap_toAlgebra, φ, Set.mem_image, Finset.mem_coe]
    constructor <;> rintro ⟨j, hj, rfl⟩ <;> exact ⟨j, hj, by rw [MvPolynomial.eval₂Hom_X']⟩
  have h1 : (algebraMap ℂ (A ⧸ I)).Smooth := by
    rw [RingHom.smooth_algebraMap]
    haveI : Algebra.Smooth ℂ (MvPolynomial {x // x ∉ (J : Set (Fin n))} ℂ) := ⟨inferInstance, inferInstance⟩
    exact Algebra.Smooth.of_equiv (quotientSpanXEquiv ℂ (J : Set (Fin n))).symm
  have h2 : (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B)).Smooth := by
    rw [RingHom.smooth_algebraMap]; infer_instance
  let e : ((A ⧸ I) ⊗[A] B) ≃+* B ⧸ Ideal.span (z '' (J : Set (Fin n))) :=
    ((Algebra.TensorProduct.comm A (A ⧸ I) B).toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm.toRingEquiv).trans
      (Ideal.quotEquivOfEq hI)
  have h12 : ((algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B)).comp (algebraMap ℂ (A ⧸ I))).Smooth :=
    RingHom.Smooth.comp h1 h2
  have h3 : (e.toRingHom.comp ((algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B)).comp (algebraMap ℂ (A ⧸ I)))).Smooth :=
    have he : e.toRingHom.Smooth := RingHom.Smooth.of_bijective e.bijective
    RingHom.Smooth.comp h12 he
  convert h3 using 1
  ext c
  simp only [RingHom.comp_apply]
  have k1 : algebraMap ℂ (A ⧸ I) c = Ideal.Quotient.mk I (MvPolynomial.C c) := rfl
  have k2 : algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B) (Ideal.Quotient.mk I (MvPolynomial.C c)) =
      (1 : A ⧸ I) ⊗ₜ[A] (algX q U c) := by
    have hm : Ideal.Quotient.mk I (MvPolynomial.C c) = (MvPolynomial.C c : A) • (1 : A ⧸ I) := by
      rw [Algebra.smul_def, mul_one]; rfl
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hm,
      TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    congr 1
    simp [RingHom.algebraMap_toAlgebra, φ]
    rfl
  have k3 : (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm (algX q U c ⊗ₜ[A] (1 : A ⧸ I)) =
      Ideal.Quotient.mk _ (algX q U c) := by
    rw [AlgEquiv.symm_apply_eq, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
  rw [k1, k2]
  simp only [e, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.trans_apply,
    AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.comm_tmul, k3,
    Ideal.quotEquivOfEq_mk]

theorem smooth_coordStratum : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (U : Y.Opens) (z : Fin n → Γ(Y, U)), IsFrame (dOn q z) → ∀ J : Finset (Fin n), ((Ideal.Quotient.mk (Ideal.span (z '' (J : Set (Fin n))))).comp (algX q U)).Smooth := by
  intro Y _ _ q n _ U z hF J
  exact smooth_quotient_of_isEtCoord Y q n U z J (GlobalTheory.T.isEtaleCoordinatesOnOpen_of_isTopFormFrame ℂ Y q n U z hF).2

end GlobalTheory.PairStep
