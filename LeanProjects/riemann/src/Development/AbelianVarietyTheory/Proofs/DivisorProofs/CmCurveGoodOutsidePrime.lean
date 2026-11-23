import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CmCurveGoodOutsidePrimePremises
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqrtNegPrimeKernelDatumOfIntegersLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescaledLatticeProdDerivWeierstrassPMemStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralOfModelAtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationSubringComplexOverPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralJOfNonrealMultiplierStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegersLatticeInvariantsNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticTwistCmCurveModelDiscriminantNegPrimeCuStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMinimalOfDiscrEqUnitMulNegCubeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastNotMemCubePrimeAdjoinJInvariantSqrtNegStatement

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField

namespace GlobalTheory.CMModel

theorem shortTwist_Δ (d a b : ℂ) :
    (shortTwist d a b).Δ = d ^ 6 * (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).Δ := by
  simp only [shortTwist, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem shortTwist_c₄ (d a b : ℂ) :
    (shortTwist d a b).c₄ = d ^ 2 * (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).c₄ := by
  simp only [shortTwist, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

theorem shortTwist_j {d a b : ℂ} (hd : d ≠ 0) [(shortTwist d a b).IsElliptic]
    [(⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).IsElliptic] :
    (shortTwist d a b).j = (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).j := by
  have h0 : (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ).Δ ≠ 0 :=
    (WeierstrassCurve.IsElliptic.isUnit (W := (⟨0, 0, 0, a, b⟩ : WeierstrassCurve ℂ))).ne_zero
  simp only [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ',
    shortTwist_Δ, shortTwist_c₄]
  field_simp

theorem j_congr_of_eq {W W' : WeierstrassCurve ℂ} (h : W = W') [W.IsElliptic] [W'.IsElliptic] :
    W.j = W'.j := by
  subst h; rfl

end GlobalTheory.CMModel

namespace GlobalTheory.Published

theorem cmCurveGoodOutsidePrime : CMCurveGoodOutsidePrimeSt := by
  intro p hp h4 h3
  obtain ⟨L₀, hL₀⟩ := exists_isIntegersLattice (p := p) hp.pos
  obtain ⟨-, -, hms⟩ := GlobalTheory.T.integersLattice_g2_g3_ne_zero_and_mulStable p L₀ hp h3 hL₀
  have him : (sqrtNegNat p).im ≠ 0 := by
    simp only [sqrtNegNat, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
      Complex.I_re, mul_one, mul_zero, add_zero]
    exact (Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)).ne'
  have hjint := GlobalTheory.T.isIntegral_j_of_nonreal_multiplier L₀ (sqrtNegNat p) hms him
  have hjQ : IsIntegral ℚ (latticeCurve L₀).j := hjint.tower_top
  haveI : FiniteDimensional ℚ ℚ⟮(latticeCurve L₀).j⟯ := IntermediateField.adjoin.finiteDimensional hjQ
  haveI hNF : NumberField ℚ⟮(latticeCurve L₀).j⟯ := NumberField.of_module_finite ℚ _
  obtain ⟨L₁, t₁, hD₁, hj₁⟩ := GlobalTheory.T.exists_sqrtNegPrimeKernelDatum_of_integersLattice p L₀ hp h4 h3 hL₀
  obtain ⟨L, t, hD, hj, hsq⟩ := GlobalTheory.T.exists_rescaled_lattice_prodDerivWeierstrassP_mem p _ L₁ t₁ hp h4 h3 hD₁
  set F := ℚ⟮(latticeCurve L₀).j⟯ with hFdef
  have hg₂ : -L.g₂ / 4 ∈ F := div_mem (neg_mem hD.g₂_mem) (ofNat_mem _ 4)
  have hg₃ : -L.g₃ / 4 ∈ F := div_mem (neg_mem hD.g₃_mem) (ofNat_mem _ 4)
  let dF : F := if p % 8 = 3 then 1 else -(p : F)
  let dC : ℂ := if p % 8 = 3 then 1 else -(p : ℂ)
  have hdC : ((dF : F) : ℂ) = dC := by
    simp only [dF, dC]; split_ifs <;> simp
  have hdC0 : dC ≠ 0 := by
    simp only [dC]; split_ifs
    · exact one_ne_zero
    · exact neg_ne_zero.mpr (by exact_mod_cast hp.ne_zero)
  let A : WeierstrassCurve F := shortTwist dF ⟨-L.g₂ / 4, hg₂⟩ ⟨-L.g₃ / 4, hg₃⟩
  have hmap : A.map (algebraMap F ℂ) = shortTwist dC (-L.g₂ / 4) (-L.g₃ / 4) := by
    rw [← hdC]
    ext <;> simp [A, shortTwist, WeierstrassCurve.map]
  have hlat : (⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ : WeierstrassCurve ℂ) = latticeCurve L := rfl
  have hΔA : A.Δ ≠ 0 := by
    intro h0
    have := congrArg (algebraMap F ℂ) h0
    rw [← WeierstrassCurve.map_Δ, hmap, shortTwist_Δ, hlat, map_zero] at this
    exact mul_ne_zero (pow_ne_zero _ hdC0) (latticeCurve_Δ_ne_zero L) this
  haveI hE : A.IsElliptic := ⟨Ne.isUnit hΔA⟩
  have hmin : HasMinimalDiscriminant A (-(p : F) ^ 3) := by
    intro w
    obtain ⟨V, hV⟩ := GlobalTheory.T.exists_valuationSubring_complex_restrict_eq_at_prime F w
    have hloc := GlobalTheory.T.quadraticTwist_cmCurve_model_discriminant_negPrimeCube p F L t hp h4 h3 hD hsq V
    have hD0 : (-(p : F) ^ 3) ≠ 0 :=
      neg_ne_zero.mpr (pow_ne_zero _ (by exact_mod_cast hp.ne_zero))
    have hmod : ModelAt V F (A.map (algebraMap F ℂ)) ((-(p : F) ^ 3 : F) : ℂ) := by
      rw [hmap]
      convert hloc using 1
      push_cast; rfl
    obtain ⟨C, u, hI, hΔ⟩ := GlobalTheory.T.exists_variableChange_isIntegral_of_modelAt F w V A _ hV hD0 hmod
    have hram := GlobalTheory.T.natCast_notMem_cube_prime_adjoin_jInvariant_sqrtNeg p L₀ w hp hL₀
    exact ⟨C, u, GlobalTheory.T.isMinimal_of_discr_eq_unit_mul_neg_prime_cube p F w (C • A) u hram hI hΔ, hΔ⟩
  refine ⟨F, hNF, A, ⟨hNF, hE, L₀, hL₀, rfl, ?_, hmin.hasGoodReductionOutside⟩, hmin⟩
  have e1 : ((A.j : F) : ℂ) = (A.map (algebraMap F ℂ)).j := (A.map_j (algebraMap F ℂ)).symm
  haveI : (shortTwist dC (-L.g₂ / 4) (-L.g₃ / 4)).IsElliptic := hmap ▸ inferInstance
  haveI : (⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩ : WeierstrassCurve ℂ).IsElliptic :=
    inferInstanceAs (latticeCurve L).IsElliptic
  rw [e1, j_congr_of_eq hmap, shortTwist_j hdC0, j_congr_of_eq hlat, hj, hj₁]

end GlobalTheory.Published
