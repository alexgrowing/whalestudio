import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SExpDefs
import GroundTheory.AutomorphicForms.GL2.GodementSectionFactor
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
import GroundTheory.LocalFields.LocalZetaGauss
import GroundTheory.LocalFields.LocalZeta
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ArchInt
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.UnitaryTransvectionZeroSecondMemClosure
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.HcToIdele
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ArchimedeanIntegralHolds
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.CoefficientDivisorHolds
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.QuasiCharConductorLoc
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.InverseSubstitutionHolds
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.LocalIntegralOfSubstitution
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.CharacterProductHolds
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.CharacterPositiveHolds
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.TateThesis.FiniteOrderParams
import GroundTheory.GlobalFields.WeilGroups.QuasiCharacterDecomposition

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published GroundTheory.LocalField

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

open GroundTheory.Automorphic.GodementSection

omit [IsTotallyReal F] in
theorem ω_split (ω : HChar F) (τ : IdeleGroup F) :
    ((ω.1 τ : ℂˣ) : ℂ) = ωI ω (toInfinite F τ) * ωF ω (toFinite F τ) := by
  conv_lhs => rw [← ofFinite_mul_ofInfinite τ]
  rw [map_mul, Units.val_mul, mul_comm]
  rfl

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

open GroundTheory.Automorphic.GodementSection

theorem pInf_yAd (y : (UpperTheory.V.TR.Rinf F)ˣ) (yf : (Af F)ˣ) : UpperTheory.V.TR.pInf F (yAd y yf) = y.val := by
  have hs : ∀ x, UpperTheory.V.TR.pInf F (UpperTheory.V.TR.sInf F x) = x := fun x => (UpperTheory.V.TR.infEq F).symm_apply_apply x
  have hf : ∀ x, UpperTheory.V.TR.pInf F (sFin F x) = 0 := fun x => map_zero (UpperTheory.V.TR.infEq F).symm
  have h1 : UpperTheory.V.TR.pInf F ((UpperTheory.V.TR.infId F y : (Ad F)ˣ) : Ad F) = y.val := by
    change UpperTheory.V.TR.pInf F (1 - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F y.val) = y.val
    rw [map_add, map_sub, map_one, hs, hs]; ring
  have h2 : UpperTheory.V.TR.pInf F ((finId F yf : (Ad F)ˣ) : Ad F) = 1 := by
    change UpperTheory.V.TR.pInf F (1 - sFin F 1 + sFin F (yf : Af F)) = 1
    rw [map_add, map_sub, map_one, hf, hf]; ring
  rw [yAd, Units.val_mul, map_mul, h1, h2, mul_one]

theorem pFin_yAd (y : (UpperTheory.V.TR.Rinf F)ˣ) (yf : (Af F)ˣ) : pFin F (yAd y yf) = (yf : Af F) := by
  have h1 : pFin F ((UpperTheory.V.TR.infId F y : (Ad F)ˣ) : Ad F) = 1 := by
    change pFin F (1 - UpperTheory.V.TR.sInf F 1 + UpperTheory.V.TR.sInf F y.val) = 1
    rw [map_add, map_sub, map_one]
    change (1 : Af F) - 0 + 0 = 1
    ring
  have h2 : pFin F ((finId F yf : (Ad F)ˣ) : Ad F) = yf := by
    change pFin F (1 - sFin F 1 + sFin F (yf : Af F)) = yf
    rw [map_add, map_sub, map_one]
    change (1 : Af F) - 1 + (yf : Af F) = yf
    ring
  rw [yAd, Units.val_mul, map_mul, h1, h2, one_mul]

theorem reAt_eq' (v : InfinitePlace F) (x : F) :
    reAt v x = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  rw [reAt, ← InfinitePlace.embedding_of_isReal_apply (IsTotallyReal.isReal v), Complex.ofReal_re]

theorem pInf_alg' (v : InfinitePlace F) (x : F) : UpperTheory.V.TR.pInf F (algebraMap F (Ad F) x) v = reAt v x := by
  rw [reAt_eq']
  change InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v)
    (algebraMap F (InfiniteAdeleRing F) x v) = _
  simp

theorem pInf_tau (τ : IdeleGroup F) (v : InfinitePlace F) :
    UpperTheory.V.TR.pInf F (τ : Ad F) v = rc (toInfinite F τ) v := rfl

theorem pInf_tau_inv (τ : IdeleGroup F) (v : InfinitePlace F) :
    UpperTheory.V.TR.pInf F ((τ⁻¹ : IdeleGroup F) : Ad F) v = (rc (toInfinite F τ) v)⁻¹ := by
  rw [← pInf_tau]
  refine eq_inv_of_mul_eq_one_left ?_
  rw [← Pi.mul_apply, ← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one, Pi.one_apply]

theorem kernF_split (c : HeightOneSpectrum (𝓞 F) → ℕ) (y : (UpperTheory.V.TR.Rinf F)ˣ) (yf : (Af F)ˣ) (ξ : F)
    (τ : IdeleGroup F) :
    kernF c ((τ : Ad F) * yAd y yf) (τ⁻¹ • algebraMap F (Ad F) ξ) =
      archK y ξ (toInfinite F τ) * finK c yf ξ (toFinite F τ) := by
  have hA : ∀ v, UpperTheory.V.TR.pInf F ((τ : Ad F) * yAd y yf) v = rc (toInfinite F τ) v * y.val v := by
    intro v
    rw [map_mul, Pi.mul_apply, pInf_yAd, pInf_tau]
  have hZ : ∀ v, UpperTheory.V.TR.pInf F (τ⁻¹ • algebraMap F (Ad F) ξ) v = (rc (toInfinite F τ) v)⁻¹ * reAt v ξ := by
    intro v
    rw [Units.smul_def, smul_eq_mul, map_mul, Pi.mul_apply, pInf_tau_inv, pInf_alg']
  have hA' : pFin F ((τ : Ad F) * yAd y yf) = (toFinite F τ : Af F) * (yf : Af F) := by
    rw [map_mul, pFin_yAd]; rfl
  have hZ' : pFin F (τ⁻¹ • algebraMap F (Ad F) ξ) =
      (((toFinite F τ)⁻¹ : (Af F)ˣ) : Af F) * algebraMap F (Af F) ξ := by
    rw [Units.smul_def, smul_eq_mul, map_mul, ← map_inv]; rfl
  rw [kernF, archK, finK, hA', hZ']
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [hA, hZ]
  push_cast
  ring_nf

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

open GroundTheory.Automorphic.GodementSection

omit [IsTotallyReal F] in
theorem ordAt_eq_zero {b : (Af F)ˣ} {w : HeightOneSpectrum (𝓞 F)} (h : IsIntegralUnitAt b w) : ordAt b w = 0 := by
  have hb0 : pLoc F w (b : Af F) ≠ 0 := by
    intro h0
    have := congrArg (fun a : Af F => pLoc F w a) b.mul_inv
    simp only [map_mul, map_one, h0, zero_mul] at this
    exact zero_ne_one this
  have h1 : Valued.v (pLoc F w (b : Af F)) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h.1
  have h2 : Valued.v (pLoc F w ((b⁻¹ : (Af F)ˣ) : Af F)) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h.2
  have hm : pLoc F w (b : Af F) * pLoc F w ((b⁻¹ : (Af F)ˣ) : Af F) = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  have h3 : Valued.v (pLoc F w (b : Af F)) = 1 := by
    refine le_antisymm h1 ?_
    have := congrArg Valued.v hm
    rw [map_mul, map_one] at this
    calc (1 : WithZero (Multiplicative ℤ)) = _ := this.symm
      _ ≤ Valued.v (pLoc F w (b : Af F)) := mul_le_of_le_one_right' h2
  have := valued_eq_exp_neg_ord hb0
  rw [h3, ← WithZero.exp_zero, WithZero.exp_inj] at this
  unfold ordAt
  omega

omit [IsTotallyReal F] in
theorem isIntegralUnitAt_mul {b b' : (Af F)ˣ} {w : HeightOneSpectrum (𝓞 F)} (h : IsIntegralUnitAt b w)
    (h' : IsIntegralUnitAt b' w) : IsIntegralUnitAt (b * b') w := by
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul]
    exact mul_mem h.1 h'.1
  · rw [mul_inv_rev, Units.val_mul]
    exact mul_mem h'.2 h.2

omit [IsTotallyReal F] in
theorem pLoc_unit_ne_zero (b : (Af F)ˣ) (w : HeightOneSpectrum (𝓞 F)) : pLoc F w (b : Af F) ≠ 0 := by
  intro h0
  have := congrArg (fun a : Af F => pLoc F w a) b.mul_inv
  simp only [map_mul, map_one, h0, zero_mul] at this
  exact zero_ne_one this

theorem fin_int (hLI : LocInt) (hFS : FinSplit) (hOP : OmegaProd) (hCD : CoefDiv) (hR : LocRam)
    (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (H : Hyp ω c) :
    ∃ Cf : ℂ, Cf ≠ 0 ∧ ∀ (yf : (Af F)ˣ) (ξ : Fˣ),
      Integrable (fun b => finK c yf (ξ : F) b * (ωF ω b)⁻¹) (finiteIdeleMeasure F) ∧
      ∫ b, finK c yf (ξ : F) b * (ωF ω b)⁻¹ ∂finiteIdeleMeasure F =
        Cf * (ωF ω (xiF ξ))⁻¹ * coefAt (divS ω c) (algebraMap F (Af F) (ξ : F) * (yf : Af F)) := by
  classical
  have hfin0 : {w : HeightOneSpectrum (𝓞 F) | c w ≠ 0 ∨ dd w ≠ 0}.Finite := by
    refine (L2.finite_support H).union ((Ideal.finite_factors (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F))).subset ?_)
    intro w hw
    have hw' : ordI w (differentIdeal ℤ (𝓞 F)) ≠ 0 := by
      intro h0
      apply hw
      simp [dd, h0]
    exact (Associates.count_ne_zero_iff_dvd (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F)) w.irreducible).1 hw'
  set S0 := hfin0.toFinset with hS0
  refine ⟨∏ v ∈ S0, cst ω c v, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro v _
    unfold cst
    split_ifs with hcv
    · exact zpow_ne_zero _ (Units.ne_zero _)
    · exact (hR F ω c H v hcv).2
  intro yf ξ
  set S : Finset (HeightOneSpectrum (𝓞 F)) := S0 ∪ (finite_setOf_not_isIntegralUnitAt yf).toFinset ∪
    (finite_setOf_not_isIntegralUnitAt (xiF ξ)).toFinset with hSdef
  have hS : ∀ w ∉ S, c w = 0 ∧ dd w = 0 ∧ IsIntegralUnitAt yf w ∧ IsIntegralUnitAt (xiF ξ) w := by
    intro w hw
    refine ⟨?_, ?_, ?_, ?_⟩ <;> by_contra hcon <;> apply hw <;> simp [hSdef, hS0, hcon]
  have hloc := fun v => hLI F ω c H yf ξ v
  obtain ⟨hint, heq⟩ := hFS F ω c H yf ξ S hS (fun v => (hloc v).1)
  refine ⟨hint, ?_⟩
  rw [heq, Finset.prod_congr rfl (fun v _ => (hloc v).2), Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  have hxi : ωF ω (xiF ξ) =
      ∏ v ∈ S, ((ω.loc v (Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom ξ) : ℂˣ) : ℂ) := by
    rw [hOP F ω c H (xiF ξ) S (fun w hw => ⟨(hS w hw).1, (hS w hw).2.2.2⟩)]
    refine Finset.prod_congr rfl fun v _ => ?_
    congr 3
  rw [← hxi]
  set m : HeightOneSpectrum (𝓞 F) → ℤ := fun w => ordAt (xiF ξ * yf) w + dd w with hm
  have hite : ∀ v ∈ S, (if ordAt (xiF ξ * yf) v + dd v < 0 then 0 else
      cst ω c v * ∑ j ∈ Finset.range ((ordAt (xiF ξ * yf) v + dd v).toNat + 1), chiW ω c v ^ j) =
      if 0 ≤ m v then cst ω c v * ∑ j ∈ Finset.range ((m v).toNat + 1), chiW ω c v ^ j else 0 := by
    intro v _
    by_cases h0 : 0 ≤ ordAt (xiF ξ * yf) v + dd v
    · rw [if_neg (not_lt.2 h0), if_pos h0]
    · rw [if_pos (lt_of_not_ge h0), if_neg h0]
  rw [Finset.prod_congr rfl hite, Finset.prod_ite_zero]
  have hz : (algebraMap F (Af F) (ξ : F) * (yf : Af F)) = ((xiF ξ * yf : (Af F)ˣ) : Af F) := by
    rw [Units.val_mul]; rfl
  have hcd := hCD F ω c (algebraMap F (Af F) (ξ : F) * (yf : Af F)) m S (fun w => by
      have hne := pLoc_unit_ne_zero (xiF ξ * yf) w
      rw [hz, valued_eq_exp_neg_ord hne]
      congr 1
      simp only [hm, ordAt]
      ring)
    (fun w hw => by
      have h1 := hS w hw
      simp only [hm, ordAt_eq_zero (isIntegralUnitAt_mul h1.2.2.2 h1.2.2.1), h1.2.1, add_zero])
  rw [hcd]
  have hcst : ∏ v ∈ S, cst ω c v = ∏ v ∈ S0, cst ω c v := by
    symm
    refine Finset.prod_subset (fun v hv => by simp [hSdef, hv]) fun v _ hv0 => ?_
    have h1 : c v = 0 := by
      by_contra h; apply hv0; simp [hS0, h]
    have h2 : dd v = 0 := by
      by_contra h; apply hv0; simp [hS0, h]
    simp [cst, h1, h2]
  split_ifs with hall
  · rw [Finset.prod_mul_distrib, hcst]
    ring
  · ring

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open L4 GroundTheory.Automorphic.GodementSection

theorem sLocal_of (hA : ArchInt) (hLI : LocInt) (hFS : FinSplit) (hOP : OmegaProd) (hCD : CoefDiv) (hR : LocRam)
    (hPos : OmegaPos) : SFin → SKern → SLocal := by
  intro hfin hK F _ _ _ ω c H
  obtain ⟨κ, hκ, hκF⟩ := hK F c (hfin F ω c H)
  obtain ⟨Cf, hCf, hfinI⟩ := fin_int hLI hFS hOP hCD hR ω c H
  refine ⟨κ * (2 : ℂ) ^ Fintype.card (InfinitePlace F) * Cf, ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero hκ (pow_ne_zero _ two_ne_zero)) hCf
  intro y hy yf ξ
  set gI : (InfiniteAdeleRing F)ˣ → ℂ := fun a => archK y (ξ : F) a * (ωI ω a)⁻¹
  set gF : (Af F)ˣ → ℂ := fun b => finK c yf (ξ : F) b * (ωF ω b)⁻¹
  have hpt : ∀ τ : IdeleGroup F, kern c (yAd y yf) τ ξ * ((ω.1 τ : ℂˣ) : ℂ)⁻¹ * ((ideleModule F τ : ℝ) : ℂ) =
      κ * (gI (toInfinite F τ) * gF (toFinite F τ)) := by
    intro τ
    simp only [kern, hκF, kernF_split, ω_split, gI, gF]
    have h1 : ((ideleModule F τ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ideleModule F τ).2.ne'
    field_simp
  obtain ⟨hAi, hAe⟩ := hA F ω c H y hy ξ
  obtain ⟨hFi, hFe⟩ := hfinI yf ξ
  have hprod : Integrable (fun p : (InfiniteAdeleRing F)ˣ × (Af F)ˣ => κ * (gI p.1 * gF p.2))
      ((infiniteIdeleMeasure F).prod (finiteIdeleMeasure F)) :=
    (hAi.mul_prod hFi).const_mul κ
  have hmap : ∀ p : (InfiniteAdeleRing F)ˣ × (Af F)ˣ,
      toInfinite F ((prodEquiv F).symm p) = p.1 ∧ toFinite F ((prodEquiv F).symm p) = p.2 :=
    fun p => ⟨toInfinite_symm p, toFinite_symm p⟩
  constructor
  · have : Integrable (fun τ : IdeleGroup F => κ * (gI (toInfinite F τ) * gF (toFinite F τ))) (ideleMeasure F) := by
      rw [ideleMeasure]
      refine (integrable_map_equiv (prodEquiv F).symm.toHomeomorph.toMeasurableEquiv _).2 ?_
      convert hprod using 2 with p
      exact congrArg₂ (fun a b => κ * (gI a * gF b)) (hmap p).1 (hmap p).2
    exact this.congr (Filter.Eventually.of_forall fun τ => (hpt τ).symm)
  · rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_ideleMeasure]
    simp only [(hmap _).1, (hmap _).2]
    rw [integral_const_mul, integral_prod_mul, hAe, hFe]
    split_ifs with hξ
    · rw [hPos F ω c H ξ hξ, inv_one, mul_one]
      ring
    · ring

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

theorem local_expansion_holds : SFin → SKern → SLocal :=
  sLocal_of archimedean_integral_holds (local_integral_of_substitution inverse_substitution_holds) finite_split_holds character_product_holds coefficient_divisor_holds local_ramified_holds
    character_positive_holds

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
