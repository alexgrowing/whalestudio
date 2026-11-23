import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.IsProbabilityMeasureComplexPart
import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ToRHomeomorphMixedSpace
import GroundTheory.AutomorphicForms.GL2.AdelicFourier2TensorCosetIndicatorAlgebraMap

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open NumberField.mixedEmbedding MeasureTheory GroundTheory.Global GroundTheory.Automorphic.Adele2 UpperTheory.V.Sd UpperTheory.V.Published
open scoped Matrix Classical NumberField.AdeleRing nonZeroDivisors

namespace UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic

variable {F : Type} [Field F] [NumberField F]

def nId (c : HeightOneSpectrum (𝓞 F) → ℕ) : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  ∏ᶠ w, primeIdealUnit w ^ (c w : ℤ)

theorem count_nId {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite)
    (w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w ((nId c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) = c w :=
  count_finprod_primeIdealUnit_zpow _ (Filter.eventually_cofinite.2 (hc.subset fun v hv => by
    simp only [Set.mem_ofPred_eq] at hv ⊢
    exact_mod_cast hv)) w

theorem count_different (w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = dd w := by
  rw [FractionalIdeal.count_coe F w differentIdeal_ne_bot]
  rfl

theorem mem_nId_iff {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (a : Af F) :
    (∀ w, Valued.v (pLoc F w a) ≤ WithZero.exp (-(c w : ℤ))) ↔ a ∈ idealFiniteAdeles (nId c) := by
  rw [mem_idealFiniteAdeles]
  refine forall_congr' fun w => ?_
  rw [count_nId hc]
  rfl

theorem mem_dual_iff {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (a : Af F) :
    (∀ w, Valued.v (pLoc F w a) ≤ WithZero.exp ((c w : ℤ) + dd w)) ↔
      a ∈ idealFiniteAdeles (traceDualIdeal F (nId c)) := by
  rw [mem_idealFiniteAdeles]
  refine forall_congr' fun w => ?_
  rw [count_traceDualIdeal, count_nId hc, count_different, neg_neg]
  rfl

theorem arch_zero [IsTotallyReal F] : arch (0 : UpperTheory.V.TR.Rinf F) 0 = 0 := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp)

def gFin (c : HeightOneSpectrum (𝓞 F) → ℕ) : (Fin 2 → Af F) → ℂ :=
  finiteTensor2 ![cosetIndicator (nId c) 0, cosetIndicator (nId c) 1]

theorem gFin_mem (c : HeightOneSpectrum (𝓞 F) → ℕ) : gFin c ∈ finiteSchwartzBruhat2 F :=
  finiteTensor2_mem fun i => by
    fin_cases i
    · exact cosetIndicator_mem_finiteSchwartzBruhat _ _
    · exact cosetIndicator_mem_finiteSchwartzBruhat _ _

variable [IsTotallyReal F]

theorem phi_eq {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite)
    (φ : SchwartzMap (Fin 2 → mixedSpace F) ℂ) (hφ : ∀ u, φ u = arch (toR F (u 0)) (toR F (u 1))) :
    Phi c = schwartzBruhatTensor2 φ (gFin c) := by
  funext x
  rw [schwartzBruhatTensor2, hφ, gFin, finiteTensor2_apply, Phi]
  simp only [infPart, finPart, toR_homeomorphMixedSpace, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, cosetIndicator_apply, sub_zero]
  congr 1
  have h0 := mem_nId_iff hc (pFin F (x 0))
  have h1 := mem_nId_iff hc (pFin F (x 1) - 1)
  simp only [map_sub, map_one] at h1
  by_cases a : (x 0).2 ∈ idealFiniteAdeles (nId c) <;> by_cases b : (x 1).2 - 1 ∈ idealFiniteAdeles (nId c)
  · rw [if_pos fun w => ⟨h0.2 a w, h1.2 b w⟩, if_pos a, if_pos b, mul_one]
  · rw [if_neg (fun h => b (h1.1 fun w => (h w).2)), if_neg b, mul_zero]
  · rw [if_neg (fun h => a (h0.1 fun w => (h w).1)), if_neg a, zero_mul]
  · rw [if_neg (fun h => a (h0.1 fun w => (h w).1)), if_neg a, zero_mul]

def cst (c : HeightOneSpectrum (𝓞 F) → ℕ) : ℂ :=
  (-Complex.I) ^ Fintype.card (InfinitePlace F) *
    (((finiteAdeleMeasure F (idealFiniteAdeles (nId c))).toReal : ℝ) : ℂ) ^ 2

theorem cst_ne_zero (c : HeightOneSpectrum (𝓞 F) → ℕ) : cst c ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr Complex.I_ne_zero)) (pow_ne_zero _ ?_)
  rw [Complex.ofReal_ne_zero]
  exact ENNReal.toReal_ne_zero.mpr ⟨(isOpen_idealFiniteAdeles _).measure_ne_zero _ ⟨0, zero_mem _⟩,
    finiteAdeleMeasure_idealFiniteAdeles_ne_top _⟩

theorem fourier_phi {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite)
    (φ : SchwartzMap (Fin 2 → mixedSpace F) ℂ) (hφ : ∀ u, φ u = arch (toR F (u 0)) (toR F (u 1)))
    (y : Fin 2 → Ad F) :
    adelicFourier2 F (Phi c) y = cst c * PhiH c y := by
  have hφ' : (⇑φ : (Fin 2 → mixedSpace F) → ℂ) = fun u => arch (toR F (u 0)) (toR F (u 1)) := funext hφ
  rw [phi_eq hc φ hφ, adelicFourier2_schwartzBruhatTensor2, schwartzBruhatTensor2,
    mixedFourier2Schwartz_apply, hφ', mixedFourier2_arch, gFin, finiteFourier2_finiteTensor2,
    finiteTensor2_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    finiteFourier_cosetIndicator, zero_mul, one_mul, AddChar.map_zero_eq_one, Circle.coe_one,
    infPart, finPart, toR_homeomorphMixedSpace, PhiH, cst]
  have h0 := mem_dual_iff hc (pFin F (y 0))
  have h1 := mem_dual_iff hc (pFin F (y 1))
  rw [show pFin F (y 1) = (y 1).2 from rfl]
  by_cases a : (y 0).2 ∈ idealFiniteAdeles (traceDualIdeal F (nId c)) <;>
    by_cases b : (y 1).2 ∈ idealFiniteAdeles (traceDualIdeal F (nId c))
  · rw [if_pos fun w => ⟨h0.2 a w, h1.2 b w⟩]
    simp only [Set.indicator_apply, SetLike.mem_coe, a, b, if_true, Pi.one_apply]
    ring
  · rw [if_neg (fun h => b (h1.1 fun w => (h w).2))]
    simp only [Set.indicator_apply, SetLike.mem_coe, a, b, if_true, if_false, Pi.one_apply]
    ring
  · rw [if_neg (fun h => a (h0.1 fun w => (h w).1))]
    simp only [Set.indicator_apply, SetLike.mem_coe, a, b, if_true, if_false, Pi.one_apply]
    ring
  · rw [if_neg (fun h => a (h0.1 fun w => (h w).1))]
    simp only [Set.indicator_apply, SetLike.mem_coe, a, b, if_true, if_false, Pi.one_apply]
    ring

theorem rowA_zero : rowA (0 : Fin 2 → F) = 0 := by
  funext i
  simp [rowA]

theorem phi_zero (c : HeightOneSpectrum (𝓞 F) → ℕ) : Phi c 0 = 0 := by
  simp [Phi, map_zero, arch_zero]

theorem phiH_zero (c : HeightOneSpectrum (𝓞 F) → ℕ) : PhiH c 0 = 0 := by
  simp [PhiH, map_zero, arch_zero]

end UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic

open UpperTheory.HilbertEisensteinWeightOne UpperTheory.HilbertEisensteinWeightOne.PoissonSummationAdelic in
theorem UpperTheory.HilbertEisensteinWeightOne.poisson_summation_holds : SPois := by
  intro F _ _ _ ω c hyp
  have hc := finite_support_of_cond F ω c hyp.fin hyp.cond
  obtain ⟨φ, hφ⟩ := exists_schwartz_arch F
  have hmem : Phi c ∈ schwartzBruhat2 F := by
    rw [phi_eq hc φ hφ]
    exact schwartzBruhatTensor2_mem φ (gFin_mem c)
  refine ⟨cst c, fun h => ?_⟩
  obtain ⟨S1, S2, E⟩ := poisson_rightTranslate hmem h
  have hF : ∀ ξ : Fin 2 → F, adelicFourier2 F (Phi c) ((fun i ↦ algebraMap F (Ad F) (ξ i)) ᵥ*
      ((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F))ᵀ) =
      cst c * PhiH c (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ) := by
    intro ξ
    rw [fourier_phi hc φ hφ, Matrix.vecMul_transpose]
    rfl
  simp only [hF, norm_mul] at S2 E
  have hsupp1 : Function.support (fun ξ : Fin 2 → F => Phi c (rowA ξ ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F)))) ⊆
      {ξ | ξ ≠ 0} := by
    intro ξ hξ
    rintro (rfl : ξ = 0)
    apply hξ
    dsimp only
    rw [rowA_zero, Matrix.zero_vecMul, phi_zero]
  have hsupp2 : Function.support (fun ξ : Fin 2 → F =>
      PhiH c (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ)) ⊆ {ξ | ξ ≠ 0} := by
    intro ξ hξ
    rintro (rfl : ξ = 0)
    apply hξ
    dsimp only
    rw [rowA_zero, Matrix.mulVec_zero, phiH_zero]
  have hC : ‖cst c‖ ≠ 0 := norm_ne_zero_iff.mpr (cst_ne_zero c)
  refine ⟨?_, ?_, ?_⟩
  · exact (S1.subtype {ξ | ξ ≠ 0} : _)
  · exact (((summable_mul_left_iff hC).mp S2).subtype {ξ | ξ ≠ 0} : _)
  · rw [thetaS, thetaT]
    rw [show (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, Phi c (rowA ξ.1 ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F)))) =
        ∑' ξ : ({ξ | ξ ≠ 0} : Set (Fin 2 → F)), Phi c (rowA (ξ : Fin 2 → F) ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F))) from rfl,
      tsum_subtype_eq_of_support_subset hsupp1,
      show (∑' ξ : {ξ : Fin 2 → F // ξ ≠ 0}, PhiH c (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA ξ.1)) =
        ∑' ξ : ({ξ | ξ ≠ 0} : Set (Fin 2 → F)), PhiH c (((h⁻¹ : GA F 2) : Matrix (Fin 2) (Fin 2) (Ad F)) *ᵥ rowA (ξ : Fin 2 → F)) from rfl,
      tsum_subtype_eq_of_support_subset hsupp2]
    change ∑' ξ : Fin 2 → F, Phi c ((fun i ↦ algebraMap F (Ad F) (ξ i)) ᵥ* (h : Matrix (Fin 2) (Fin 2) (Ad F))) = _
    rw [E, tsum_mul_left, absD, Complex.ofReal_inv]
    ring
