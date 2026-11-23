import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldMirabolic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaSeriesUnfoldMirabolic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MeasurePreservingToMixedPiSymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IteratedColumnTransformEqGlobalWhittaker
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageTopOfVanishingBlockAver

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open GlobalTheory.MirTower GlobalTheory.CuspGeneric
open GroundTheory.Automorphic.FourierWhittaker (partialCoeff blockGL uGL)

noncomputable section

namespace GlobalTheory.ColFourier

open Matrix GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.GJMatrix GroundTheory.Global

variable {E : Type} [Field E] [NumberField E]

theorem partialCoeff_colSmooth : ∀ (E : Type) [Field E] [NumberField E] (n m : ℕ) (φ : GA E n → ℂ), Continuous φ → (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) →
    ∀ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi E (Fin m), ∀ (j : ℕ) (g : GA E n),
    partialCoeff (GlobalTheory.RSnm.colSmooth m F φ) j g = GlobalTheory.RSnm.colSmooth m F (partialCoeff φ j) g := by
  intro E _ _ n m φ hc ⟨C, hC⟩ F hF j
  have hFi := integrable_of_mem_schwartzBruhatPi hF
  have hFc := continuous_of_mem_schwartzBruhatPi hF
  have hb : ∀ i g, ‖partialWhittakerCoeff φ i g‖ ≤ C := by
    intro i
    induction i with
    | zero => exact hC
    | succ i ih => exact fun g => norm_vecCoeff_le (fun x _ => ih _) _
  have hcc : ∀ i, Continuous (partialWhittakerCoeff φ i) := by
    intro i
    induction i with
    | zero => exact hc
    | succ i ih => exact continuous_stepCoeff _ ih
  unfold partialCoeff
  induction n - j with
  | zero => intro g; rfl
  | succ i ih =>
    intro g
    have e : partialWhittakerCoeff (GlobalTheory.RSnm.colSmooth m F φ) i = GlobalTheory.RSnm.colSmooth m F (partialWhittakerCoeff φ i) := funext ih
    simp only [partialWhittakerCoeff]
    rw [e]
    set l := n - 1 - i
    set Q := partialWhittakerCoeff φ i
    haveI : IsFiniteMeasure ((vecMeasure E (Fin l)).restrict (vecDomain E (Fin l))) := ⟨by
      rw [Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
    set H : (Fin l → Ad E) → (Fin m → Ad E) → ℂ := fun y x =>
      F x * (Q (FourierWhittaker.colGL l y * (g * FourierWhittaker.colGL m x)) *
        (adelicChar E (-pair (lastVec l) y) : ℂ)) with hH
    have hHc : Continuous (Function.uncurry H) :=
      (hFc.comp continuous_snd).mul (((hcc i).comp (((FourierWhittaker.continuous_colGL l).comp continuous_fst).mul
        (continuous_const.mul ((FourierWhittaker.continuous_colGL m).comp continuous_snd)))).mul
        ((continuous_adelicChar_neg_pair _).comp continuous_fst))
    have hI : Integrable (Function.uncurry H)
        (((vecMeasure E (Fin l)).restrict (vecDomain E (Fin l))).prod (adeleMeasurePi E)) := by
      refine Integrable.mono' ((integrable_const C).mul_prod hFi.norm) hHc.aestronglyMeasurable (.of_forall fun p => ?_)
      simp only [Function.uncurry, hH, norm_mul, Circle.norm_coe, mul_one]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hb i _) (norm_nonneg _)
    have hs := integral_integral_swap hI
    simp only [stepCoeff, vecCoeff, GlobalTheory.RSnm.colSmooth, ← integral_mul_const, ← integral_const_mul, mul_assoc]
    exact hs

theorem vecCoeff_zero_eq_zero : ∀ (E : Type) [Field E] [NumberField E] (k m : ℕ), m + 1 ≤ k → ∀ (φ : GA E (k + 1) → ℂ),
    Continuous φ → (∀ γ g, φ (ratGL E (k + 1) γ * g) = φ g) →
    (∀ r, 0 < r → r ≤ k → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (k + 1) r k)) (fun x => φ (blkU x * g)) = 0) →
    ∀ g : GA E (k + 1), GroundTheory.Automorphic.FourierWhittaker.vecCoeff (fun z : Fin (m + 1) → Ad E =>
      partialCoeff φ (m + 1 + 1) (GroundTheory.Automorphic.FourierWhittaker.colGL (m + 1) z * g)) (0 : Fin (m + 1) → E) = 0 := by
  intro E _ _ k m hmk φ hc hl hv g
  set ψ : AddChar (Ad E) ℂ := GlobalTheory.StdCharConductor.psi E
  have hψ : StdPsi ψ := GlobalTheory.StdCharConductor.stdPsi_psi E
  have hG : ∀ i j, j + i = k → Good ψ j (partialCoeff φ (j + 1)) := by
    intro i
    induction i with
    | zero =>
      intro j hj
      obtain rfl : j = k := hj
      rw [partialCoeff_self]
      exact good_top E j ψ φ hc hl hv
    | succ i ih =>
      intro j hj
      have hk : j + 1 < k + 1 := by omega
      have h1 := GlobalTheory.CuspRep.Generic.good_colT hψ hk (ih (j + 1) (by omega))
      have hcol : colT ψ (j + 1) (partialCoeff φ (j + 1 + 1)) = partialCoeff φ (j + 1) := by
        funext g
        rw [partialCoeff_of_lt φ hk]
        exact WhitEq.colT_eq_stepCoeff hk _ (fun ξ g => partialCoeff_succ_diagonal_colGL (K := E) (n := k + 1) hl hk ξ g) g
      rwa [hcol] at h1
  have hg := hG (k - (m + 1)) (m + 1) (by omega)
  have hk : m + 1 < k + 1 := by omega
  have hz := hg.van (m + 1) (Nat.succ_pos m) le_rfl g
  have hper := (per_blk hg.cont (GlobalTheory.CuspRep.Generic.hl_of_good hg le_rfl) g).2
  haveI : Countable (ratV E (UnipotentBlockColumnIndex (k + 1) (m + 1) (m + 1))) := countable_vecLattice
  rw [WhitEq.avg_eq_setIntegral (ratV E (UnipotentBlockColumnIndex (k + 1) (m + 1) (m + 1))) (vecMeasure E _) (vecDomain E _)
      isAddFundamentalDomain_vecDomain vecMeasure_vecDomain _ hper] at hz
  let Em := MeasurableEquiv.piCongrLeft (fun _ : Fin (m + 1) => Ad E) (WhitEq.colIx hk)
  have hE : MeasurePreserving Em (vecMeasure E (UnipotentBlockColumnIndex (k + 1) (m + 1) (m + 1))) (vecMeasure E (Fin (m + 1))) :=
    measurePreserving_piCongrLeft (fun _ : Fin (m + 1) => GroundTheory.Global.adeleMeasure E) (WhitEq.colIx hk)
  have hEx : ∀ x : UnipotentBlockColumnIndex (k + 1) (m + 1) (m + 1) → Ad E, Em x = fun i => x ((WhitEq.colIx hk).symm i) := by
    intro x
    funext i
    simp [Em, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  have hpre : Em ⁻¹' vecDomain E (Fin (m + 1)) = vecDomain E (UnipotentBlockColumnIndex (k + 1) (m + 1) (m + 1)) := by
    ext x
    simp only [Set.mem_preimage, hEx, vecDomain, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h t
      have := h (WhitEq.colIx hk t)
      rwa [Equiv.symm_apply_apply] at this
    · intro h i
      exact h _
  rw [vecCoeff, ← hE.setIntegral_preimage_emb Em.measurableEmbedding, hpre, ← hz]
  refine setIntegral_congr_fun measurableSet_vecDomain fun x _ => ?_
  simp only [hEx]
  rw [WhitEq.blkU_eq_colGL hk]
  simp [pair]

theorem tsum_translate_eq : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), ∀ G ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi E (Fin n), ∀ x : Fin n → Ad E,
    ∑' η : Fin n → E, G ((fun i => algebraMap E (Ad E) (η i)) + x) =
      ∑' ξ : Fin n → E, GroundTheory.Automorphic.GJMatrix.adelicFourierPi E G (fun i => algebraMap E (Ad E) (ξ i)) *
        (GroundTheory.Global.adelicChar E (-GroundTheory.Automorphic.FourierWhittaker.pair ξ x) : ℂ) := by
  intro E _ _ n G hG x
  have hT : (fun y => G (y + x)) ∈ schwartzBruhatPi E (Fin n) := by
    induction hG using Submodule.span_induction with
    | mem G hG =>
      obtain ⟨φ, g, hg, rfl⟩ := hG
      have hg' : (g ∘ Homeomorph.addRight (finPartPi x)) ∈ finiteSchwartzBruhatPi E :=
        ⟨hg.1.comp_continuous (Homeomorph.continuous _), hg.2.comp_homeomorph _⟩
      convert schwartzBruhatTensorPi_mem (SchwartzMap.compSubConstCLM ℂ (-infPartPi x) φ) hg' using 1
      funext y
      have h1 : infPartPi (y + x) = infPartPi y + infPartPi x := by
        funext i
        simp only [infPartPi, Pi.add_apply, homeomorphMixedSpace_apply]
        exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace E) (y i).1 (x i).1
      have h2 : finPartPi (y + x) = finPartPi y + finPartPi x := rfl
      simp only [schwartzBruhatTensorPi, SchwartzMap.compSubConstCLM_apply, Function.comp_apply, h1, h2,
        sub_neg_eq_add, Homeomorph.coe_addRight]
    | zero => exact zero_mem _
    | add G H _ _ hG hH => exact add_mem hG hH
    | smul r G _ hG => exact Submodule.smul_mem _ r hG
  refine (tsum_algebraMap_eq_tsum_adelicFourierPi hT).trans (tsum_congr fun ξ => ?_)
  simp only [adelicFourierPi]
  rw [← integral_mul_const, ← integral_add_right_eq_self (μ := adeleMeasurePi E) (fun y => G y *
    (adelicChar E (∑ i, y i * algebraMap E (Ad E) (ξ i)) : ℂ) * (adelicChar E (-pair ξ x) : ℂ)) x]
  refine integral_congr_ae (.of_forall fun y => ?_)
  simp only
  rw [mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  congr 3
  simp only [pair, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_comm (x _), add_neg_cancel_right]

theorem hasSum_integral_mul_of_periodic : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (G f : (Fin n → Ad E) → ℂ) (c : (Fin n → E) → ℂ),
    Continuous G → Integrable G (GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E) → Continuous f → (∃ C : ℝ, ∀ x, ‖f x‖ ≤ C) →
    (∀ (η : Fin n → E) x, f ((fun i => algebraMap E (Ad E) (η i)) + x) = f x) → (Summable fun ξ => ‖c ξ‖) →
    (∀ x, ∑' η : Fin n → E, G ((fun i => algebraMap E (Ad E) (η i)) + x) =
      ∑' ξ : Fin n → E, c ξ * (GroundTheory.Global.adelicChar E (-GroundTheory.Automorphic.FourierWhittaker.pair ξ x) : ℂ)) →
    HasSum (fun ξ : Fin n → E => c ξ * GroundTheory.Automorphic.FourierWhittaker.vecCoeff f ξ)
      (∫ x, G x * f x ∂GroundTheory.Automorphic.GJMatrix.adeleMeasurePi E) := by
  intro E _ _ n G f c hGc hGi hf ⟨C, hC⟩ hp hs hP
  haveI := GroundTheory.Global.countable_numberField E
  set μ := vecMeasure E (Fin n)
  set D := vecDomain E (Fin n)
  have hGi' : Integrable (fun x => G x * f x) μ := hGi.mul_bdd hf.aestronglyMeasurable (.of_forall hC)
  have hD : IsAddFundamentalDomain (vecLattice E (Fin n)) D μ := isAddFundamentalDomain_vecDomain
  let e : (Fin n → E) ≃ vecLattice E (Fin n) := Equiv.ofBijective
    (fun η => ⟨fun i => algebraMap E (Ad E) (η i), algebraMap_mem_vecLattice η⟩)
    ⟨fun η η' h => funext fun i => AdeleRing.algebraMap_injective (𝓞 E) E (congrFun (congrArg Subtype.val h) i),
      fun ⟨_, η, hη⟩ => ⟨η, Subtype.ext hη⟩⟩
  have h1 : ∫ x, G x * f x ∂μ = ∫ x in D, ∑' l : vecLattice E (Fin n), G (l +ᵥ x) * f (l +ᵥ x) ∂μ := by
    rw [hD.integral_eq_tsum'' _ hGi', integral_tsum]
    · intro l
      exact ((hGc.mul hf).comp (continuous_const_vadd l)).aestronglyMeasurable
    · rw [← hD.lintegral_eq_tsum'' fun x => ‖G x * f x‖ₑ]
      exact hGi'.2.ne
  have h2 : ∀ x, ∑' l : vecLattice E (Fin n), G (l +ᵥ x) * f (l +ᵥ x) =
      ∑' ξ : Fin n → E, c ξ * (f x * (adelicChar E (-pair ξ x) : ℂ)) := by
    intro x
    rw [← e.tsum_eq]
    change ∑' η : Fin n → E, G ((fun i => algebraMap E (Ad E) (η i)) + x) * f ((fun i => algebraMap E (Ad E) (η i)) + x) = _
    simp only [hp]
    rw [tsum_mul_right, hP, ← tsum_mul_right]
    exact tsum_congr fun ξ => by ring
  haveI : IsFiniteMeasure (μ.restrict D) := ⟨by
    rw [Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  change HasSum _ (∫ x, G x * f x ∂μ)
  rw [h1]
  simp only [h2, vecCoeff, ← integral_const_mul]
  have hn : ∀ (ξ : Fin n → E) x, ‖c ξ * (f x * (adelicChar E (-pair ξ x) : ℂ))‖ ≤ ‖c ξ‖ * C := fun ξ x => by
    rw [norm_mul, norm_mul, Circle.norm_coe, mul_one]
    exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
  have hi : ∀ ξ : Fin n → E, Integrable (fun x => c ξ * (f x * (adelicChar E (-pair ξ x) : ℂ))) (μ.restrict D) :=
    fun ξ => Integrable.mono' (integrable_const (‖c ξ‖ * C))
      (continuous_const.mul (hf.mul (continuous_adelicChar_neg_pair ξ))).aestronglyMeasurable (.of_forall (hn ξ))
  refine hasSum_integral_of_summable_integral_norm hi ?_
  refine Summable.of_nonneg_of_le (fun ξ => integral_nonneg fun x => norm_nonneg _) (fun ξ => ?_) (hs.mul_right C)
  refine (integral_mono (hi ξ).norm (integrable_const (‖c ξ‖ * C)) (hn ξ)).trans_eq ?_
  rw [integral_const, measureReal_def, Measure.restrict_apply_univ, vecMeasure_vecDomain, ENNReal.toReal_one, one_smul]

theorem norm_partialCoeff_le {n : ℕ} {φ : GA E n → ℂ} {C : ℝ} (hC : ∀ g, ‖φ g‖ ≤ C) (j : ℕ) (g : GA E n) :
    ‖partialCoeff φ j g‖ ≤ C := by
  unfold partialCoeff
  induction n - j generalizing g with
  | zero => exact hC g
  | succ i ih => exact norm_vecCoeff_le (fun x _ => ih _) _

def trGL {R : Type} [CommRing R] {n : ℕ} (h : GL (Fin n) R) : GL (Fin n) R :=
  ⟨h.valᵀ, (h⁻¹).valᵀ, by rw [← transpose_mul, Units.inv_mul, transpose_one],
    by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩

theorem hasSum_integral_mulVec {n : ℕ} {F : (Fin n → Ad E) → ℂ} (hF : F ∈ schwartzBruhatPi E (Fin n))
    {f : (Fin n → Ad E) → ℂ} (hf : Continuous f) (hb : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C)
    (hp : ∀ (η : Fin n → E) x, f ((fun i => algebraMap E (Ad E) (η i)) + x) = f x) (h : GA E n) :
    HasSum (fun ξ : Fin n → E => adelicFourierPi E F ((algebraMap E (Ad E) ∘ ξ) ᵥ* h.val) * vecCoeff f ξ)
      (∫ x, F x * f (h.val *ᵥ x) ∂adeleMeasurePi E) := by
  set t := trGL h with ht
  set G : (Fin n → Ad E) → ℂ := fun y => F (y ᵥ* (t⁻¹).val) with hG
  have hGm : G ∈ schwartzBruhatPi E (Fin n) := GlobalTheory.ThetaPoisson.comp_vecMul_mem t⁻¹ hF
  have H := hasSum_integral_mul_of_periodic E n G f _ (continuous_of_mem_schwartzBruhatPi hGm) (integrable_of_mem_schwartzBruhatPi hGm) hf hb hp
    (poisson_of_mem_schwartzBruhatPi hGm).2.1 (tsum_translate_eq E n G hGm)
  set d : ℝ := (IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det t) : ℝ) with hd
  have hd0 : 0 < d := (IdeleGroup.ideleModule E (Matrix.GeneralLinearGroup.det t)).2
  have hFT : ∀ y, adelicFourierPi E G y = (d : ℂ) * adelicFourierPi E F (y ᵥ* h.val) := by
    intro y
    have := GlobalTheory.ThetaPoisson.adelicFourierPi_comp_vecMul t⁻¹ F y
    rw [inv_inv, map_inv, map_inv, Positive.coe_inv, inv_inv] at this
    exact this
  have hm := (GroundTheory.Automorphic.GJGlobal.Modulus.vecMulHomeomorph t).measurableEmbedding.integral_map
    (μ := adeleMeasurePi E) (fun x => G x * f x)
  have hmap : (adeleMeasurePi E).map (GroundTheory.Automorphic.GJGlobal.Modulus.vecMulHomeomorph t) = _ :=
    GroundTheory.Automorphic.GJGlobal.Modulus.map_vecMul_adeleMeasurePi t
  rw [hmap, integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.2 hd0.le), Complex.real_smul] at hm
  have e : ∀ x : Fin n → Ad E, G (x ᵥ* t.val) * f (x ᵥ* t.val) = F x * f (h.val *ᵥ x) := by
    intro x
    simp only [hG]
    rw [vecMul_vecMul, Units.mul_inv, vecMul_one]
    congr 2
    exact vecMul_transpose _ _
  have hm' : ∫ x, F x * f (h.val *ᵥ x) ∂adeleMeasurePi E = ((d⁻¹ : ℝ) : ℂ) * ∫ x, G x * f x ∂adeleMeasurePi E := by
    rw [hm]
    exact integral_congr_ae (.of_forall fun x => (e x).symm)
  rw [hm']
  refine (H.mul_left ((d⁻¹ : ℝ) : ℂ)).congr_fun fun ξ => ?_
  have hd' : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd0.ne'
  rw [hFT, Complex.ofReal_inv, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hd', one_mul]
  rfl

theorem hasSum_colSmooth : ∀ (E : Type) [Field E] [NumberField E] (k m : ℕ) (hmk : m + 1 ≤ k) (φ : GA E (k + 1) → ℂ),
    Continuous φ → (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) → (∀ γ g, φ (ratGL E (k + 1) γ * g) = φ g) →
    (∀ r, 0 < r → r ≤ k → ∀ g, avg (ratV E (UnipotentBlockColumnIndex (k + 1) r k)) (fun x => φ (blkU x * g)) = 0) →
    ∀ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi E (Fin (m + 1)),
    ∀ γ : {ξ : Fin (m + 1) → E // ξ ≠ 0} → GL (Fin (m + 1)) E,
    (∀ ξ, Matrix.vecMul (Pi.single (Fin.last m) 1 : Fin (m + 1) → E) (γ ξ).val = ξ.1) → ∀ h : GA E (m + 1),
    HasSum (fun ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0} =>
        GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (Matrix.vecMul (algebraMap E (Ad E) ∘ ξ.1) h.val) *
          partialCoeff φ (m + 1) (blockGL (by omega : m + 1 ≤ k + 1) (ratGL E (m + 1) (γ ξ) * h)))
      (partialCoeff (GlobalTheory.RSnm.colSmooth (m + 1) F φ) (m + 1 + 1) (blockGL (by omega : m + 1 ≤ k + 1) h)) := by
  intro E _ _ k m hmk φ hc hb hl hv F hF γ hγ h
  have hlt : m + 1 < k + 1 := by omega
  obtain ⟨C, hC⟩ := hb
  set b : GA E (k + 1) := blockGL hlt.le h with hbdef
  set f : (Fin (m + 1) → Ad E) → ℂ := fun z => partialCoeff φ (m + 1 + 1) (FourierWhittaker.colGL (m + 1) z * b) with hf
  have hfc : Continuous f := (continuous_partialCoeff hc _).comp ((FourierWhittaker.continuous_colGL (m + 1)).mul continuous_const)
  have hp : ∀ (η : Fin (m + 1) → E) x, f ((fun i => algebraMap E (Ad E) (η i)) + x) = f x := by
    intro η x
    simp only [hf]
    rw [colGL_add, mul_assoc, ← diagonal_colGL, partialCoeff_succ_diagonal_colGL (K := E) (n := k + 1) hl hlt]
  have H := hasSum_integral_mulVec hF hfc ⟨C, fun x => norm_partialCoeff_le hC _ _⟩ hp h
  have hval : partialCoeff (GlobalTheory.RSnm.colSmooth (m + 1) F φ) (m + 1 + 1) b =
      ∫ x, F x * f (h.val *ᵥ x) ∂adeleMeasurePi E := by
    rw [partialCoeff_colSmooth E (k + 1) (m + 1) φ hc ⟨C, hC⟩ F hF, GlobalTheory.RSnm.colSmooth]
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [hf, hbdef]
    rw [colGL_mul_blockGL hlt, mulVec_mulVec, Units.inv_mul, one_mulVec]
  have h0 : vecCoeff f 0 = 0 := vecCoeff_zero_eq_zero E k m hmk φ hc hl hv b
  have hlast : (lastVec (m + 1) : Fin (m + 1) → E) = Pi.single (Fin.last m) 1 := by
    funext i
    simp only [lastVec, Pi.single_apply, Fin.ext_iff, Fin.val_last, add_left_inj]
  have hcoef : ∀ ξ : {ξ : Fin (m + 1) → E // ξ ≠ 0},
      partialCoeff φ (m + 1) (blockGL hlt.le (ratGL E (m + 1) (γ ξ) * h)) = vecCoeff f ξ.1 := by
    intro ξ
    have := partialCoeff_diagonal_blockGL_eq_vecCoeff (K := E) (n := k + 1) hl hlt (γ ξ) b
    rw [hlast, hγ, diagonal_blockGL] at this
    rw [map_mul]
    exact this
  rw [hval]
  simp only [hcoef]
  refine (hasSum_subtype_iff_of_support_subset (s := {ξ : Fin (m + 1) → E | ξ ≠ 0}) ?_).2 H
  intro ξ hξ h1
  apply hξ
  simp only [h1, h0, mul_zero]

end GlobalTheory.ColFourier

end
