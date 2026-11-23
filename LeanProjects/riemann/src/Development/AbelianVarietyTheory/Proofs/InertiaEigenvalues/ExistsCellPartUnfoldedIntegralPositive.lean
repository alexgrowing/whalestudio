import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRankinSelbergSchurTermFinsuppEulerProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LastRowCongruenceDetWeightMeasurableInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArchTranslatedSqrtWeightedFunGoodMirabolicTop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NegOneNotMemNatLat
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

noncomputable section

namespace GlobalTheory.CellBump

open GlobalTheory.CellDec GlobalTheory.RSJ

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ}

omit [IsTotallyComplex E] in

theorem detPow_eq (x : ℝ) {a : ℕ} (g : GA E a) :
    detPow E a x g = Real.exp (x * GlobalTheory.Mem.Chr.CharModel.logNorm E (Matrix.GeneralLinearGroup.det g)) := by
  change ‖((GlobalTheory.Mem.Chr.CharModel.absHom E (x : ℂ) (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)‖ = _
  rw [GlobalTheory.Mem.Chr.CharModel.absHom_val, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

omit [IsTotallyComplex E] in
theorem single_last_eq {R : Type} [Zero R] [One R] (j : Fin (m + 1)) :
    (Pi.single (Fin.last m) (1 : R) : Fin (m + 1) → R) j = if (j : ℕ) + 1 = m + 1 then 1 else 0 := by
  by_cases h : j = Fin.last m
  · subst h; simp
  · have : (j : ℕ) ≠ m := fun e => h (Fin.ext e)
    rw [Pi.single_apply, if_neg h, if_neg (by omega)]

omit [IsTotallyComplex E] in

theorem isOpen_natLat {N : ℕ} (hN : 0 < N) : IsOpen (natLat E N) := by
  have hu : IsUnit (N : Af E) := by
    have e : (N : Af E) = algebraMap E (Af E) (N : E) := (map_natCast _ _).symm
    rw [e]
    exact (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hN.ne')).map _
  have e : natLat E N = (fun x => ((hu.unit⁻¹ : (Af E)ˣ) : Af E) * x) ⁻¹'
      (GroundTheory.Global.integralFiniteAdeles (𝓞 E) E : Set (Af E)) := by
    ext x
    simp only [natLat, Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, GroundTheory.Global.mem_integralFiniteAdeles]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← mul_assoc, hu.val_inv_mul, one_mul]
      exact hz
    · intro h
      refine ⟨_, h, ?_⟩
      rw [← mul_assoc, hu.mul_val_inv, one_mul]
  rw [e]
  exact GroundTheory.Global.isOpen_integralFiniteAdeles.preimage (continuous_const.mul continuous_id)

omit [IsTotallyComplex E] in

theorem continuous_indN {N : ℕ} (hN : 0 < N) : Continuous fun y : Fin (m + 1) → Af E => indN N y := by
  set T : Set (Fin (m + 1) → Af E) :=
    {y | ∀ i : Fin (m + 1), y i - (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈ natLat E N} with hT
  have hTc : IsClopen T := by
    have e : T = ⋂ i : Fin (m + 1),
        (fun y : Fin (m + 1) → Af E => y i - (if (i : ℕ) + 1 = m + 1 then 1 else 0)) ⁻¹' natLat E N := by
      ext y; simp [T]
    rw [e]
    exact isClopen_iInter_of_finite fun i =>
      ⟨(GlobalTheory.ZUnfWt.isClosed_natLat N).preimage ((continuous_apply i).sub continuous_const),
        (isOpen_natLat hN).preimage ((continuous_apply i).sub continuous_const)⟩
  have e2 : (fun y : Fin (m + 1) → Af E => indN N y) = T.indicator (fun _ => (1 : ℂ)) := by
    funext y
    by_cases h : y ∈ T
    · rw [Set.indicator_of_mem h]; unfold indN; exact if_pos h
    · rw [Set.indicator_of_notMem h]; unfold indN; exact if_neg h
  rw [e2]
  exact continuous_indicator (by simp [hTc.frontier_eq]) continuous_const.continuousOn

theorem continuous_uInt {N : ℕ} (hN : 0 < N) {φ φ' : GA E (m + 1) → ℂ} (hφ : Continuous (GlobalTheory.JSW.whit φ))
    (hφ' : Continuous (GlobalTheory.JSW.whit φ')) {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : Continuous Φ)
    (hs : tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m)) (x : ℝ) :
    Continuous (GlobalTheory.ZEul.uInt φ φ' Φ N x) := by
  have hi : Continuous fun g : GA E (m + 1) => indN N (GlobalTheory.ZUnf.yFin g) :=
    (continuous_indN hN).comp GlobalTheory.ZUnfWt.continuous_yFin
  have hw : Continuous fun g : GA E (m + 1) => (detPow E (m + 1) x g : ℂ) :=
    Complex.continuous_ofReal.comp (GlobalTheory.ZUnfWt.continuous_detPow x)
  have e : GlobalTheory.ZEul.uInt φ φ' Φ N x = fun q => GlobalTheory.JSW.whit φ (q * infGL E (m + 1) (secInv (GlobalTheory.ZUnf.yInf q))) *
      conj (GlobalTheory.JSW.whit φ' (q * infGL E (m + 1) (secInv (GlobalTheory.ZUnf.yInf q)))) * Φ (GlobalTheory.ZUnf.yInf q) *
      indN N (GlobalTheory.ZUnf.yFin q) * (detPow E (m + 1) x q : ℂ) := rfl
  rw [e]
  refine continuous_iff_continuousAt.2 fun g => ?_
  by_cases hp : GlobalTheory.ZUnf.yInf g ∈ tsupport Φ
  · have hU : GlobalTheory.RSTheta.rowSet E (Fin.last m) ∈ nhds (GlobalTheory.ZUnf.yInf g) :=
      (GlobalTheory.RSTheta.isOpen_rowSet (E := E) (Fin.last m)).mem_nhds (hs hp)
    have hc : ContinuousOn (fun u => infGL E (m + 1) (secInv u)) (GlobalTheory.RSTheta.rowSet E (Fin.last m)) := by
      refine (GlobalTheory.RSTheta.continuousOn_inv_rowGL (E := E) (Fin.last m)).congr fun u hu => ?_
      simp only [GlobalTheory.ZUnf.secInv_eq_inv_rowGL hu, map_inv]
    have h1 : ContinuousAt (fun q : GA E (m + 1) => q * infGL E (m + 1) (secInv (GlobalTheory.ZUnf.yInf q))) g :=
      continuousAt_id.mul ((hc.continuousAt hU).comp GlobalTheory.ZUnf.continuous_yInf.continuousAt)
    exact (((hφ.continuousAt.comp h1).mul (Complex.continuous_conj.continuousAt.comp (hφ'.continuousAt.comp h1))).mul
      (hΦ.comp GlobalTheory.ZUnf.continuous_yInf).continuousAt).mul hi.continuousAt |>.mul hw.continuousAt
  · refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [GlobalTheory.ZUnf.continuous_yInf.continuousAt.eventually (notMem_tsupport_iff_eventuallyEq.1 hp)] with q hq
    simp [hq]

theorem uInt_self_zero {Φ : (Fin (m + 1) → Cinf E) → ℂ} (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0)
    (φ : GA E (m + 1) → ℂ) (N : ℕ) (g : GA E (m + 1)) :
    GlobalTheory.ZEul.uInt φ φ Φ N 0 g = ((GlobalTheory.ZEul.uInt φ φ Φ N 0 g).re : ℂ) ∧ 0 ≤ (GlobalTheory.ZEul.uInt φ φ Φ N 0 g).re := by
  set w := GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) with hw
  set y : Fin (m + 1) → Cinf E := fun i => pInf E (GlobalTheory.ZEul.lastRow g i) with hy
  set c := indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) with hc
  have hc' : c = (c.re : ℂ) ∧ 0 ≤ c.re := by
    simp only [c, indN]; split_ifs <;> simp
  have hΦy : Φ y = ((Φ y).re : ℂ) := Complex.ext rfl (by simp [(hΦ y).2])
  have hd : detPow E (m + 1) 0 g = 1 := by rw [detPow_eq]; simp
  have e : GlobalTheory.ZEul.uInt φ φ Φ N 0 g = ((Complex.normSq w * (Φ y).re * c.re : ℝ) : ℂ) := by
    change w * conj w * Φ y * c * (detPow E (m + 1) 0 g : ℂ) = _
    conv_lhs => rw [hd, Complex.mul_conj, hΦy, hc'.1]
    push_cast; ring
  rw [e, Complex.ofReal_re]
  exact ⟨rfl, mul_nonneg (mul_nonneg (Complex.normSq_nonneg _) (hΦ y).1) hc'.2⟩

theorem uInt_unip_mul {φ : GA E (m + 1) → ℂ}
    (hN : ∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g)
    (Φ : (Fin (m + 1) → Cinf E) → ℂ) (N : ℕ) (x : ℝ) {u : GA E (m + 1)} (hu : u ∈ NA E (m + 1))
    (g : GA E (m + 1)) : GlobalTheory.ZEul.uInt φ φ Φ N x (u * g) = GlobalTheory.ZEul.uInt φ φ Φ N x g := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hu
  have hu' : u ∈ GlobalTheory.JSW.NA E (m + 1) := ⟨h1, h2⟩
  have hr : GlobalTheory.ZEul.lastRow (u * g) = GlobalTheory.ZEul.lastRow g := GlobalTheory.ZUnf.lastRow_mul_of_row fun l => by
    rcases lt_or_eq_of_le (Fin.le_last l) with hl | rfl
    · rw [h1 _ _ hl, Matrix.one_apply_ne (ne_of_gt hl)]
    · rw [h2, Matrix.one_apply_eq]
  have hd : detPow E (m + 1) x (u * g) = detPow E (m + 1) x g := by
    rw [detPow_eq, detPow_eq, map_mul,
      show Matrix.GeneralLinearGroup.det u = 1 from Units.ext (GlobalTheory.RSLocalPart.det_eq_one hu), one_mul]
  have hp : GlobalTheory.JSW.psiN u * conj (GlobalTheory.JSW.psiN u) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [GlobalTheory.JSW.psiN, Circle.norm_coe]
    simp
  unfold GlobalTheory.ZEul.uInt
  rw [hr, hd, mul_assoc u g, hN u hu' _, map_mul]
  set W := GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)))
  set r := Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) * indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) *
    (detPow E (m + 1) x g : ℂ)
  linear_combination (W * conj W * r) * hp

end GlobalTheory.CellBump

namespace GlobalTheory.CellBump

open GlobalTheory.CellDec GlobalTheory.RSJ
open scoped Pointwise

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {m : ℕ}

omit [IsTotallyComplex E] in
theorem single_vecMul_eq_lastRow (g : GA E (m + 1)) :
    Matrix.vecMul (Pi.single (Fin.last m) (1 : Ad E)) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) =
      GlobalTheory.ZEul.lastRow g := by
  funext j
  rw [Matrix.single_one_vecMul]
  rfl

theorem exists_compact_support {S : Finset (HeightOneSpectrum (𝓞 E))} {b φ : GA E (m + 1) → ℂ} {N : ℕ}
    {J : (FractionalIdeal (𝓞 E)⁰ E)ˣ} {Φ : (Fin (m + 1) → Cinf E) → ℂ}
    (hJ : ∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))
    (hNJ : ∀ z ∈ natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)))
    (hΦc : HasCompactSupport Φ) (hs : tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m))
    (hN : ∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g)
    (hK : ∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, GlobalTheory.JSW.whit φ (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ g)
    (hb : ∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, b p ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * p ∈ C)
    (hW : ∀ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.whit φ p = b p) :
    ∃ K : Set (GA E (m + 1)), IsCompact K ∧ ∀ g ∈ C0 E (m + 1) S, GlobalTheory.ZEul.uInt φ φ Φ N 0 g ≠ 0 →
      ∃ u ∈ NA E (m + 1), u * g ∈ K := by
  obtain ⟨C, hC, hbC⟩ := hb
  refine ⟨(C * (finGL E (m + 1) '' (GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E (m + 1) : Set _))) *
      ((fun y => infGL E (m + 1) (GlobalTheory.RSTheta.rowGL (Fin.last m) y)) '' tsupport Φ),
    (hC.mul ((GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E (m + 1)).image
      GlobalTheory.RSLocalPart.continuous_finGL)).mul
      (hΦc.isCompact.image_of_continuousOn
        (GlobalTheory.CuspQuot.continuous_infGL.comp_continuousOn ((GlobalTheory.RSTheta.continuousOn_rowGL _).mono hs))), ?_⟩
  intro g hg h0
  have hrow := single_vecMul_eq_lastRow g
  have hdef : GlobalTheory.ZEul.uInt φ φ Φ N 0 g =
      GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i))) *
        conj (GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow g i)))) *
        Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) * indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) *
        (detPow E (m + 1) 0 g : ℂ) := rfl
  have hΦ0 : Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) ≠ 0 := fun h => h0 (by rw [hdef, h]; ring)
  have hy : (fun i => pInf E (GlobalTheory.ZEul.lastRow g i)) ∈ tsupport Φ := subset_tsupport _ hΦ0
  have hcond : ∀ i : Fin (m + 1), GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i) -
      (if (i : ℕ) + 1 = m + 1 then 1 else 0) ∈ natLat E N := by
    by_contra hc
    apply h0
    have : indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow g i)) = 0 := by unfold indN; exact if_neg hc
    rw [hdef, this]; ring
  have hi : (fun i => pInf E (Matrix.vecMul (Pi.single (Fin.last m) 1) (g : Matrix _ _ (Ad E)) i)) ∈
      GlobalTheory.RSTheta.rowSet E (Fin.last m) := by
    rw [hrow]; exact hs hy
  have hf : ∀ v ∈ S, ∀ j : Fin (m + 1),
      Valued.v ((GlobalTheory.CuspRep.pFin E (Matrix.vecMul (Pi.single (Fin.last m) 1) (g : Matrix _ _ (Ad E)) j) -
        (Pi.single (Fin.last m) 1 : Fin (m + 1) → Af E) j) v) ≤
        WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) := by
    intro v hv j
    rw [hrow, single_last_eq]
    exact hNJ _ (hcond j) v hv
  obtain ⟨u, hu, p, hp, κ, hκ, e⟩ := GlobalTheory.RSLocalPart.exists_decomp (fun i => Fin.le_last i) hJ hg hi hf
  rw [hrow] at e
  set y : Fin (m + 1) → Cinf E := fun i => pInf E (GlobalTheory.ZEul.lastRow g i) with hydef
  have hge : g = u * p * finGL E (m + 1) κ * infGL E (m + 1) (GlobalTheory.RSTheta.rowGL (Fin.last m) y) := by
    rw [← e, inv_mul_cancel_right]
  have hpS : p ∈ GlobalTheory.JSW.mirS E S m := ⟨fun w hw => hp.2 w hw, hp.1⟩
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB _).1 hu
  have hW' : GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (secInv y)) = GlobalTheory.JSW.psiN u * b p := by
    rw [GlobalTheory.ZUnf.secInv_eq_inv_rowGL (hs hy), map_inv, e, mul_assoc, hN u ⟨h1, h2⟩, hK κ hκ, hW p hpS]
  have hbp : b p ≠ 0 := by
    intro hb0
    apply h0
    rw [hdef]
    change GlobalTheory.JSW.whit φ (g * infGL E (m + 1) (secInv y)) * _ * _ * _ * _ = 0
    rw [hW', hb0, mul_zero]; ring
  obtain ⟨u', hu', hc'⟩ := hbC p hpS hbp
  have hu'N : u' ∈ NA E (m + 1) := (GlobalTheory.SmGL.mem_unipB _).2 hu'
  refine ⟨(u * u')⁻¹, inv_mem (mul_mem hu hu'N), _, ⟨_, hc', _, ⟨κ, GlobalTheory.RSLocalPart.levelAt_subset S J hκ, rfl⟩, rfl⟩,
    _, ⟨y, hy, rfl⟩, ?_⟩
  rw [hge]
  group

end GlobalTheory.CellBump

namespace GlobalTheory.CellBump

open GlobalTheory.CellDec GlobalTheory.RSJ

theorem exists_cellPart_unfoldedIntegral_positive_alt : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ) (φ : GA E (m + 1) → ℂ)
    (N : ℕ) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (Φ : (Fin (m + 1) → Cinf E) → ℂ),
    0 < N → (∀ v ∈ S, 0 < FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E)) →
    (∀ z ∈ GlobalTheory.RSJ.natLat E N, ∀ v ∈ S,
        Valued.v (z v) ≤ WithZero.exp (-FractionalIdeal.count E v (J : FractionalIdeal (𝓞 E)⁰ E))) →
    Continuous Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) →
    (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) → Φ (Pi.single (Fin.last m) 1) ≠ 0 →
    Continuous (GlobalTheory.JSW.whit φ) →
    (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g) →
    (∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g, GlobalTheory.JSW.whit φ (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ g) →
    b 1 = 1 → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, b p ≠ 0 →
      ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * p ∈ C) →
    (∀ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.whit φ p = b p) →
    ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E (m + 1))),
    IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
    ∃ f t : GA E (m + 1) → ℝ, Measurable f ∧ Measurable t ∧ (∀ g, 0 ≤ f g) ∧ IntegrableOn f 𝓕₀ μ ∧
      0 < ∫ g in 𝓕₀, f g ∂μ ∧ (∃ R : ℝ, ∀ g, f g ≠ 0 → |t g| ≤ R) ∧
      (∀ g ∉ GlobalTheory.CellDec.C0 E (m + 1) S, f g = 0) ∧
      (∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, GlobalTheory.ZEul.uInt φ φ Φ N 0 g = (f g : ℂ)) ∧
      ∀ (x : ℝ) (g : GA E (m + 1)), (GlobalTheory.RSJ.detPow E (m + 1) x g : ℂ) = Complex.exp (x * t g) := by
  intro E _ _ _ m S b φ N J Φ hN0 hJ hNJ hΦ hΦc hs hΦr hΦ1 hWc hN hK hb1 hb hW μ _ 𝓕₀ h𝓕
  have hO := isOpen_adelicUnipotentTimesIntegralOutsideSet E (m + 1) S
  have hre := fun g => uInt_self_zero hΦr φ N g
  have hc : Continuous (GlobalTheory.ZEul.uInt φ φ Φ N 0) := continuous_uInt hN0 hWc hWc hΦ hs 0
  have hBc : Continuous fun g => (GlobalTheory.ZEul.uInt φ φ Φ N 0 g).re := Complex.continuous_re.comp hc
  obtain ⟨K, hKc, hKs⟩ := exists_compact_support hJ hNJ hΦc hs hN hK hb hW

  have hS1 : (1 : GA E (m + 1)) ∈ GlobalTheory.JSW.mirS E S m :=
    ⟨fun w _ => map_one _, fun j => by simp [Matrix.one_apply, eq_comm]⟩
  have hy1 : (fun i => pInf E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)) = Pi.single (Fin.last m) 1 := by
    funext i
    by_cases h : i = Fin.last m
    · subst h; simp [GlobalTheory.ZEul.lastRow]
    · simp [GlobalTheory.ZEul.lastRow, Matrix.one_apply_ne (Ne.symm h), h]
  have hyl : (Pi.single (Fin.last m) 1 : Fin (m + 1) → Cinf E) = GlobalTheory.RSJ.Model.eLast (Cinf E) (m + 1) := by
    funext i; rw [single_last_eq]; rfl
  have hf1 : indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)) = 1 := by
    unfold indN
    refine if_pos fun i => ?_
    have : GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i) = if (i : ℕ) + 1 = m + 1 then 1 else 0 := by
      rw [← single_last_eq (R := Af E)]
      by_cases h : i = Fin.last m
      · subst h; simp [GlobalTheory.ZEul.lastRow]
      · simp [GlobalTheory.ZEul.lastRow, Matrix.one_apply_ne (Ne.symm h), h]
    show GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i) - _ ∈ _
    rw [this, sub_self]
    exact ⟨0, fun v => zero_mem _, by simp⟩
  have hB1 : 0 < (GlobalTheory.ZEul.uInt φ φ Φ N 0 1).re := by
    have e : GlobalTheory.ZEul.uInt φ φ Φ N 0 1 = Φ (Pi.single (Fin.last m) 1) := by
      change GlobalTheory.JSW.whit φ (1 * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i))) *
        conj (GlobalTheory.JSW.whit φ (1 * infGL E (m + 1) (secInv fun i => pInf E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)))) *
        Φ (fun i => pInf E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)) *
        indN N (fun i => GlobalTheory.RSJ.pFin E (GlobalTheory.ZEul.lastRow (1 : GA E (m + 1)) i)) *
        (detPow E (m + 1) 0 1 : ℂ) = _
      rw [hf1, hy1, hyl, GlobalTheory.RSJ.Model.secInv_eLast, map_one, one_mul, hW 1 hS1, hb1, detPow_eq, ← hyl]
      simp
    rw [e]
    refine lt_of_le_of_ne (hΦr _).1 fun h => hΦ1 (Complex.ext h.symm (hΦr _).2)

  obtain ⟨hpos, -⟩ := GlobalTheory.RSLocalPart.lintegral_cell_pos_lt_top_continuous E (m + 1) μ S 𝓕₀ h𝓕
    (fun _ g => (GlobalTheory.ZEul.uInt φ φ Φ N 0 g).re) (hBc.comp continuous_snd) (fun _ g => (hre g).2) (fun _ => hB1)
    (fun _ u hu g => by simp only [uInt_unip_mul hN Φ N 0 hu g])
    ⟨K, hKc, fun _ g hg h0 => hKs g hg fun h => h0 (by rw [h, Complex.zero_re])⟩
  obtain ⟨hlpos, hltop⟩ := hpos 0
  have hIB : IntegrableOn (fun g => (GlobalTheory.ZEul.uInt φ φ Φ N 0 g).re) (𝓕₀ ∩ C0 E (m + 1) S) μ :=
    ⟨hBc.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun g => (hre g).2)).2 hltop⟩

  set t : GA E (m + 1) → ℝ := fun g => GlobalTheory.Mem.Chr.CharModel.logNorm E (Matrix.GeneralLinearGroup.det g) with ht
  have htc : Continuous t := (GlobalTheory.Mem.Chr.CharModel.continuous_logNorm E).comp Matrix.GeneralLinearGroup.continuous_det
  have htu : ∀ u ∈ NA E (m + 1), ∀ g, t (u * g) = t g := fun u hu g => by
    simp only [ht, map_mul, show Matrix.GeneralLinearGroup.det u = 1 from Units.ext (GlobalTheory.RSLocalPart.det_eq_one hu),
      one_mul]
  obtain ⟨R, hR⟩ := hKc.exists_bound_of_continuousOn htc.continuousOn
  refine ⟨(C0 E (m + 1) S).indicator fun g => (GlobalTheory.ZEul.uInt φ φ Φ N 0 g).re, t,
    hBc.measurable.indicator hO.measurableSet, htc.measurable,
    fun g => Set.indicator_nonneg (fun g _ => (hre g).2) g, ?_, ?_, ⟨R, fun g hg => ?_⟩,
    fun g hg => Set.indicator_of_notMem hg _, fun g hg => ?_, fun x g => ?_⟩
  · unfold IntegrableOn
    rw [integrable_indicator_iff hO.measurableSet]
    unfold IntegrableOn
    rw [Measure.restrict_restrict hO.measurableSet, Set.inter_comm]
    exact hIB
  · rw [integral_indicator hO.measurableSet, Measure.restrict_restrict hO.measurableSet, Set.inter_comm,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun g => (hre g).2) hBc.aestronglyMeasurable]
    exact ENNReal.toReal_pos hlpos.ne' hltop.ne
  · have hgC : g ∈ C0 E (m + 1) S := by
      by_contra h
      exact hg (Set.indicator_of_notMem h _)
    rw [Set.indicator_of_mem hgC] at hg
    obtain ⟨u, hu, hk⟩ := hKs g hgC fun h => hg (by rw [h, Complex.zero_re])
    have := hR _ hk
    rwa [htu u hu, Real.norm_eq_abs] at this
  · rw [Set.indicator_of_mem hg]
    exact (hre g).1
  · rw [detPow_eq, Complex.ofReal_exp]
    push_cast
    rfl

end GlobalTheory.CellBump
