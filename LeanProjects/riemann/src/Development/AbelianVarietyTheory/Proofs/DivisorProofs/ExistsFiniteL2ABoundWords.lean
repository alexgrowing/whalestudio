import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleJoinZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergWordL2Bound

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

open MeasureTheory

namespace GlobalTheory.FoldrBoundLinearForms

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_bound_foldr_le {M U : Type*} [AddCommGroup M] [Module ℝ M] [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (D : U →ₗ[ℝ] M →ₗ[ℝ] M) (m : M)
    (R : ℝ) (n : ℕ) :
    ∀ T : M →ₗ[ℝ] E, ∃ B : ℝ, ∀ l : List U, l.length = n → (∀ u ∈ l, ‖u‖ ≤ R) →
      ‖T (l.foldr (fun u x => D u x) m)‖ ≤ B := by
  induction n with
  | zero =>
    intro T
    refine ⟨‖T m‖, fun l hl _ => ?_⟩
    rw [List.length_eq_zero_iff.1 hl]
    exact le_rfl
  | succ n ih =>
    intro T
    let b := Module.finBasis ℝ U
    choose B hB using fun j => ih (T ∘ₗ D (b j))
    refine ⟨∑ j, ‖LinearMap.toContinuousLinearMap (b.coord j)‖ * R * B j, fun l hl hu => ?_⟩
    cases l with
    | nil => simp at hl
    | cons u l =>
      rw [List.foldr_cons]
      set y := l.foldr (fun u x => D u x) m with hy
      have e : T (D u y) = ∑ j, b.repr u j • T (D (b j) y) := by
        conv_lhs => rw [← b.sum_repr u]
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      rw [e]
      have hR : 0 ≤ R := (norm_nonneg u).trans (hu u List.mem_cons_self)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_smul]
      have h1 : ‖b.repr u j‖ ≤ ‖LinearMap.toContinuousLinearMap (b.coord j)‖ * R := by
        have := (LinearMap.toContinuousLinearMap (b.coord j)).le_opNorm u
        exact this.trans (mul_le_mul_of_nonneg_left (hu u List.mem_cons_self) (norm_nonneg _))
      have h2 := hB j l (by simpa using hl) (fun v hv => hu v (List.mem_cons_of_mem _ hv))
      exact mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (norm_nonneg _) hR)

def lForm (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) (c : κ → mixedEmbedding.mixedSpace F) :
    (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => ℓ (y ⬝ᵥ c)
      map_add' := fun y y' => by rw [add_dotProduct, map_add]
      map_smul' := fun r y => by rw [smul_dotProduct, map_smul]; rfl }

theorem lForm_apply (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) (c y : κ → mixedEmbedding.mixedSpace F) :
    lForm ℓ c y = ℓ (y ⬝ᵥ c) := rfl

def lOp (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
  LineDeriv.lineDerivOpCLM ℂ (SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) v.1 f +
    (2 * Real.pi * Complex.I) • SchwartzMap.smulLeftCLM ℂ (fun x => ((lForm ℓ v.2 x : ℝ) : ℂ)) f

theorem lOp_apply (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (x : κ → mixedEmbedding.mixedSpace F) :
    lOp ℓ v f x = fderiv ℝ f x v.1 + (2 * Real.pi * Complex.I) * ((lForm ℓ v.2 x : ℝ) : ℂ) * f x := by
  have htg : Function.HasTemperateGrowth fun x : κ → mixedEmbedding.mixedSpace F => ((lForm ℓ v.2 x : ℝ) : ℂ) :=
    (Complex.ofRealCLM.comp (lForm ℓ v.2)).hasTemperateGrowth
  simp only [lOp, SchwartzMap.add_apply,
      SchwartzMap.smul_apply, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
      SchwartzMap.smulLeftCLM_apply_apply htg, smul_eq_mul]
  ring

def lLin (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) :
    ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
    SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →ₗ[ℝ] SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
  LinearMap.mk₂ ℝ (fun v f => lOp ℓ v f)
    (fun v v' f => by
      ext x
      simp only [SchwartzMap.add_apply, lOp_apply, lForm_apply, Prod.fst_add, Prod.snd_add, map_add,
        dotProduct_add]
      push_cast; ring)
    (fun c v f => by
      ext x
      simp only [SchwartzMap.smul_apply, lOp_apply, lForm_apply, Prod.smul_fst, Prod.smul_snd, map_smul,
        dotProduct_smul, smul_eq_mul, Complex.real_smul]
      push_cast; ring)
    (fun v f f' => by
      simp only [lOp, map_add, smul_add]
      abel)
    (fun c v f => by
      simp only [lOp, ContinuousLinearMap.map_smul_of_tower, smul_add]
      rw [smul_comm c])

variable [Invertible (2 : AdeleRing (𝓞 F) F)]

theorem schr_pureA_arch (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hℓ : ∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z))
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (t : ℝ)
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (a : κ → AdeleRing (𝓞 F) F) :
    GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (t • h)) (GlobalTheory.WeilM.pureA F f g) a =
      Complex.exp (2 * Real.pi * Complex.I *
        ((t * lForm ℓ h.2 (GlobalTheory.WeilL2Words.archPart F a) + t ^ 2 * (1 / 2 * ℓ (h.1 ⬝ᵥ h.2)) : ℝ) : ℂ)) *
        f (GlobalTheory.WeilL2Words.archPart F a + t • h.1) * g (fun i => (a i).2) := by
  obtain ⟨h1, h2⟩ := h
  simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilM.pureA, GlobalTheory.WeilL2Words.archPair, Prod.smul_fst, Prod.smul_snd]
  have hfin : (fun i => ((a + GlobalTheory.WeilL2Words.arch F (t • h1)) i).2) = fun i => (a i).2 := by
    funext i
    change (a i).2 + 0 = _
    rw [add_zero]
  have harch : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((a + GlobalTheory.WeilL2Words.arch F (t • h1)) i).1) =
      GlobalTheory.WeilL2Words.archPart F a + t • h1 := by
    funext i
    change InfiniteAdeleRing.ringEquiv_mixedSpace F ((a i).1 + (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm ((t • h1) i)) =
      InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1 + (t • h1) i
    rw [map_add, RingEquiv.apply_symm_apply]
  set A := a ⬝ᵥ GlobalTheory.WeilL2Words.arch F (t • h2) +
    ⅟(2 : AdeleRing (𝓞 F) F) * (GlobalTheory.WeilL2Words.arch F (t • h1) ⬝ᵥ GlobalTheory.WeilL2Words.arch F (t • h2)) with hA
  have hev : ∀ w : κ → mixedEmbedding.mixedSpace F,
      ⇑(GlobalTheory.ThetaSobolevBase.evHom F) ∘ GlobalTheory.WeilL2Words.arch F w = w := by
    intro w
    funext i
    change InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (w i)) = w i
    rw [RingEquiv.apply_symm_apply]
  let s : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd _ _
  have hsnd : ∀ w : κ → mixedEmbedding.mixedSpace F, ⇑s ∘ GlobalTheory.WeilL2Words.arch F w = 0 := by
    intro w
    funext i
    rfl
  have hA2 : A.2 = 0 := by
    change s A = 0
    rw [hA, map_add, map_mul, RingHom.map_dotProduct, RingHom.map_dotProduct, hsnd, hsnd, dotProduct_zero,
      dotProduct_zero, mul_zero, add_zero]
  have hpa : ⇑(GlobalTheory.ThetaSobolevBase.evHom F) ∘ a = GlobalTheory.WeilL2Words.archPart F a := rfl
  have hA1 : GlobalTheory.ThetaSobolevBase.evHom F A = GlobalTheory.WeilL2Words.archPart F a ⬝ᵥ (t • h2) +
      algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) * ((t • h1) ⬝ᵥ (t • h2)) := by
    rw [hA, map_add, map_mul, RingHom.map_dotProduct, RingHom.map_dotProduct, GlobalTheory.ThetaSobolevBase.evHom_invOf_two,
      hev, hev, hpa]
  have hAe : A = GlobalTheory.WeilL2Words.arch1 F (GlobalTheory.ThetaSobolevBase.evHom F A) := by
    refine Prod.ext ?_ ?_
    · change A.1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (InfiniteAdeleRing.ringEquiv_mixedSpace F A.1)
      rw [RingEquiv.symm_apply_apply]
    · rw [hA2]; rfl
  have hl : ℓ (GlobalTheory.WeilL2Words.archPart F a ⬝ᵥ (t • h2) +
      algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) * ((t • h1) ⬝ᵥ (t • h2))) =
      t * lForm ℓ h2 (GlobalTheory.WeilL2Words.archPart F a) + t ^ 2 * (1 / 2 * ℓ (h1 ⬝ᵥ h2)) := by
    rw [← Algebra.smul_def, lForm_apply]
    simp only [dotProduct_smul, smul_dotProduct, map_add, map_smul, smul_eq_mul]
    ring
  rw [hAe, hℓ, hA1, hfin, harch, hl]
  ring

theorem hasDerivAt_schr_pureA_arch (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hℓ : ∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z))
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (a : κ → AdeleRing (𝓞 F) F) :
    HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (t • h)) (GlobalTheory.WeilM.pureA F f g) a)
      (GlobalTheory.WeilM.pureA F (lOp ℓ h f) g a) 0 := by
  simp only [schr_pureA_arch ψ ℓ hℓ]
  set y := GlobalTheory.WeilL2Words.archPart F a with hy
  set L := lForm ℓ h.2 y with hL
  set c := 1 / 2 * ℓ (h.1 ⬝ᵥ h.2) with hc
  have h0 : HasDerivAt (fun t : ℝ => t * L + t ^ 2 * c) L 0 := by
    exact (((hasDerivAt_id (0 : ℝ)).mul_const L).fun_add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const c)).congr_deriv (by simp)
  have h1 := (h0.ofReal_comp.const_mul (2 * Real.pi * Complex.I)).cexp
  have h2 : HasDerivAt (fun t : ℝ => f (y + t • h.1)) (fderiv ℝ f y h.1) 0 :=
    (f.differentiableAt (x := y)).hasFDerivAt.hasLineDerivAt _
  have h3 := (h1.fun_mul h2).mul_const (g (fun i => (a i).2))
  refine h3.congr_deriv (Eq.symm ?_)
  change lOp ℓ h f y * g (fun i => (a i).2) = _
  rw [lOp_apply, ← hL]
  congr 1
  simp
  ring

theorem dS_sumPure (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hℓ : ∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)) {ι : Type} [Fintype ι]
    (g : ι → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (f : ι → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (h : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :
    GlobalTheory.WeilL2Words.dS F ψ h (GlobalTheory.ThetaSobolevBase.sumPure g f) =
      GlobalTheory.ThetaSobolevBase.sumPure g (fun i => lLin ℓ h (f i)) := by
  funext x
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hasDerivAt_schr_pureA_arch ψ ℓ hℓ h (f i) (g i) x
  have e : (fun t : ℝ => GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (t • h)) (GlobalTheory.ThetaSobolevBase.sumPure g f) x) =
      fun t => ∑ i, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair F (t • h)) (GlobalTheory.WeilM.pureA F (f i) (g i)) x := by
    funext t
    simp only [GlobalTheory.WeilM.schr, GlobalTheory.ThetaSobolevBase.sumPure, Finset.sum_apply, Finset.mul_sum]
  simp only [GlobalTheory.WeilL2Words.dS]
  rw [e, hd.deriv]
  simp only [GlobalTheory.ThetaSobolevBase.sumPure, Finset.sum_apply]
  rfl

theorem word_sumPure (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (ℓ : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hℓ : ∀ z, ψ (GlobalTheory.WeilL2Words.arch1 F z) = Complex.exp (2 * Real.pi * Complex.I * ℓ z)) {ι : Type} [Fintype ι]
    (g : ι → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (f : ι → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (ws : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))) :
    GlobalTheory.WeilL2Words.word F ψ ws (GlobalTheory.ThetaSobolevBase.sumPure g f) =
      GlobalTheory.ThetaSobolevBase.sumPure g (fun i => ws.foldr (fun u x => lLin ℓ u x) (f i)) := by
  induction ws with
  | nil => rfl
  | cons h ws ih =>
    rw [GlobalTheory.WeilL2Words.word_cons, ih, dS_sumPure ψ ℓ hℓ]
    rfl

omit [Invertible (2 : AdeleRing (𝓞 F) F)] in

theorem l2A_sumPure_le {m : ℕ} (μ : @Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _))
    (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hg : ∀ i, Continuous (g i))
    (f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) :
    GlobalTheory.WeilL2Words.l2A F μ (GlobalTheory.ThetaSobolevBase.sumPure g f) ≤
      (m : ENNReal) * ∑ i, (∫⁻ x, ‖f i x‖ₑ ^ 2) * @lintegral _ (borel _) μ (fun y => ‖g i y‖ₑ ^ 2) := by
  haveI hO : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  letI : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  have hpt : ∀ x y, ‖GlobalTheory.ThetaSobolevBase.sumPure g f (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2 ≤
      (m : ENNReal) * ∑ i, ‖f i x‖ₑ ^ 2 * ‖g i y‖ₑ ^ 2 := by
    intro x y
    have e : GlobalTheory.ThetaSobolevBase.sumPure g f (GlobalTheory.WeilCont.adeleJoin F x y) = ∑ i, f i x * g i y := by
      simp only [GlobalTheory.ThetaSobolevBase.sumPure, Finset.sum_apply, GlobalTheory.WeilCont.pureA_adeleJoin]
    rw [e]
    have hr : ‖∑ i, f i x * g i y‖ ^ 2 ≤ (m : ℝ) * ∑ i, (‖f i x‖ * ‖g i y‖) ^ 2 := by
      refine (pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun i _ => norm_mul _ _)) 2).trans ?_
      simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖f i x‖ * ‖g i y‖)
    have := ENNReal.ofReal_le_ofReal hr
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)] at this
    refine this.trans_eq ?_
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _),
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, ofReal_norm_eq_enorm]
  have hfm : ∀ i, Measurable fun x => ‖f i x‖ₑ ^ 2 := fun i => (f i).continuous.measurable.enorm.pow_const 2
  have hgm : ∀ i, Measurable fun y => ‖g i y‖ₑ ^ 2 := fun i => (hg i).measurable.enorm.pow_const 2
  unfold GlobalTheory.WeilL2Words.l2A
  calc ∫⁻ y, (∫⁻ x, ‖GlobalTheory.ThetaSobolevBase.sumPure g f (GlobalTheory.WeilCont.adeleJoin F x y)‖ₑ ^ 2) ∂μ
      ≤ ∫⁻ y, (∫⁻ x, (m : ENNReal) * ∑ i, ‖f i x‖ₑ ^ 2 * ‖g i y‖ₑ ^ 2) ∂μ :=
        lintegral_mono fun y => lintegral_mono fun x => hpt x y
    _ = ∫⁻ y, (m : ENNReal) * ∑ i, (∫⁻ x, ‖f i x‖ₑ ^ 2) * ‖g i y‖ₑ ^ 2 ∂μ := by
        congr 1
        funext y
        rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => (hfm i).mul_const _),
          lintegral_finset_sum _ fun i _ => (hfm i).mul_const _]
        simp_rw [lintegral_mul_const _ (hfm _)]
    _ = _ := by
        rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => (hgm i).const_mul _),
          lintegral_finset_sum _ fun i _ => (hgm i).const_mul _]
        simp_rw [lintegral_const_mul _ (hgm _)]

end GlobalTheory.FoldrBoundLinearForms

open GlobalTheory.FoldrBoundLinearForms in

theorem GlobalTheory.WeilL2Words.l2A_word_le : ∀ (F : Type) [Field F] [NumberField F] [Invertible (2 : AdeleRing (𝓞 F) F)] (κ : Type) [Fintype κ]
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ), GlobalTheory.WeilL2Words.IsStdInf F ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    ∀ (μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _)), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (n : ℕ) (R : ℝ), ∃ B : ENNReal, B ≠ ⊤ ∧ ∀ ws : List ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)), ws.length = n → (∀ h ∈ ws, ‖h‖ ≤ R) →
      GlobalTheory.WeilL2Words.l2A F μ (GlobalTheory.WeilL2Words.word F ψ ws Φ) ≤ B := by
  intro F _ _ _ κ _ ψ hψ Φ hΦ μ hμ n R
  haveI hO : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI := GlobalTheory.WeilAdm.HaarSplit.volume_isAddHaar F κ
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).HasTemperateGrowth := inferInstance
  obtain ⟨ℓ, -, hℓ⟩ := hψ
  obtain ⟨m, g, f, hg, rfl⟩ := GlobalTheory.ThetaSobolevBase.exists_sumPure hΦ
  have hgc : ∀ i, Continuous (g i) := fun i => (hg i).1.continuous
  letI : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI := hμ
  have hG : ∀ i, ∫⁻ y, ‖g i y‖ₑ ^ 2 ∂μ ≠ ⊤ := by
    intro i
    have h := ((hgc i).memLp_of_hasCompactSupport (p := 2) (μ := μ) (hg i).2).2
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)] at h
    simpa using h.ne
  let T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →ₗ[ℝ]
      Lp ℂ 2 (volume : Measure (κ → mixedEmbedding.mixedSpace F)) :=
    { toFun := fun f => (f.memLp 2 volume).toLp _
      map_add' := fun f f' => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (by ext x; simp))
      map_smul' := fun c f => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (by ext x; simp)) }
  choose B hB using fun i => exists_bound_foldr_le (lLin ℓ) (f i) R n T
  refine ⟨(m : ENNReal) * ∑ i, ENNReal.ofReal (B i) ^ 2 * ∫⁻ y, ‖g i y‖ₑ ^ 2 ∂μ, ?_, fun ws hl hws => ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top m) (ENNReal.sum_ne_top.2 fun i _ =>
      ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (hG i))
  rw [word_sumPure ψ ℓ hℓ]
  refine (l2A_sumPure_le μ g hgc _).trans ?_
  gcongr with i
  set f' := ws.foldr (fun u x => lLin ℓ u x) (f i) with hf'
  have h1 := hB i ws hl hws
  have hm := f'.memLp 2 (volume : Measure (κ → mixedEmbedding.mixedSpace F))
  have h2 : eLpNorm f' 2 volume ≤ ENNReal.ofReal (B i) := by
    have h3 : ‖T f'‖ = (eLpNorm f' 2 volume).toReal := Lp.norm_toLp _ hm
    rw [← ENNReal.ofReal_toReal hm.2.ne, ← h3]
    exact ENNReal.ofReal_le_ofReal h1
  have h4 : ∫⁻ x, ‖f' x‖ₑ ^ 2 = eLpNorm f' 2 volume ^ 2 := by
    have := eLpNorm_nnreal_pow_eq_lintegral (f := (f' : (κ → mixedEmbedding.mixedSpace F) → ℂ))
      (μ := volume) (p := 2) (by norm_num)
    simpa using this.symm
  rw [h4]
  exact pow_le_pow_left' h2 2

end
