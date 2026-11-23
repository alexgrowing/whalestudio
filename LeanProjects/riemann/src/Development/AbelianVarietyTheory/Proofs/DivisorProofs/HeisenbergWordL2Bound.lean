import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DHRealAdSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicVectorsBoundsPureTensorsSlices
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDecay
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.ThetaSobolevBase

open scoped Classical SchwartzMap ENNReal

theorem exists_bound_foldr {M U : Type*} [AddCommGroup M] [Module ℝ M] [NormedAddCommGroup U] [NormedSpace ℝ U]
    [FiniteDimensional ℝ U] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (D : U →ₗ[ℝ] M →ₗ[ℝ] M) (m : M) (ℓ : ℕ) :
    ∀ T : M →ₗ[ℝ] E, ∃ B : ℝ, ∀ l : List U, l.length ≤ ℓ → (∀ u ∈ l, ‖u‖ ≤ 1) →
      ‖T (l.foldr (fun u x => D u x) m)‖ ≤ B := by
  induction ℓ with
  | zero =>
    intro T
    refine ⟨‖T m‖, fun l hl _ => ?_⟩
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)]
    exact le_rfl
  | succ n ih =>
    intro T
    let b := Module.finBasis ℝ U
    choose B hB using fun j => ih (T ∘ₗ D (b j))
    refine ⟨max ‖T m‖ (∑ j, ‖LinearMap.toContinuousLinearMap (b.coord j)‖ * B j), fun l hl hu => ?_⟩
    cases l with
    | nil => exact le_max_left _ _
    | cons u l =>
      refine le_trans ?_ (le_max_right _ _)
      rw [List.foldr_cons]
      set y := l.foldr (fun u x => D u x) m with hy
      have e : T (D u y) = ∑ j, b.repr u j • T (D (b j) y) := by
        conv_lhs => rw [← b.sum_repr u]
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      rw [e]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_smul]
      have h1 : ‖b.repr u j‖ ≤ ‖LinearMap.toContinuousLinearMap (b.coord j)‖ := by
        have := (LinearMap.toContinuousLinearMap (b.coord j)).le_opNorm u
        refine this.trans ?_
        exact mul_le_of_le_one_right (norm_nonneg _) (hu u List.mem_cons_self)
      have h2 := hB j l (by simpa using hl) (fun v hv => hu v (List.mem_cons_of_mem _ hv))
      exact mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def trForm (c : κ → mixedEmbedding.mixedSpace F) : (κ → mixedEmbedding.mixedSpace F) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ c)
      map_add' := fun y y' => by rw [add_dotProduct, map_add]
      map_smul' := fun r y => by rw [smul_dotProduct, map_smul]; rfl }

theorem trForm_apply (c y : κ → mixedEmbedding.mixedSpace F) :
    trForm c y = Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (y ⬝ᵥ c) := rfl

def derOp (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (f : SInf F κ) : SInf F κ :=
  LineDeriv.lineDerivOpCLM ℂ (SInf F κ) v.1 f -
    (2 * Real.pi * Complex.I) • SchwartzMap.smulLeftCLM ℂ (fun x => ((trForm v.2 x : ℝ) : ℂ)) f

theorem derOp_apply (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (f : SInf F κ)
    (x : κ → mixedEmbedding.mixedSpace F) :
    derOp v f x = fderiv ℝ f x v.1 - (2 * Real.pi * Complex.I) * ((trForm v.2 x : ℝ) : ℂ) * f x := by
  have htg : Function.HasTemperateGrowth fun x : κ → mixedEmbedding.mixedSpace F => ((trForm v.2 x : ℝ) : ℂ) :=
    (Complex.ofRealCLM.comp (trForm v.2)).hasTemperateGrowth
  simp only [derOp, SchwartzMap.sub_apply,
      SchwartzMap.smul_apply, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv,
      SchwartzMap.smulLeftCLM_apply_apply htg, smul_eq_mul]
  ring

def derLin (ι : Type) : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
    (ι → SInf F κ) →ₗ[ℝ] (ι → SInf F κ) :=
  LinearMap.mk₂ ℝ (fun v f i => derOp v (f i))
    (fun v v' f => by
      funext i; ext x
      simp only [Pi.add_apply, SchwartzMap.add_apply, derOp_apply, trForm_apply, Prod.fst_add, Prod.snd_add, map_add,
        dotProduct_add]
      push_cast; ring)
    (fun c v f => by
      funext i; ext x
      simp only [Pi.smul_apply, SchwartzMap.smul_apply, derOp_apply, trForm_apply, Prod.smul_fst, Prod.smul_snd, map_smul,
        dotProduct_smul, smul_eq_mul, Complex.real_smul]
      push_cast; ring)
    (fun v f f' => by
      funext i
      simp only [Pi.add_apply, derOp, map_add, smul_add]
      abel)
    (fun c v f => by
      funext i
      simp only [Pi.smul_apply, derOp, ContinuousLinearMap.map_smul_of_tower, smul_sub]
      rw [smul_comm c])

variable (F) in

def evHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem evHom_apply (a : AF F) : evHom F a = evI F a := rfl

theorem evHom_realAd (t : ℝ) : evHom F (realAd F t) = algebraMap ℝ (mixedEmbedding.mixedSpace F) t := by
  change InfiniteAdeleRing.ringEquiv_mixedSpace F
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ (mixedEmbedding.mixedSpace F) t)) = _
  exact RingEquiv.apply_symm_apply _ _

theorem realAd_snd (t : ℝ) : (realAd F t).2 = 0 := rfl

theorem evHom_invOf_two [Invertible (2 : AF F)] :
    evHom F (⅟(2 : AF F)) = algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) := by
  have h2 : evHom F (⅟(2 : AF F)) * 2 = 1 := by
    rw [← map_ofNat (evHom F) 2, ← map_mul, invOf_mul_self, map_one]
  calc evHom F (⅟(2 : AF F)) = evHom F (⅟(2 : AF F)) * algebraMap ℝ (mixedEmbedding.mixedSpace F) (2 * (1 / 2)) := by
        rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, map_one, mul_one]
    _ = (evHom F (⅟(2 : AF F)) * 2) * algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) := by
        rw [map_mul, map_ofNat]; ring
    _ = _ := by rw [h2, one_mul]

def evDir (w : (κ → AF F) × (κ → AF F)) : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F) :=
  (fun i => evI F (w.1 i), fun i => evI F (w.2 i))

theorem schr_pureA [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F)) (t : ℝ)
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : κ → AF F) :
    schr ψ (realAd F t • w) (pureA F f g) x =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((t * trForm (evDir w).2 (fun i => evI F (x i)) +
        t ^ 2 * (1 / 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) ((evDir w).1 ⬝ᵥ (evDir w).2)) : ℝ) : ℂ)) *
        f ((fun i => evI F (x i)) + t • (evDir w).1) * g (fun i => (x i).2) := by
  obtain ⟨a, b⟩ := w
  simp only [evDir]
  set X1 : κ → mixedEmbedding.mixedSpace F := fun i => evI F (a i) with hX1
  set Y : κ → mixedEmbedding.mixedSpace F := fun i => evI F (b i) with hY
  simp only [schr, pureA]
  have hfin : (fun i => ((x + (realAd F t • (a, b)).1) i).2) = fun i => (x i).2 := by
    funext i
    change (x i).2 + (realAd F t).2 * (a i).2 = _
    rw [realAd_snd, zero_mul, add_zero]
  have harch : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + (realAd F t • (a, b)).1) i).1) =
      (fun i => evI F (x i)) + t • X1 := by
    funext i
    change evHom F (x i + realAd F t * a i) = evHom F (x i) + t • evHom F (a i)
    rw [map_add, map_mul, evHom_realAd, Algebra.smul_def]
  set A := x ⬝ᵥ (realAd F t • (a, b)).2 + ⅟(2 : AF F) * ((realAd F t • (a, b)).1 ⬝ᵥ (realAd F t • (a, b)).2) with hAdef
  have hA : A = realAd F t * (x ⬝ᵥ b + ⅟(2 : AF F) * (realAd F t * (a ⬝ᵥ b))) := by
    rw [hAdef]
    simp only [Prod.smul_fst, Prod.smul_snd, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  have hAt : At (evI F) A := by
    intro v hv
    rw [smul_eq_mul, hA, ← mul_assoc]
    have hv1 : v.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hv)
    have hvr : v * realAd F t = 0 :=
      Prod.ext (by change v.1 * (realAd F t).1 = 0; rw [hv1, zero_mul])
        (by change v.2 * (realAd F t).2 = 0; rw [realAd_snd, mul_zero])
    rw [hvr, zero_mul]
  have htr : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F A) =
      t * trForm Y (fun i => evI F (x i)) +
        t ^ 2 * (1 / 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (X1 ⬝ᵥ Y)) := by
    have e1 : evI F A = algebraMap ℝ (mixedEmbedding.mixedSpace F) t * ((⇑(evHom F) ∘ x) ⬝ᵥ (⇑(evHom F) ∘ b) +
        algebraMap ℝ (mixedEmbedding.mixedSpace F) (1 / 2) *
          (algebraMap ℝ (mixedEmbedding.mixedSpace F) t * ((⇑(evHom F) ∘ a) ⬝ᵥ (⇑(evHom F) ∘ b)))) := by
      rw [← evHom_apply, hA, map_mul, map_add, map_mul, map_mul, evHom_realAd, RingHom.map_dotProduct,
        RingHom.map_dotProduct, evHom_invOf_two]
    rw [e1, trForm_apply]
    simp only [← Algebra.smul_def, map_add, map_smul, smul_eq_mul]
    change t * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) ((fun i => evHom F (x i)) ⬝ᵥ Y) +
      1 / 2 * (t * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (X1 ⬝ᵥ Y))) =
      t * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) ((fun i => evHom F (x i)) ⬝ᵥ Y) +
        t ^ 2 * (1 / 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (X1 ⬝ᵥ Y))
    ring
  rw [hψ.2.2 A hAt, htr, hfin, harch]
  ring

theorem hasDerivAt_schr_pureA [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (w : (κ → AF F) × (κ → AF F)) (f : SInf F κ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (x : κ → AF F) :
    HasDerivAt (fun t : ℝ => schr ψ (realAd F t • w) (pureA F f g) x) (pureA F (derOp (evDir w) f) g x) 0 := by
  simp only [schr_pureA ψ hψ]
  set y : κ → mixedEmbedding.mixedSpace F := fun i => evI F (x i) with hy
  set L := trForm (evDir w).2 y with hL
  set c := 1 / 2 * Algebra.trace ℝ (mixedEmbedding.mixedSpace F) ((evDir w).1 ⬝ᵥ (evDir w).2) with hc
  have h0 : HasDerivAt (fun t : ℝ => t * L + t ^ 2 * c) L 0 := by
    exact (((hasDerivAt_id (0 : ℝ)).mul_const L).fun_add ((hasDerivAt_pow 2 (0 : ℝ)).mul_const c)).congr_deriv (by simp)
  have h1 := (h0.ofReal_comp.const_mul (-(2 * Real.pi * Complex.I))).cexp
  have h2 : HasDerivAt (fun t : ℝ => f (y + t • (evDir w).1)) (fderiv ℝ f y (evDir w).1) 0 :=
    (f.differentiableAt (x := y)).hasFDerivAt.hasLineDerivAt _
  have h3 := (h1.fun_mul h2).mul_const (g (fun i => (x i).2))
  refine h3.congr_deriv (Eq.symm ?_)
  change derOp (evDir w) f y * g (fun i => (x i).2) = _
  rw [derOp_apply]
  simp
  left
  ring

def sumPure {ι : Type} [Fintype ι] (g : ι → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (f : ι → SInf F κ) : (κ → AF F) → ℂ :=
  ∑ i, pureA F (f i) (g i)

theorem dH_sumPure (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {ι : Type} [Fintype ι]
    (g : ι → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (f : ι → SInf F κ) (w : (κ → AF F) × (κ → AF F)) :
    dH ψ w (sumPure g f) = sumPure g (derLin ι (evDir w) f) := by
  funext x
  have h := HasDerivAt.fun_sum (u := Finset.univ) fun i _ => hasDerivAt_schr_pureA ψ hψ w (f i) (g i) x
  have e : (fun t : ℝ => schr ψ (realAd F t • w) (sumPure g f) x) =
      fun t => ∑ i, schr ψ (realAd F t • w) (pureA F (f i) (g i)) x := by
    funext t
    simp only [schr, sumPure, Finset.sum_apply, Finset.mul_sum]
  simp only [dH]
  rw [e, h.deriv]
  simp only [sumPure, Finset.sum_apply]
  rfl

theorem wordH_sumPure (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {ι : Type} [Fintype ι]
    (g : ι → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (f : ι → SInf F κ) (l : List ((κ → AF F) × (κ → AF F))) :
    wordH ψ l (sumPure g f) = sumPure g ((l.map evDir).foldr (fun u x => derLin ι u x) f) := by
  induction l with
  | nil => rfl
  | cons w l ih => rw [wordH_cons, ih, dH_sumPure ψ hψ]; rfl

theorem exists_sumPure {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    ∃ (n : ℕ) (g : Fin n → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (f : Fin n → SInf F κ), (∀ i, g i ∈ SB _) ∧
      Φ = sumPure g f := by
  obtain ⟨n, c, p, hp⟩ := Submodule.mem_span_set'.1 hΦ
  choose f g hg he using fun i => (p i).2
  refine ⟨n, g, fun i => c i • f i, hg, ?_⟩
  rw [← hp, sumPure]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [he i, ← GlobalTheory.WeilAdm.pureA_smul]
  rfl

theorem memLp_pureA (μ : @Measure (κ → AF F) (borel _)) (hμ : @Measure.IsAddHaarMeasure _ _ _ (borel _) μ)
    (f : SInf F κ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB _) :
    MemLp (pureA F f g) 2 μ := by
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.WeilAdm.HaarSplit.volume_isAddHaar F κ
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  obtain ⟨ν, hν, C, c, hC, -, -, h, -⟩ := GlobalTheory.WeilAdm.HaarSplit.haar_pure_slice_bounds F κ g hg ⊤ isOpen_univ
  have hc : Continuous (pureA F f g) := by
    have h1 := GlobalTheory.WeilAdm.HaarSplit.continuous_comp_splitE F κ (pureA F f g)
      (Submodule.subset_span ⟨f, g, hg, rfl⟩)
    have h2 := h1.comp (GlobalTheory.WeilAdm.HaarSplit.continuous_splitE_symm F κ)
    convert h2 using 1
    funext x
    simp only [Function.comp_apply, AddEquiv.apply_symm_apply]
  have hf : ∫⁻ z, ‖f z‖ₑ ^ 2 < ⊤ := by
    have := (f.memLp 2 volume).2
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)] at this
    simpa using this
  have hν2 : MemLp (pureA F f g) 2 ν := by
    refine ⟨hc.aestronglyMeasurable, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
    have := (h f).trans_lt (ENNReal.mul_lt_top hC.lt_top hf)
    simpa using this
  rw [Measure.isAddLeftInvariant_eq_smul μ ν]
  exact hν2.smul_measure ENNReal.coe_ne_top

theorem exists_l2_bound_heisenberg_word : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (μ : @Measure (κ → AF F) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∀ Φ ∈ schA F κ, ∀ ℓ : ℕ, ∃ B : ℝ, ∀ l : List ((κ → AF F) × (κ → AF F)), l.length ≤ ℓ → (∀ w ∈ l, IsArchUnit w) → ∫⁻ x, ‖wordH ψ l Φ x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal B := by
  intro F _ _ κ _ ψ hψ μ hμ Φ hΦ ℓ
  obtain ⟨n, g, f, hg, rfl⟩ := exists_sumPure hΦ
  letI mA : MeasurableSpace (κ → AF F) := borel _
  have hm : ∀ f : Fin n → SInf F κ, MemLp (sumPure g f) 2 μ := fun f =>
    memLp_finset_sum' _ fun i _ => memLp_pureA μ hμ (f i) (hg i)
  have hadd : ∀ f f' : Fin n → SInf F κ, sumPure g (f + f') = sumPure g f + sumPure g f' := by
    intro f f'
    funext x
    simp only [sumPure, Finset.sum_apply, Pi.add_apply, pureA, SchwartzMap.add_apply, add_mul, Finset.sum_add_distrib]
  have hsmul : ∀ (c : ℝ) (f : Fin n → SInf F κ), sumPure g (c • f) = c • sumPure g f := by
    intro c f
    funext x
    simp only [sumPure, Finset.sum_apply, Pi.smul_apply, pureA, SchwartzMap.smul_apply, Complex.real_smul, Finset.mul_sum,
      mul_assoc]
  let T : (Fin n → SInf F κ) →ₗ[ℝ] Lp ℂ 2 μ :=
    { toFun := fun f => (hm f).toLp _
      map_add' := fun f f' => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (hadd f f'))
      map_smul' := fun c f => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (Filter.EventuallyEq.of_eq (hsmul c f)) }
  obtain ⟨B, hB⟩ := exists_bound_foldr (derLin (F := F) (κ := κ) (Fin n)) f ℓ T
  refine ⟨B ^ 2, fun l hl hu => ?_⟩
  have h1 := hB (l.map evDir) (by simpa using hl) (by
    intro u hu'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hu'
    rw [Prod.norm_def, max_le_iff]
    exact ⟨(pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ((hu w hw).2 i).1,
      (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ((hu w hw).2 i).2⟩)
  rw [wordH_sumPure ψ hψ]
  set f' := (l.map evDir).foldr (fun u x => derLin (F := F) (κ := κ) (Fin n) u x) f with hf'
  have h2 : eLpNorm (sumPure g f') 2 μ ≤ ENNReal.ofReal B := by
    have h3 : ‖T f'‖ = (eLpNorm (sumPure g f') 2 μ).toReal := Lp.norm_toLp _ (hm f')
    rw [← ENNReal.ofReal_toReal (hm f').2.ne, ← h3]
    exact ENNReal.ofReal_le_ofReal h1
  have hB0 : 0 ≤ B := (norm_nonneg _).trans h1
  have h4 : ∫⁻ x, ‖sumPure g f' x‖ₑ ^ 2 ∂μ = eLpNorm (sumPure g f') 2 μ ^ 2 := by
    have := eLpNorm_nnreal_pow_eq_lintegral (f := sumPure g f') (μ := μ) (p := 2) (by norm_num)
    simpa using this.symm
  rw [h4, ENNReal.ofReal_pow hB0]
  exact pow_le_pow_left' h2 2

end GlobalTheory.ThetaSobolevBase

end
