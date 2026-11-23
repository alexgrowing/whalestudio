import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicAddCharEqArchimedeanMulFinprodLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierBijOnSchwartzBruhatFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointsIndicatorFourierSelfUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanSchwartzTraceFourierBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAdelicPureTensorEqProductLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPoissonSummationAnyHaarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnramifiedAwayDifferent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.WeylFourier

section General

variable {R : Type} [CommRing R] {κ : Type} [Fintype κ] [MeasurableSpace (κ → R)]

def ft (ψ : AddChar R ℂ) (μ : Measure (κ → R)) (Φ : (κ → R) → ℂ) : (κ → R) → ℂ :=
  fun y => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ

def intSub (ψ : AddChar R ℂ) (μ : Measure (κ → R)) : Submodule ℂ ((κ → R) → ℂ) where
  carrier := {Φ | ∀ y, Integrable (fun x => Φ x * ψ (x ⬝ᵥ y)) μ}
  zero_mem' := fun y => by simp only [Pi.zero_apply, zero_mul]; exact integrable_zero _ _ _
  add_mem' := fun {a b} ha hb y => by
    simp only [Pi.add_apply, add_mul]; exact (ha y).add (hb y)
  smul_mem' := fun c a ha y => by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]; exact (ha y).const_mul c

def ftL (ψ : AddChar R ℂ) (μ : Measure (κ → R)) : intSub ψ μ →ₗ[ℂ] (κ → R) → ℂ where
  toFun Φ := ft ψ μ Φ
  map_add' a b := funext fun y => by
    simp only [ft, Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (a.2 y) (b.2 y)
  map_smul' c a := funext fun y => by
    simp only [ft, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
    exact integral_const_mul c _

def ftE (ψ : AddChar R ℂ) (μ : Measure (κ → R)) : ((κ → R) → ℂ) →ₗ[ℂ] (κ → R) → ℂ :=
  (LinearMap.exists_extend (ftL ψ μ)).choose

theorem ftE_eq (ψ : AddChar R ℂ) (μ : Measure (κ → R)) {Φ : (κ → R) → ℂ} (hΦ : Φ ∈ intSub ψ μ) :
    ftE ψ μ Φ = ft ψ μ Φ :=
  LinearMap.congr_fun (LinearMap.exists_extend (ftL ψ μ)).choose_spec ⟨Φ, hΦ⟩

variable [Invertible (2 : R)]

theorem schr_mul_psi (ψ : AddChar R ℂ) (w : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) (x y : κ → R) :
    schr ψ w Φ x * ψ (x ⬝ᵥ y) = ψ (-(w.1 ⬝ᵥ y) - ⅟(2 : R) * (w.1 ⬝ᵥ w.2)) *
      (Φ (x + w.1) * ψ ((x + w.1) ⬝ᵥ (y + w.2))) := by
  simp only [schr]
  have e : (x + w.1) ⬝ᵥ (y + w.2) = (x ⬝ᵥ w.2 + ⅟(2 : R) * (w.1 ⬝ᵥ w.2)) + x ⬝ᵥ y +
      -(-(w.1 ⬝ᵥ y) - ⅟(2 : R) * (w.1 ⬝ᵥ w.2)) := by
    have h2 : (⅟(2 : R)) + ⅟(2 : R) = 1 := invOf_two_add_invOf_two
    simp only [add_dotProduct, dotProduct_add]
    linear_combination (-(w.1 ⬝ᵥ w.2)) * h2
  have hc : ψ (-(w.1 ⬝ᵥ y) - ⅟(2 : R) * (w.1 ⬝ᵥ w.2)) * ψ (-(-(w.1 ⬝ᵥ y) - ⅟(2 : R) * (w.1 ⬝ᵥ w.2))) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  rw [e, AddChar.map_add_eq_mul ψ (_ + _) (-_), AddChar.map_add_eq_mul ψ (x ⬝ᵥ w.2 + ⅟(2 : R) * (w.1 ⬝ᵥ w.2)) (x ⬝ᵥ y)]
  linear_combination (-(ψ (x ⬝ᵥ w.2 + ⅟(2 : R) * (w.1 ⬝ᵥ w.2)) * Φ (x + w.1) * ψ (x ⬝ᵥ y))) * hc

variable [MeasurableAdd (κ → R)] (μ : Measure (κ → R)) [μ.IsAddRightInvariant]

theorem schr_mem (ψ : AddChar R ℂ) (w : (κ → R) × (κ → R)) {Φ : (κ → R) → ℂ} (hΦ : Φ ∈ intSub ψ μ) :
    schr ψ w Φ ∈ intSub ψ μ := fun y => by
  simp only [schr_mul_psi]
  exact ((hΦ (y + w.2)).comp_add_right w.1).const_mul _

theorem ft_schr (ψ : AddChar R ℂ) (w : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) :
    ft ψ μ (schr ψ w Φ) = schr ψ (w.2, -w.1) (ft ψ μ Φ) := funext fun y => by
  simp only [ft, schr_mul_psi]
  rw [integral_const_mul, integral_add_right_eq_self (fun x => Φ x * ψ (x ⬝ᵥ (y + w.2))) w.1]
  simp only [schr]
  congr 2
  rw [dotProduct_neg, dotProduct_neg, dotProduct_comm y, dotProduct_comm w.2]
  ring

end General

end GlobalTheory.WeylFourier

namespace GlobalTheory.WeylFourier

open scoped Classical

section Adelic

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem evI_dot (x y : κ → AF F) :
    evI F (x ⬝ᵥ y) = (fun i => evI F (x i)) ⬝ᵥ (fun i => evI F (y i)) := by
  have h : ∀ a : AF F, evI F a = ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (fstA F).toRingHom) a :=
    fun a => rfl
  simp only [h, dotProduct, map_sum, map_mul]

theorem evFin_dot (v : Pl F) (x y : κ → AF F) :
    evFin F v (x ⬝ᵥ y) = (fun i => evFin F v (x i)) ⬝ᵥ (fun i => evFin F v (y i)) := by
  simp only [dotProduct, map_sum, map_mul]

theorem evFin_mem (a : AF F) : ∀ᶠ v in cofinite, evFin F v a ∈ v.adicCompletionIntegers F :=
  a.2.2.mono fun _ hv => hv

theorem psiUnr_eventually (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) : ∀ᶠ v in cofinite, PsiUnr ψ v := by
  have hne : differentIdeal ℤ (𝓞 F) ≠ 0 := by rw [Ideal.zero_eq_bot]; exact differentIdeal_ne_bot
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hne).subset fun v hv => ?_)
  by_contra h
  exact hv (GlobalTheory.StdCharUnrF.psiUnr_of_not_le F ψ hψ v fun hle => h (Ideal.dvd_iff_le.2 hle))

theorem pure_mem_schA (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (hφ : IsFam φ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ schA F κ :=
  Submodule.subset_span ⟨f, fun y => ∏ᶠ v, φ v fun i => evalV F v (y i),
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hφ.1 hφ.2, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hφ.1 hφ.2⟩, rfl⟩

def archT (f : SInf F κ) (b : κ → mixedEmbedding.mixedSpace F) : (κ → mixedEmbedding.mixedSpace F) → ℂ :=
  fun z => f z * Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (z ⬝ᵥ b) : ℝ))

def finT (ψ : AddChar (AF F) ℂ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (y : κ → AF F) : ∀ v : Pl F, (κ → Fv F v) → ℂ :=
  fun v z => φ v z * GlobalTheory.LatVac.psiAt ψ v (z ⬝ᵥ fun i => evFin F v (y i))

theorem finT_isFam (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) (hφ : IsFam φ)
    (y : κ → AF F) : IsFam (finT ψ φ y) := by
  refine ⟨fun v => ?_, ?_⟩
  · have e : finT ψ φ y v = schr (GlobalTheory.LatVac.psiAt ψ v) (0, fun i => evFin F v (y i)) (φ v) := by
      funext z
      simp only [finT, schr, zero_dotProduct, mul_zero, add_zero]
      exact mul_comm _ _
    rw [e]
    exact GlobalTheory.SchrSBFin.schr_mem_SB v _ (GlobalTheory.SchrSB.continuous_psiAt ψ hψ.1 v) _ _ (hφ.1 v)
  · filter_upwards [hφ.2, psiUnr_eventually ψ hψ, Filter.eventually_all.2 fun i => evFin_mem (y i)] with v h1 h2 h3
    funext z
    simp only [finT, h1, ind]
    by_cases hz : ∀ i, z i ∈ v.adicCompletionIntegers F
    · have hmem : (z ⬝ᵥ fun i => evFin F v (y i)) ∈ v.adicCompletionIntegers F :=
        sum_mem fun i _ => mul_mem (hz i) (h3 i)
      have h4 := (h2 1).2 (one_mem _) _ hmem
      rw [one_mul] at h4
      rw [Set.indicator_of_mem (show z ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hz),
        GlobalTheory.LatVac.psiAt_apply, h4, mul_one]
    · rw [Set.indicator_of_notMem (show z ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hz), zero_mul]

end Adelic

end GlobalTheory.WeylFourier

namespace GlobalTheory.WeylFourier

open scoped Classical

section Adelic2

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem archT_continuous (f : SInf F κ) (b : κ → mixedEmbedding.mixedSpace F) : Continuous (archT f b) :=
  f.continuous.mul (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
    ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).continuous_of_finiteDimensional.comp
      (continuous_id.dotProduct continuous_const)))))

theorem archT_integrable [MeasurableSpace (κ → mixedEmbedding.mixedSpace F)] [BorelSpace (κ → mixedEmbedding.mixedSpace F)]
    (μi : Measure (κ → mixedEmbedding.mixedSpace F)) [μi.IsAddHaarMeasure] (f : SInf F κ) (b : κ → mixedEmbedding.mixedSpace F) :
    Integrable (archT f b) μi := by
  have hc : Continuous fun z : κ → mixedEmbedding.mixedSpace F => Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (z ⬝ᵥ b) : ℝ)) :=
    Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F)).continuous_of_finiteDimensional.comp
        (continuous_id.dotProduct continuous_const))))
  exact f.integrable.mul_bdd hc.aestronglyMeasurable
    (ae_of_all _ fun z => (GlobalTheory.StdCharFromIsStd.norm_exp_real _).le)

theorem pure_mul_psi (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ)
    (hφ : IsFam φ) (x y : κ → AF F) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x * ψ (x ⬝ᵥ y) = archT f (fun i => evI F (y i)) (fun i => evI F (x i)) *
      ∏ᶠ v, finT ψ φ y v (fun i => evFin F v (x i)) := by
  obtain ⟨hfin, hsplit⟩ := GlobalTheory.T.adelicAddChar_eq_archimedean_mul_finprod_local F ψ hψ.1 (x ⬝ᵥ y)
  rw [hsplit, GlobalTheory.StdCharFromIsStd.psi_pairA hψ]
  have e1 : InfiniteAdeleRing.ringEquiv_mixedSpace F (fstA F (x ⬝ᵥ y)) =
      (fun i => evI F (x i)) ⬝ᵥ (fun i => evI F (y i)) := evI_dot x y
  rw [e1]
  simp only [evFin_dot] at hfin ⊢
  have hφfin : (Function.mulSupport fun v : Pl F => φ v (fun i => evFin F v (x i))).Finite := by
    have hev : ∀ᶠ v in cofinite, φ v = ind κ v ∧ ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F :=
      hφ.2.and (Filter.eventually_all.2 fun i => evFin_mem (x i))
    refine (Filter.eventually_cofinite.1 hev).subset fun v hv hP => hv ?_
    show φ v _ = 1
    rw [hP.1]
    simp only [ind]
    exact Set.indicator_of_mem (show (fun i => evFin F v (x i)) ∈ {z : κ → Fv F v | ∀ i, z i ∈ v.adicCompletionIntegers F}
      from hP.2) 1
  simp only [finT, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, archT]
  rw [finprod_mul_distrib hφfin hfin]
  ring

end Adelic2

end GlobalTheory.WeylFourier

namespace GlobalTheory.WeylFourier
theorem act_weyl {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ] {R : Type} [CommRing R] [Algebra F R]
    (w : (κ → R) × (κ → R)) :
    act ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R)) w = (w.2, -w.1) := by
  have h1 : ((-1 : Matrix κ κ F).map (algebraMap F R)) = -1 := by
    rw [Matrix.map_neg _ (map_neg _), Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Matrix.fromBlocks_map, act_fromBlocks, h1]
  simp [Matrix.neg_mulVec]
end GlobalTheory.WeylFourier

namespace GlobalTheory.WeylFourier

open scoped Classical

theorem weyl_hasOp : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ],
    HasOp ψ (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) := by
  intro F _ _ hTR ψ hψ κ _ _
  letI mA : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mI : MeasurableSpace (κ → mixedEmbedding.mixedSpace F) := borel _
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := ⟨rfl⟩
  letI mV : ∀ v : Pl F, MeasurableSpace (κ → Fv F v) := fun _ => borel _
  haveI bV : ∀ v : Pl F, BorelSpace (κ → Fv F v) := fun _ => ⟨rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (κ → AF F), μ.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  obtain ⟨μi, hμi⟩ : ∃ μ : Measure (κ → mixedEmbedding.mixedSpace F), μ.IsAddHaarMeasure :=
    ⟨Measure.addHaar, inferInstance⟩
  obtain ⟨μv, hμv, hμv1⟩ : ∃ μv : ∀ v : Pl F, Measure (κ → Fv F v), (∀ v, (μv v).IsAddHaarMeasure) ∧
      ∀ v, μv v {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1 := by
    let K : ∀ v : Pl F, TopologicalSpace.PositiveCompacts (κ → Fv F v) := fun v =>
      ⟨⟨Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)),
        isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v⟩, by
          show (interior (Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)))).Nonempty
          rw [(isOpen_set_pi Set.finite_univ fun _ _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v).interior_eq]
          exact ⟨0, fun i _ => (v.adicCompletionIntegers F).zero_mem⟩⟩
    refine ⟨fun v => Measure.addHaarMeasure (K v), fun v => inferInstance, fun v => ?_⟩
    have e : {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} = (K v : Set (κ → Fv F v)) := by
      ext x; simp [K]
    rw [e]
    exact Measure.addHaarMeasure_self
  haveI := hμv
  obtain ⟨c₀, hc₀, hpure⟩ := GlobalTheory.T.integral_adelic_pureTensor_eq_product_local F κ μ μi μv hμv1
  obtain ⟨ei', hei'bij, hei'⟩ := GlobalTheory.T.exists_archimedeanSchwartz_traceFourier_bijective F κ μi
  obtain ⟨c, hc, hθ⟩ := GlobalTheory.T.adelicPoisson_summation_anyHaar F hTR ψ hψ κ μ
  have hψc : ∀ v, Continuous (GlobalTheory.LatVac.psiAt ψ v) := fun v => GlobalTheory.SchrSB.continuous_psiAt ψ hψ.1 v
  have hsub : ∀ v, ∀ φ ∈ SB (κ → Fv F v), φ ∈ intSub (GlobalTheory.LatVac.psiAt ψ v) (μv v) := fun v φ hφ y =>
    (hφ.1.continuous.mul ((hψc v).comp (continuous_id.dotProduct continuous_const))).integrable_of_hasCompactSupport
      hφ.2.mul_right
  let ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ := fun v => ftE (GlobalTheory.LatVac.psiAt ψ v) (μv v)
  have hev : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = ft (GlobalTheory.LatVac.psiAt ψ v) (μv v) φ :=
    fun v φ hφ => ftE_eq _ _ (hsub v φ hφ)
  have hbij : ∀ v, Set.BijOn (ev v) (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _) := fun v =>
    (GlobalTheory.T.fourier_bijOn_schwartzBruhat_finitePlace F v (GlobalTheory.LatVac.psiAt ψ v) (hψc v) (fun t => GlobalTheory.StdCharFromIsStd.norm_psi hψ _)
      (GlobalTheory.PsiNontriv.psiAt_ne_one ψ hψ v) κ (μv v)).congr fun φ hφ => (hev v φ hφ).symm
  have hind : ∀ᶠ v in cofinite, ev v (ind κ v) = ind κ v := by
    filter_upwards [psiUnr_eventually ψ hψ] with v hv
    rw [hev v (ind κ v) (GlobalTheory.StdVacuum.indicator_mem_SB v)]
    exact GlobalTheory.T.integralPointsIndicator_fourier_self_unramified F v (GlobalTheory.LatVac.psiAt ψ v) (fun x => hv x) κ (μv v) (hμv1 v)
  have hpureE : ∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), IsFam φ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ intSub ψ μ ∧
      ft ψ μ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c₀ • ei' f) (fun v => ev v (φ v)) := by
    intro f φ hφ
    have hφ' : ∀ y, IsFam (finT ψ φ y) := finT_isFam ψ hψ φ hφ
    have hfun : ∀ y, (fun x => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x * ψ (x ⬝ᵥ y)) = fun x =>
        archT f (fun i => evI F (y i)) (fun i => evI F (x i)) * ∏ᶠ v, finT ψ φ y v (fun i => evFin F v (x i)) :=
      fun y => funext fun x => pure_mul_psi ψ hψ f φ hφ x y
    refine ⟨fun y => ?_, funext fun y => ?_⟩
    · rw [hfun y]
      exact (hpure _ _ (archT_continuous f _) (archT_integrable μi f _) (hφ' y)).1
    · show ∫ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x * ψ (x ⬝ᵥ y) ∂μ = _
      rw [hfun y, (hpure _ _ (archT_continuous f _) (archT_integrable μi f _) (hφ' y)).2]
      have h2 : ∀ v, ev v (φ v) (fun i => evFin F v (y i)) = ∫ x, finT ψ φ y v x ∂(μv v) := fun v => by
        rw [hev v _ (hφ.1 v)]; rfl
      have h3 : (c₀ • ei' f) (fun i => evI F (y i)) = c₀ * ∫ x, archT f (fun i => evI F (y i)) x ∂μi := by
        have h4 := hei' f (fun i => evI F (y i))
        simp only [archT]
        rw [← h4]
        rfl
      show _ = (c₀ • ei' f) (fun i => evI F (y i)) * ∏ᶠ v, ev v (φ v) (fun i => evFin F v (y i))
      rw [h3, finprod_congr h2]
  refine ⟨ftE ψ μ, c, c₀ • ei', ev, hc, fun g => ?_, hbij, fun v w φ hφ => ?_, hind, fun f φ hφ => ?_⟩
  · obtain ⟨h, hh⟩ := hei'bij.2 (c₀⁻¹ • g)
    exact ⟨h, by rw [ContinuousLinearMap.smul_apply, hh, smul_smul, mul_inv_cancel₀ hc₀, one_smul]⟩
  · rw [act_weyl, hev v _ (GlobalTheory.SchrSBFin.schr_mem_SB v _ (hψc v) w φ hφ), hev v φ hφ, ft_schr]
  · obtain ⟨hmem, hft⟩ := hpureE f φ hφ
    have he : ftE ψ μ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c₀ • ei' f) (fun v => ev v (φ v)) :=
      (ftE_eq ψ μ hmem).trans hft
    have hfam : IsFam fun v => ev v (φ v) :=
      ⟨fun v => (hbij v).mapsTo (hφ.1 v), by filter_upwards [hφ.2, hind] with v h1 h2; rw [h1, h2]⟩
    refine ⟨he, fun w => ?_, ?_⟩
    · rw [act_weyl, ftE_eq ψ μ (schr_mem μ ψ w hmem), ft_schr, ftE_eq ψ μ hmem]
    · have hm : ft ψ μ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∈ schA F κ := by
        rw [hft]; exact pure_mem_schA _ _ hfam
      rw [he, ← hft]
      exact hθ _ (pure_mem_schA f φ hφ) hm

end GlobalTheory.WeylFourier
