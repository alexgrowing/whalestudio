import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicIntegersCompact.IsCompactAdicCompletionIntegers
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct
open MeasureTheory

noncomputable section
namespace GlobalTheory.DiagForm

open scoped Classical
variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField

local instance measAf : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _
local instance borelAf : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩

variable (F κ) in

abbrev Vi : Type := EuclideanSpace ℝ (Fin (Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F)))

variable (F κ) in

abbrev Vf : Type := κ → FiniteAdeleRing (𝓞 F) F

variable (F κ) in

def eI : Vi F κ ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) := ContinuousLinearEquiv.ofFinrankEq (by simp)

def glue (p : Vi F κ × Vf F κ) : κ → AdeleRing (𝓞 F) F := fun i =>
  (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ p.1 i), p.2 i) :
    InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)

variable (F κ) in

def resD : ((κ ⊕ κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] (Vi F κ × Vf F κ → ℂ) where
  toFun φ p := φ (Sum.elim (glue p) (glue p))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (F κ) in

def mu : Measure (Vi F κ × Vf F κ) := (volume : Measure (Vi F κ)).prod Measure.addHaar

variable (F κ) in

def intSub : Submodule ℂ (Vi F κ × Vf F κ → ℂ) where
  carrier := {h | Integrable h (mu F κ)}
  zero_mem' := integrable_zero _ _ _
  add_mem' := Integrable.add
  smul_mem' c _ h := h.smul c

variable (F κ) in

def I0 : intSub F κ →ₗ[ℂ] ℂ where
  toFun h := ∫ p, (h : Vi F κ × Vf F κ → ℂ) p ∂(mu F κ)
  map_add' h h' := integral_add h.2 h'.2
  map_smul' c h := integral_smul c (h : Vi F κ × Vf F κ → ℂ)

variable (F κ) in

def Lext : (Vi F κ × Vf F κ → ℂ) →ₗ[ℂ] ℂ := (LinearMap.exists_extend (I0 F κ)).choose

theorem Lext_apply (h : Vi F κ × Vf F κ → ℂ) (hh : Integrable h (mu F κ)) :
    Lext F κ h = ∫ p, h p ∂(mu F κ) :=
  LinearMap.congr_fun (LinearMap.exists_extend (I0 F κ)).choose_spec ⟨h, hh⟩

variable (F κ) in

def lDiag : ((κ ⊕ κ → AdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ℂ := Lext F κ ∘ₗ resD F κ

variable (F κ) in

def dI : Vi F κ →L[ℝ] (κ ⊕ κ → mixedEmbedding.mixedSpace F) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => Sum.elim (eI F κ u) (eI F κ u)
      map_add' := fun u u' => by funext i; cases i <;> simp
      map_smul' := fun c u => by funext i; cases i <;> simp }

theorem dI_apply (u : Vi F κ) : dI F κ u = Sum.elim (eI F κ u) (eI F κ u) := rfl

theorem norm_le_dI (u : Vi F κ) : ‖u‖ ≤ ‖(eI F κ).symm.toContinuousLinearMap‖ * ‖dI F κ u‖ := by
  have h1 : ‖eI F κ u‖ ≤ ‖dI F κ u‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => by
      simpa [dI_apply] using norm_le_pi_norm (dI F κ u) (Sum.inl j)
  calc ‖u‖ = ‖(eI F κ).symm.toContinuousLinearMap (eI F κ u)‖ := by simp
    _ ≤ ‖(eI F κ).symm.toContinuousLinearMap‖ * ‖eI F κ u‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ _ := by gcongr

variable (F κ) in

def compD : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (Vi F κ) ℂ :=
  SchwartzMap.compCLM ℂ (dI F κ).hasTemperateGrowth
    ⟨1, ‖(eI F κ).symm.toContinuousLinearMap‖, fun u => (norm_le_dI u).trans (by
      rw [pow_one]; gcongr; linarith)⟩

theorem resD_pureA (f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ)
    (g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (p : Vi F κ × Vf F κ) :
    resD F κ (pureA F f g) p = compD F κ f p.1 * g (Sum.elim p.2 p.2) := by
  change f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (Sum.elim (glue p) (glue p) i).1) *
      g (fun i => (Sum.elim (glue p) (glue p) i).2) = f (dI F κ p.1) * g (Sum.elim p.2 p.2)
  congr 2 <;> funext i <;> cases i <;> simp [glue, dI_apply]

theorem integrable_diag_SB {g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F)) :
    Integrable (fun v : Vf F κ => g (Sum.elim v v)) Measure.addHaar := by
  have hd : Continuous fun v : Vf F κ => (Sum.elim v v : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) :=
    continuous_pi fun i => by cases i <;> exact continuous_apply _
  have hr : Continuous fun z : κ ⊕ κ → FiniteAdeleRing (𝓞 F) F => fun j => z (Sum.inl j) :=
    continuous_pi fun j => continuous_apply _
  refine (hg.1.continuous.comp hd).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (hg.2.isCompact.image hr) fun v hv => ?_
  by_contra h
  exact hv ⟨Sum.elim v v, subset_tsupport _ h, rfl⟩

theorem integrable_resD_pureA (f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ)
    {g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F)) :
    Integrable (resD F κ (pureA F f g)) (mu F κ) := by
  have e : resD F κ (pureA F f g) = fun p => compD F κ f p.1 * g (Sum.elim p.2 p.2) :=
    funext (resD_pureA f g)
  rw [e]
  exact (compD F κ f).integrable.mul_prod (integrable_diag_SB hg)

theorem integrable_resD {φ : (κ ⊕ κ → AdeleRing (𝓞 F) F) → ℂ} (hφ : φ ∈ schA F (κ ⊕ κ)) :
    Integrable (resD F κ φ) (mu F κ) := by
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    exact integrable_resD_pureA f hg
  | zero => rw [map_zero]; exact integrable_zero _ _ _
  | add x y _ _ hx hy => rw [map_add]; exact hx.add hy
  | smul c x _ hx => rw [map_smul]; exact hx.smul c

theorem lDiag_pureA (f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ)
    {g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F)) :
    lDiag F κ (pureA F f g) = (∫ v : Vf F κ, g (Sum.elim v v) ∂Measure.addHaar) *
      SchwartzMap.integralCLM ℂ (volume : Measure (Vi F κ)) (compD F κ f) := by
  rw [lDiag, LinearMap.comp_apply, Lext_apply _ (integrable_resD_pureA f hg),
    SchwartzMap.integralCLM_apply]
  have e : resD F κ (pureA F f g) = fun p => compD F κ f p.1 * g (Sum.elim p.2 p.2) :=
    funext (resD_pureA f g)
  rw [e, mu]
  exact (integral_prod_mul (fun u => compD F κ f u) (fun v : Vf F κ => g (Sum.elim v v))).trans (mul_comm _ _)

theorem lDiag_adm : lDiag F κ ∈ (adeleClass F).adm (κ ⊕ κ) := by
  intro g hg
  refine ⟨(∫ v : Vf F κ, g (Sum.elim v v) ∂Measure.addHaar) •
    ((SchwartzMap.integralCLM ℂ (volume : Measure (Vi F κ))).comp (compD F κ)), fun f => ?_⟩
  rw [lDiag_pureA f hg]
  rfl

instance mu_inv : (mu F κ).IsAddRightInvariant := by unfold mu; infer_instance

theorem dot_anti (a y : κ → AF F) : Sum.elim a a ⬝ᵥ Sum.elim y (-y) = 0 := by
  simp [dotProduct, Fintype.sum_sum_type]

def shiftOf (x : κ → AF F) : Vi F κ × Vf F κ :=
  ((eI F κ).symm (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1), fun i => (x i).2)

theorem glue_add_shiftOf (p : Vi F κ × Vf F κ) (x : κ → AF F) : glue (p + shiftOf x) = glue p + x := by
  funext i
  refine Prod.ext ?_ ?_
  · show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ (p.1 + (eI F κ).symm _) i) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F κ p.1 i) + (x i).1
    rw [map_add, ContinuousLinearEquiv.apply_symm_apply, Pi.add_apply, map_add, RingEquiv.symm_apply_apply]
  · rfl

theorem resD_schr (ψ : AddChar (AF F) ℂ) (x y : κ → AF F) (φ : (κ ⊕ κ → AF F) → ℂ) :
    resD F κ (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = fun p => resD F κ φ (p + shiftOf x) := by
  funext p
  show ψ (Sum.elim (glue p) (glue p) ⬝ᵥ Sum.elim y (-y) + ⅟(2 : AF F) * (Sum.elim x x ⬝ᵥ Sum.elim y (-y))) *
      φ (Sum.elim (glue p) (glue p) + Sum.elim x x) = φ (Sum.elim (glue (p + shiftOf x)) (glue (p + shiftOf x)))
  rw [dot_anti, dot_anti, mul_zero, add_zero, AddChar.map_zero_eq_one, one_mul, glue_add_shiftOf]
  congr 1
  funext i
  cases i <;> rfl

theorem lDiag_schr (ψ : AddChar (AF F) ℂ) (x y : κ → AF F) {φ : (κ ⊕ κ → AF F) → ℂ}
    (hφ : φ ∈ schA F (κ ⊕ κ)) : lDiag F κ (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = lDiag F κ φ := by
  have hi := integrable_resD hφ
  rw [lDiag, LinearMap.comp_apply, LinearMap.comp_apply, resD_schr,
    Lext_apply _ (hi.comp_add_right (shiftOf x)), Lext_apply _ hi]
  exact integral_add_right_eq_self _ _

theorem exists_lDiag_ne : ∃ φ ∈ schA F (κ ⊕ κ), lDiag F κ φ ≠ 0 := by
  obtain ⟨hO, hK⟩ := PI.IntAdCpctOpenWork.main F
  set O := {x : FiniteAdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), x v ∈ v.adicCompletionIntegers F}
  have h0 : (0 : FiniteAdeleRing (𝓞 F) F) ∈ O := fun v => (v.adicCompletionIntegers F).zero_mem
  set U : Set (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) := Set.univ.pi fun _ => O
  have hUo : IsOpen U := isOpen_set_pi Set.finite_univ fun _ _ => hO
  have hUc : IsCompact U := isCompact_univ_pi fun _ => hK
  set g : (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) → ℂ := U.indicator fun _ => 1
  have hg : g ∈ SB (κ ⊕ κ → FiniteAdeleRing (𝓞 F) F) :=
    ⟨(LocallyConstant.indicator (1 : LocallyConstant _ ℂ) ⟨hUc.isClosed, hUo⟩).isLocallyConstant,
      HasCompactSupport.intro hUc fun z hz => Set.indicator_of_notMem hz _⟩
  set V : Set (Vf F κ) := Set.univ.pi fun _ => O
  have hVo : IsOpen V := isOpen_set_pi Set.finite_univ fun _ _ => hO
  have hVc : IsCompact V := isCompact_univ_pi fun _ => hK
  have hgV : (fun v : Vf F κ => g (Sum.elim v v)) = V.indicator fun _ => (1 : ℂ) := by
    funext v
    simp only [g, U, V, Set.indicator_apply, Set.mem_univ_pi, Sum.forall, Sum.elim_inl, Sum.elim_inr, and_self]
  have hc : (∫ v : Vf F κ, g (Sum.elim v v) ∂Measure.addHaar) ≠ 0 := by
    rw [hgV, integral_indicator_const _ hVo.measurableSet]
    have hpos : 0 < (Measure.addHaar : Measure (Vf F κ)) V := hVo.measure_pos _ ⟨0, fun i _ => h0⟩
    have hfin : (Measure.addHaar : Measure (Vf F κ)) V < ⊤ := hVc.measure_lt_top
    have : 0 < (Measure.addHaar : Measure (Vf F κ)).real V := ENNReal.toReal_pos hpos.ne' hfin.ne
    simpa using this.ne'
  let b : ContDiffBump (0 : κ ⊕ κ → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let f : SchwartzMap (κ ⊕ κ → mixedEmbedding.mixedSpace F) ℂ :=
    h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hT : SchwartzMap.integralCLM ℂ (volume : Measure (Vi F κ)) (compD F κ f) ≠ 0 := by
    rw [SchwartzMap.integralCLM_apply]
    have e : ∀ u, compD F κ f u = ((b (dI F κ u) : ℝ) : ℂ) := fun u => rfl
    simp only [e, integral_complex_ofReal]
    have hcs : HasCompactSupport fun u : Vi F κ => b (dI F κ u) := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : Vi F κ)
        (‖(eI F κ).symm.toContinuousLinearMap‖ * 2)) fun u hu => b.zero_of_le_dist ?_
      rw [dist_zero_right]
      by_contra h
      refine hu (mem_closedBall_zero_iff.2 ((norm_le_dI u).trans ?_))
      exact mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge h)) (norm_nonneg _)
    have hpos := (b.continuous.comp (dI F κ).continuous).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (μ := (volume : Measure (Vi F κ))) (x := 0) hcs (fun u => b.nonneg) (by
        simp only [Function.comp_apply, map_zero]
        rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
        exact one_ne_zero)
    exact_mod_cast hpos.ne'
  refine ⟨pureA F f g, Submodule.subset_span ⟨f, g, hg, rfl⟩, ?_⟩
  rw [lDiag_pureA f hg]
  exact mul_ne_zero hc hT

end GlobalTheory.DiagForm

namespace GlobalTheory

theorem diagLagrangian_form : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ],
    ∃ l : ((κ ⊕ κ → AF F) → ℂ) →ₗ[ℂ] ℂ, l ∈ (adeleClass F).adm (κ ⊕ κ) ∧
      (∀ (x y : κ → AF F), ∀ φ ∈ schA F (κ ⊕ κ), l (schr ψ (Sum.elim x x, Sum.elim y (-y)) φ) = l φ) ∧
      ∃ φ ∈ schA F (κ ⊕ κ), l φ ≠ 0 := by
  intro F _ _ ψ κ _
  exact ⟨DiagForm.lDiag F κ, DiagForm.lDiag_adm, fun x y φ hφ => DiagForm.lDiag_schr ψ x y hφ,
    DiagForm.exists_lDiag_ne⟩

end GlobalTheory
