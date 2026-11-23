import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfAeFundamentalDomain

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TowerSmooth

open GlobalTheory.WeilVacMove

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {k : ℕ}

def rayHom (v : Fin k → ℝ) : ℝ →+ (Fin k → ℝ) where
  toFun s := s • v
  map_zero' := zero_smul _ _
  map_add' a b := add_smul a b v

theorem continuous_rayHom (v : Fin k → ℝ) : Continuous (rayHom v) :=
  continuous_id.smul continuous_const

def coordC (i : Fin k) : (Fin k → ℝ) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)

theorem clm_eq_sum (l : (Fin k → ℝ) →L[ℝ] ℂ) : l = ∑ i, l (Pi.single i 1) • coordC i := by
  ext v
  have e : ∀ i, (Pi.single i (v i) : Fin k → ℝ) = v i • Pi.single i (1 : ℝ) := by
    intro i; ext j; by_cases h : j = i
    · subst h; simp
    · simp [h]
  conv_lhs => rw [← Finset.univ_sum_single v]
  simp only [map_sum, e, map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, coordC, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply, smul_eq_mul, Complex.real_smul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem hasFDerivAt_coord (hψ : IsStdChar D ψ (-1)) {M : (Fin k → ℝ) →+ WO S T} (hM : Continuous M)
    (hM0 : ∀ t, (M t).map (finPart D) = 0) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g)
    {lam : AF D.host.F →+ ℂ} (hl : Continuous lam)
    (hlam : ∀ a, sndA D.host.F a = 0 → ψ a = Complex.exp (lam a)) (p : WO S T) (t : Fin k → ℝ) :
    HasFDerivAt (fun t' => g (p + M t'))
      (∑ i, (dLine ψ S T (M.comp (rayHom (Pi.single i 1))) g (p + M t) -
        phase lam S T (M (Pi.single i 1)) (p + M t) * g (p + M t)) • coordC i) t := by
  have hs := hg.smooth k M hM hM0 p
  have hd : HasFDerivAt (fun t' => g (p + M t')) (fderiv ℝ (fun t' => g (p + M t')) t) t :=
    ((hs.differentiable (by simp)) t).hasFDerivAt
  convert hd using 1
  conv_rhs => rw [clm_eq_sum (fderiv ℝ (fun t' => g (p + M t')) t)]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  set e : Fin k → ℝ := Pi.single i 1
  set N : ℝ →+ WO S T := M.comp (rayHom e)
  have hN : Continuous N := hM.comp (continuous_rayHom e)
  have hN0 : ∀ s, (N s).map (finPart D) = 0 := fun s => hM0 _
  have hN1 : N 1 = M e := by simp [N, rayHom]
  set x := p + M t
  set ph := phase lam S T (M e) x
  have hline : HasDerivAt (fun s : ℝ => t + s • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add t
  have h1 : HasDerivAt (fun s : ℝ => g (p + M (t + s • e))) (fderiv ℝ (fun t' => g (p + M t')) t e) 0 := by
    have hd' : HasFDerivAt (fun t' => g (p + M t')) (fderiv ℝ (fun t' => g (p + M t')) t) (t + (0 : ℝ) • e) := by
      rw [zero_smul, add_zero]; exact hd
    exact hd'.comp_hasDerivAt (0 : ℝ) hline
  have h0 : HasDerivAt (fun s : ℝ => (s : ℂ) * -ph) (-ph) 0 := by
    simpa using (HasDerivAt.ofReal_comp (hasDerivAt_id (0 : ℝ))).mul_const (-ph)
  have hh := (hasDerivAt_zero_and_isTheta hψ hN hN0 hg).1 x
  have h2 := h0.cexp.mul hh
  have eq : (fun s : ℝ => g (p + M (t + s • e))) =
      fun s : ℝ => Complex.exp ((s : ℂ) * -ph) * heisO ψ S T (N s) g x := by
    funext s
    have hp := psi_sympl_line hl hlam hN hN0 x s
    rw [hN1] at hp
    rw [heisO, hp, ← mul_assoc, ← Complex.exp_add]
    have : (s : ℂ) * -ph + s * ph = 0 := by ring
    rw [this, Complex.exp_zero, one_mul]
    simp only [N, x, AddMonoidHom.comp_apply, rayHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_add, add_assoc]
  rw [eq] at h1
  have hz : N 0 = 0 := map_zero N
  have h3 : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * -ph) * heisO ψ S T (N s) g x)
      (dLine ψ S T N g x - ph * g x) 0 := by
    refine h2.congr_deriv ?_
    rw [hz, heisO_zero]
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul]
    ring
  exact (h1.unique h3).symm

end GlobalTheory.TowerSmooth

namespace GlobalTheory.TowerSmooth

open GlobalTheory.WeilVacMove

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {k : ℕ}

theorem contDiff_integral (hψ : IsStdChar D ψ (-1)) {X : Type} [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] {q : X → WO S T} (hq : Continuous q)
    {M : (Fin k → ℝ) →+ WO S T} (hM : Continuous M) (hM0 : ∀ t, (M t).map (finPart D) = 0)
    (b : Fin k → AF D.host.F) (hb : ∀ i y, symplOH S T (q y) (M (Pi.single i 1)) = b i)
    (g : WO S T → ℂ) (hg : IsThetaFunO ψ S T g) : ContDiff ℝ ∞ fun t => ∫ y, g (q y + M t) ∂ν := by
  obtain ⟨lam, hl, hlam⟩ := exists_log hψ
  let a : Fin k → (Fin k → ℝ) → ℂ := fun i t => lam (b i) + phase lam S T (M (Pi.single i 1)) (M t)
  have ha : ∀ i y t, phase lam S T (M (Pi.single i 1)) (q y + M t) = a i t := by
    intro i y t
    rw [map_add]
    congr 1
    show lam (symplOH S T (q y) (M (Pi.single i 1))) = lam (b i)
    rw [hb]
  have haC : ∀ i, ContDiff ℝ ∞ (a i) := fun i =>
    contDiff_const.add (contDiff_additive ((phase lam S T (M (Pi.single i 1))).comp M)
      (hl.comp (continuous_symplOH S T hM continuous_const)))
  let G : (WO S T → ℂ) → (Fin k → ℝ) → ℂ := fun h t => ∫ y, h (q y + M t) ∂ν
  let N : Fin k → ℝ →+ WO S T := fun i => M.comp (rayHom (Pi.single i 1))
  have hN : ∀ i, Continuous (N i) := fun i => hM.comp (continuous_rayHom _)
  have hN0 : ∀ i s, (N i s).map (finPart D) = 0 := fun i s => hM0 _
  have hdt : ∀ h, IsThetaFunO ψ S T h → ∀ i, IsThetaFunO ψ S T (dLine ψ S T (N i) h) := fun h hh i =>
    (hasDerivAt_zero_and_isTheta hψ (hN i) (hN0 i) hh).2
  have hcq : ∀ t, Continuous fun y => q y + M t := fun t => hq.add continuous_const
  have hint : ∀ h, IsThetaFunO ψ S T h → ∀ t, Integrable (fun y => h (q y + M t)) ν := by
    intro h hh t
    obtain ⟨C, hC⟩ := exists_bound hψ hh
    exact Integrable.of_bound (hh.cont.comp (hcq t)).aestronglyMeasurable C (ae_of_all _ fun y => hC _)
  have hder : ∀ h, IsThetaFunO ψ S T h → ∀ t₀, HasFDerivAt (G h)
      (∑ i, (G (dLine ψ S T (N i) h) t₀ - a i t₀ * G h t₀) • coordC i) t₀ := by
    intro h hh t₀
    obtain ⟨C0, hC0⟩ := exists_bound hψ hh
    have hCd : ∀ i, ∃ C : ℝ, ∀ w, ‖dLine ψ S T (N i) h w‖ ≤ C := fun i => exists_bound hψ (hdt h hh i)
    choose Cd hCd using hCd
    have hA : ∀ i, ∃ C : ℝ, ∀ t ∈ Metric.closedBall t₀ 1, ‖a i t‖ ≤ C := fun i =>
      (isCompact_closedBall t₀ 1).exists_bound_of_continuousOn (haC i).continuous.continuousOn
    choose A hA using hA
    have hA0 : ∀ i, 0 ≤ A i := fun i =>
      (norm_nonneg _).trans (hA i t₀ (Metric.mem_closedBall_self zero_le_one))
    let F' : (Fin k → ℝ) → X → (Fin k → ℝ) →L[ℝ] ℂ := fun t y =>
      ∑ i, (dLine ψ S T (N i) h (q y + M t) - a i t * h (q y + M t)) • coordC i
    have hF' : ∀ y t, HasFDerivAt (fun t => h (q y + M t)) (F' t y) t := by
      intro y t
      have := hasFDerivAt_coord hψ hM hM0 hh hl hlam (q y) t
      simp only [ha] at this
      exact this
    have hbd : ∀ y, ∀ t ∈ Metric.ball t₀ 1, ‖F' t y‖ ≤ ∑ i, (Cd i + A i * C0) * ‖coordC (k := k) i‖ := by
      intro y t ht
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_smul]
      refine mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans (add_le_add (hCd i _) ?_)) (norm_nonneg _)
      rw [norm_mul]
      exact mul_le_mul (hA i t (Metric.ball_subset_closedBall ht)) (hC0 _) (norm_nonneg _) (hA0 i)
    have hF'm : AEStronglyMeasurable (F' t₀) ν := by
      refine Continuous.aestronglyMeasurable ?_
      refine continuous_finsetSum _ fun i _ => ?_
      exact (((hdt h hh i).cont.comp (hcq t₀)).sub (continuous_const.mul (hh.cont.comp (hcq t₀)))).smul
        continuous_const
    have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (F := fun t y => h (q y + M t))
      (F' := F') (x₀ := t₀) (bound := fun _ => ∑ i, (Cd i + A i * C0) * ‖coordC (k := k) i‖)
      (Metric.ball_mem_nhds t₀ zero_lt_one)
      (Filter.Eventually.of_forall fun t => (hh.cont.comp (hcq t)).aestronglyMeasurable) (hint h hh t₀) hF'm
      (ae_of_all _ hbd) (integrable_const _) (ae_of_all _ fun y t _ => hF' y t)
    refine key.congr_fderiv ?_
    have hi : ∀ i, Integrable (fun y => (dLine ψ S T (N i) h (q y + M t₀) - a i t₀ * h (q y + M t₀)) • coordC i) ν :=
      fun i => ((hint _ (hdt h hh i) t₀).sub ((hint h hh t₀).const_mul _)).smul_const _
    show ∫ y, (∑ i, (dLine ψ S T (N i) h (q y + M t₀) - a i t₀ * h (q y + M t₀)) • coordC i) ∂ν = _
    rw [integral_finsetSum _ fun i _ => hi i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_const, integral_sub (hint _ (hdt h hh i) t₀) ((hint h hh t₀).const_mul _),
      integral_const_mul]
  have hn : ∀ n : ℕ, ∀ h, IsThetaFunO ψ S T h → ContDiff ℝ n (G h) := by
    intro n
    induction n with
    | zero =>
      intro h hh
      exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun t => (hder h hh t).continuousAt)
    | succ n ih =>
      intro h hh
      rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
      refine ⟨_, ?_, hder h hh⟩
      refine ContDiff.sum fun i _ => ?_
      exact ((ih _ (hdt h hh i)).sub ((contDiff_infty.1 (haC i) n).mul (ih h hh))).smul contDiff_const
  exact contDiff_infty.2 fun n => hn n g hg

end GlobalTheory.TowerSmooth

namespace GlobalTheory.TowerSmooth

open GlobalTheory.WeilVacMove

theorem res_smooth : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), (∀ (y y' : Mx D W.rank r) (x x' : WO V' W), symplOH V W (isoPart V W C y + midPart V V' W B x) (isoPart V W C y' + midPart V V' W B x') = symplOH V' W x x') → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ f, IsThetaFunO ψ V W f → ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WO V' W), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => res V V' W C B μ 𝓨 f (w + L t) := by
  intro D V V' W r C B hform ψ hψ μ 𝓨 hcov f hf k L hL hL0 w
  have : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓨) :=
    ⟨by rw [Measure.restrict_apply_univ, hcov.2.2]; exact ENNReal.one_lt_top⟩
  let mid : WO V' W →+ WO V W :=
    { toFun := midPart V V' W B
      map_zero' := by simp [midPart]
      map_add' := fun x y => by simp [midPart, Matrix.add_mul] }
  have hmid : Continuous mid := continuous_id.matrix_mul continuous_const
  have hmid0 : ∀ x : WO V' W, x.map (finPart D) = 0 → (mid x).map (finPart D) = 0 := by
    intro x hx
    simp only [mid, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    unfold midPart
    rw [Matrix.map_mul, hx, Matrix.zero_mul]
  have hiso0 : isoPart V W C 0 = 0 := by simp [isoPart]
  have hq : Continuous fun y : Mx D W.rank r => isoPart V W C y + midPart V V' W B w :=
    (continuous_id.matrix_mul continuous_const).add continuous_const
  have hb : ∀ i y, symplOH V W (isoPart V W C y + midPart V V' W B w) ((mid.comp L) (Pi.single i 1)) =
      symplOH V' W w (L (Pi.single i 1)) := by
    intro i y
    have := hform y 0 w (L (Pi.single i 1))
    rwa [hiso0, zero_add] at this
  have key := contDiff_integral hψ (μ.restrict 𝓨) hq (hmid.comp hL) (fun t => hmid0 _ (hL0 t)) _ hb f hf
  convert key using 1
  funext t
  show ∫ y in 𝓨, f (isoPart V W C y + midPart V V' W B (w + L t)) ∂μ = _
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  show f (isoPart V W C y + mid (w + L t)) = f (isoPart V W C y + midPart V V' W B w + mid (L t))
  rw [map_add, add_assoc]
  rfl

end GlobalTheory.TowerSmooth
