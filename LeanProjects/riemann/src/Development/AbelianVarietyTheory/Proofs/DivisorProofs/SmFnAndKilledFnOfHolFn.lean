import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict.HolTo

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

set_option backward.isDefEq.respectTransparency false in
theorem contDiff_exp_entry (X : Mt n) (a b : Fin n) :
    ContDiff ℝ ∞ fun t : ℝ => NormedSpace.exp (t • X) a b := by
  letI : NormedRing (Mt n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mt n) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Mt n) := FiniteDimensional.complete ℝ _
  let L : Mt n →ₗ[ℝ] ℂ := { toFun := fun M => M a b, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  rw [contDiff_iff_contDiffAt]
  intro t
  have hl : AnalyticAt ℝ (fun s : ℝ => s • X) t :=
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) X).analyticAt t
  have he : AnalyticAt ℝ (fun s : ℝ => NormedSpace.exp (s • X)) t :=
    AnalyticAt.comp (f := fun s : ℝ => s • X) (NormedSpace.exp_analytic (𝕂 := ℝ) _) hl
  exact (AnalyticAt.comp (f := fun s : ℝ => NormedSpace.exp (s • X))
    ((LinearMap.toContinuousLinearMap L).analyticAt _) he).contDiffAt

set_option backward.isDefEq.respectTransparency false in
theorem hasDerivAt_exp_entry (X : Mt n) (a b : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) a b) (X a b) 0 := by
  letI : NormedRing (Mt n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mt n) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Mt n) := FiniteDimensional.complete ℝ _
  let L : Mt n →ₗ[ℝ] ℂ := { toFun := fun M => M a b, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

private theorem isOpen_frDom' (H : Mt n) (q : ℕ) : IsOpen (frDom H q) := by
  have e : frDom H q = {x : Mt n | x.det ≠ 0} ∩ ⋂ i : Fin (n + 1), {x : Mt n |
      0 < ReciprocityTheory.ChartRestriction.G.FD.psgn q i * (ReciprocityTheory.ChartRestriction.G.FD.lminor (-(xᴴ * H * x)) i).re} := by
    ext x
    simp only [frDom, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [e]
  refine IsOpen.inter (isOpen_ne_fun continuous_id.matrix_det continuous_const)
    (isOpen_iInter_of_finite fun i => ?_)
  refine isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp ?_))
  exact ((((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id).neg).matrix_submatrix _ _).matrix_det

theorem isOpen_frDoms (Hm : ι → Mt n) (q : ι → ℕ) : IsOpen (frDoms Hm q) := by
  have e : frDoms Hm q = ⋂ τ, (fun x : ι → Fin n → Fin n → ℂ => (Matrix.of (x τ) : Mt n)) ⁻¹' frDom (Hm τ) (q τ) := by
    ext x
    simp only [frDoms, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  rw [e]
  exact isOpen_iInter_of_finite fun τ => (isOpen_frDom' (Hm τ) (q τ)).preimage (continuous_apply τ)

theorem det_diag_ne (q : ℕ) :
    (diagonal fun a : Fin n => -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ)).det ≠ 0 := by
  rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
  intro a _
  unfold ReciprocityTheory.ChartRestriction.G.FD.sgn
  split_ifs <;> norm_num

theorem dets_ne {H x : Mt n} {q : ℕ} (h : OrthFr H q x) : H.det ≠ 0 ∧ x.det ≠ 0 := by
  have h2 := congrArg Matrix.det h.2
  rw [Matrix.det_mul, Matrix.det_mul] at h2
  have h3 : (xᴴ).det * H.det * x.det ≠ 0 := h2 ▸ det_diag_ne q
  exact ⟨fun h0 => h3 (by rw [h0]; ring), fun h0 => h3 (by rw [h0]; ring)⟩

theorem herm_of_orth {H x : Mt n} {q : ℕ} (h : OrthFr H q x) : Hᴴ = H := by
  obtain ⟨_, hx⟩ := dets_ne h
  have hD : (diagonal fun a : Fin n => -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ))ᴴ =
      diagonal fun a : Fin n => -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ) := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    simp [Complex.conj_ofReal]
  have e : xᴴ * Hᴴ * x = xᴴ * H * x := by
    have h4 := congrArg Matrix.conjTranspose h.2
    rw [hD, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      ← h.2] at h4
    rw [← h4, Matrix.mul_assoc]
  have hu : IsUnit x := (Matrix.isUnit_iff_isUnit_det x).mpr (isUnit_iff_ne_zero.mpr hx)
  have hu' : IsUnit xᴴ := (Matrix.isUnit_iff_isUnit_det _).mpr
    (by rw [Matrix.det_conjTranspose]; exact isUnit_iff_ne_zero.mpr (star_ne_zero.mpr hx))
  exact hu'.mul_left_cancel (hu.mul_right_cancel e)

private theorem lminor_neg_diagonal_neg_sgn_eq_psgn (q : ℕ) (i : Fin (n + 1)) :
    ReciprocityTheory.ChartRestriction.G.FD.lminor (-(diagonal fun a : Fin n => -((ReciprocityTheory.ChartRestriction.G.FD.sgn q (a : ℕ) : ℝ) : ℂ))) i
      = ((ReciprocityTheory.ChartRestriction.G.FD.psgn q i : ℝ) : ℂ) := by
  unfold ReciprocityTheory.ChartRestriction.G.FD.lminor ReciprocityTheory.ChartRestriction.G.FD.psgn
  rw [← Matrix.diagonal_neg, neg_neg, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
  simp only [Function.comp_apply, Pi.neg_apply, neg_neg, Fin.coe_castLE]
  rw [Complex.ofReal_prod]
  exact Fin.prod_univ_eq_prod_range (fun a => ((ReciprocityTheory.ChartRestriction.G.FD.sgn q a : ℝ) : ℂ)) i

private theorem psgn_ne_zero (q i : ℕ) : ReciprocityTheory.ChartRestriction.G.FD.psgn q i ≠ 0 := by
  unfold ReciprocityTheory.ChartRestriction.G.FD.psgn
  rw [Finset.prod_ne_zero_iff]
  intro a _
  unfold ReciprocityTheory.ChartRestriction.G.FD.sgn
  split_ifs <;> norm_num

theorem mul_mem_frDom {H x u : Mt n} {q : ℕ} (h : OrthFr H q x) (hu : u ∈ Formalism.QuantumDeterminants.UH H) :
    u * x ∈ frDom H q := by
  obtain ⟨hH, hx⟩ := dets_ne h
  have hu' : uᴴ * H * u = H := hu
  have key : (u * x)ᴴ * H * (u * x) = xᴴ * H * x := by
    rw [Matrix.conjTranspose_mul]
    calc xᴴ * uᴴ * H * (u * x) = xᴴ * (uᴴ * H * u) * x := by simp only [Matrix.mul_assoc]
      _ = xᴴ * H * x := by rw [hu']
  have hdu : u.det ≠ 0 := by
    intro h0
    have h5 := congrArg Matrix.det hu'
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h5
    exact hH h5.symm
  refine ⟨by rw [Matrix.det_mul]; exact mul_ne_zero hdu hx, fun i => ?_⟩
  rw [key, h.2, lminor_neg_diagonal_neg_sgn_eq_psgn, Complex.ofReal_re]
  exact mul_self_pos.mpr (psgn_ne_zero q i)

theorem one_mem_UH (H : Mt n) : (1 : Mt n) ∈ Formalism.QuantumDeterminants.UH H := by
  show (1 : Mt n)ᴴ * H * 1 = H
  rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

private theorem exp_smul_mem_UH_of_mem_lieH (H X : Mt n) (hX : X ∈ lieH H) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH H := by
  letI : NormedRing (Mt n) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Mt n) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Mt n) := FiniteDimensional.complete ℝ _
  have hX' : Xᴴ * H + H * X = 0 := hX
  let F : ℝ → Mt n := fun s => NormedSpace.exp (s • Xᴴ) * H * NormedSpace.exp (s • X)
  have hd : ∀ s, HasDerivAt F 0 s := by
    intro s
    have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) Xᴴ s
    have h2 := hasDerivAt_exp_smul_const' (𝕂 := ℝ) X s
    have h3 := (h1.mul_const H).mul h2
    have h4 : NormedSpace.exp (s • Xᴴ) * Xᴴ * H * NormedSpace.exp (s • X) +
        NormedSpace.exp (s • Xᴴ) * H * (X * NormedSpace.exp (s • X)) = 0 := by
      have h5 : NormedSpace.exp (s • Xᴴ) * Xᴴ * H * NormedSpace.exp (s • X) +
          NormedSpace.exp (s • Xᴴ) * H * (X * NormedSpace.exp (s • X)) =
          NormedSpace.exp (s • Xᴴ) * (Xᴴ * H + H * X) * NormedSpace.exp (s • X) := by
        simp only [mul_add, add_mul, mul_assoc]
      rw [h5, hX', mul_zero, zero_mul]
    exact h3.congr_deriv h4
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  show (NormedSpace.exp (t • X))ᴴ * H * NormedSpace.exp (t • X) = H
  rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, star_trivial]
  have hF : F t = H := by
    rw [hc]
    simp only [F, zero_smul, NormedSpace.exp_zero, one_mul, mul_one]
  exact hF

theorem single_mem_UG (Hm : ι → Mt n) (τ : ι) {X : Mt n} (hX : X ∈ lieH (Hm τ)) (t : ℝ) :
    (Pi.mulSingle τ (NormedSpace.exp (t • X)) : ι → Mt n) ∈ UG Hm := by
  intro σ
  by_cases h : σ = τ
  · subst h
    rw [Pi.mulSingle_eq_same]
    exact exp_smul_mem_UH_of_mem_lieH _ _ hX t
  · rw [Pi.mulSingle_eq_of_ne h]
    exact one_mem_UH _

theorem mul_mem_UG {Hm : ι → Mt n} {u v : ι → Mt n} (hu : u ∈ UG Hm) (hv : v ∈ UG Hm) : u * v ∈ UG Hm := by
  intro τ
  have h1 : (u τ)ᴴ * Hm τ * u τ = Hm τ := hu τ
  have h2 : (v τ)ᴴ * Hm τ * v τ = Hm τ := hv τ
  show (u τ * v τ)ᴴ * Hm τ * (u τ * v τ) = Hm τ
  rw [Matrix.conjTranspose_mul]
  calc (v τ)ᴴ * (u τ)ᴴ * Hm τ * (u τ * v τ) = (v τ)ᴴ * ((u τ)ᴴ * Hm τ * u τ) * v τ := by
        simp only [Matrix.mul_assoc]
    _ = Hm τ := by rw [h1, h2]

theorem prod_mem_UG {Hm : ι → Mt n} (l : List (ι → Mt n)) (hl : ∀ v ∈ l, v ∈ UG Hm) : l.prod ∈ UG Hm := by
  induction l with
  | nil =>
    rw [List.prod_nil]
    intro σ
    exact one_mem_UH _
  | cons v l ih =>
    rw [List.prod_cons]
    exact mul_mem_UG (hl v (by simp)) (ih fun w hw => hl w (by simp [hw]))

def SmE {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (F : E → ι → Mt n) : Prop :=
  ∀ σ a b, ContDiff ℝ ∞ fun t => F t σ a b

theorem SmE.mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F G : E → ι → Mt n} (hF : SmE F) (hG : SmE G) :
    SmE fun t => F t * G t := by
  intro σ a b
  simp only [Pi.mul_apply, Matrix.mul_apply]
  exact ContDiff.sum fun c _ => (hF σ a c).mul (hG σ c b)

theorem smE_prod {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∀ (k : ℕ) (F : Fin k → E → ι → Mt n), (∀ i, SmE (F i)) → SmE fun t => (List.ofFn fun i => F i t).prod := by
  intro k
  induction k with
  | zero =>
    intro F _ σ a b
    simp only [List.ofFn_zero, List.prod_nil]
    exact contDiff_const
  | succ k ih =>
    intro F hF
    simp only [List.ofFn_succ, List.prod_cons]
    exact SmE.mul (hF 0) (ih _ fun i => hF i.succ)

theorem smooth_of_holFn {Hm : ι → Mt n} {q : ι → ℕ} {x₀ : ι → Mt n} {w : ι → Fin n → ℤ}
    (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) {f : (ι → Mt n) → ℂ} (hf : HolFn Hm q x₀ w f) : SmFn Hm f := by
  obtain ⟨P, ⟨hPd, _⟩, hfP⟩ := hf
  intro k τs Xs hXs u hu
  have hV : ∀ t : Fin k → ℝ, u * (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)).prod ∈ UG Hm := fun t =>
    mul_mem_UG hu (prod_mem_UG _ (List.forall_mem_ofFn_iff.mpr fun i => single_mem_UG Hm (τs i) (hXs i) (t i)))
  have h1 : SmE (fun t : Fin k → ℝ => (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)).prod) := by
    refine smE_prod k (fun i (t : Fin k → ℝ) => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)) ?_
    intro i σ a b
    by_cases hσ : σ = τs i
    · subst hσ
      simp only [Pi.mulSingle_eq_same]
      exact (contDiff_exp_entry (Xs i) a b).comp (contDiff_apply ℝ ℝ i)
    · simp only [Pi.mulSingle_eq_of_ne hσ]
      exact contDiff_const
  have h2 : SmE (fun t : Fin k → ℝ => u * (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)).prod) :=
    SmE.mul (F := fun _ => u) (fun _ _ _ => contDiff_const) h1
  have hsm : SmE (fun t : Fin k → ℝ => u * (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)).prod * x₀) :=
    SmE.mul (G := fun _ => x₀) h2 (fun _ _ _ => contDiff_const)
  have hc : ContDiff ℝ ∞ (fun t : Fin k → ℝ =>
      (fun σ a b => ((u * (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)).prod) σ * x₀ σ) a b)) := by
    rw [contDiff_pi]; intro σ; rw [contDiff_pi]; intro a; rw [contDiff_pi]; intro b
    exact hsm σ a b
  have hin : ∀ t : Fin k → ℝ, (fun σ a b => ((u * (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)).prod) σ * x₀ σ) a b) ∈ frDoms Hm q :=
    fun t σ => mul_mem_frDom (h σ) (hV t σ)
  have hP : ContDiffOn ℝ ∞ P (frDoms Hm q) :=
    (GlobalTheory.SCV.contDiffOn_of_differentiableOn (isOpen_frDoms Hm q) hPd _).restrict_scalars ℝ
  have e : (fun t : Fin k → ℝ => f (u * (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)).prod)) = P ∘ (fun t : Fin k → ℝ =>
      (fun σ a b => ((u * (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : ι → Mt n)).prod) σ * x₀ σ) a b)) := by
    funext t
    exact hfP _ (hV t)
  rw [e]
  exact hP.comp_contDiff hc hin

def tang (τ : ι) (u x : ι → Mt n) : Mt n →ₗ[ℂ] (ι → Fin n → Fin n → ℂ) where
  toFun X := fun σ => (u σ * (Pi.single τ X : ι → Mt n) σ * x σ : Mt n)
  map_add' X Y := by
    funext σ
    change (_ : Mt n) = (_ : Mt n) + (_ : Mt n)
    rw [Pi.single_add, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    funext σ
    change (_ : Mt n) = c • (_ : Mt n)
    rw [Pi.single_smul', Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]

theorem hasDerivAt_curve {P : (ι → Fin n → Fin n → ℂ) → ℂ} (τ : ι) (u x : ι → Mt n) (g : ℝ → Mt n) (X : Mt n)
    (g0 : g 0 = 1) (hg : ∀ a b, HasDerivAt (fun t => g t a b) (X a b) 0)
    (hP : DifferentiableAt ℂ P fun σ a b => (u σ * x σ : Mt n) a b) :
    HasDerivAt (fun t : ℝ => P fun σ => (u σ * (Pi.mulSingle τ (g t) : ι → Mt n) σ * x σ : Mt n))
      (fderiv ℂ P (fun σ => (u σ * x σ : Mt n)) (tang τ u x X)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => (fun σ a b => (u σ * (Pi.mulSingle τ (g t) : ι → Mt n) σ * x σ) a b)) (tang τ u x X) 0 := by
    rw [hasDerivAt_pi]; intro σ
    rw [hasDerivAt_pi]; intro a
    rw [hasDerivAt_pi]; intro b
    show HasDerivAt (fun t : ℝ => (u σ * (Pi.mulSingle τ (g t) : ι → Mt n) σ * x σ : Mt n) a b)
      ((u σ * (Pi.single τ X : ι → Mt n) σ * x σ : Mt n) a b) 0
    by_cases hσ : σ = τ
    · subst hσ
      simp only [Pi.mulSingle_eq_same, Pi.single_eq_same, Matrix.mul_apply]
      exact HasDerivAt.fun_sum fun d _ => (HasDerivAt.fun_sum fun c _ => (hg c d).const_mul _).mul_const _
    · simp only [Pi.mulSingle_eq_of_ne hσ, Pi.single_eq_of_ne hσ, Matrix.mul_one, Matrix.mul_zero,
        Matrix.zero_mul, Matrix.zero_apply]
      exact hasDerivAt_const _ _
  have h0 : (fun σ a b => (u σ * x σ : Mt n) a b) = (fun t : ℝ => (fun σ a b => (u σ * (Pi.mulSingle τ (g t) : ι → Mt n) σ * x σ) a b)) 0 := by
    funext σ a b
    simp [g0]
  exact (hP.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq 0 hc h0

theorem der_eq {Hm : ι → Mt n} {q : ι → ℕ} {x₀ : ι → Mt n}
    (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) {f : (ι → Mt n) → ℂ} {P : (ι → Fin n → Fin n → ℂ) → ℂ}
    (hP : DifferentiableOn ℂ P (frDoms Hm q)) (hfP : ∀ u ∈ UG Hm, f u = P fun τ => (u τ * x₀ τ : Mt n))
    (τ : ι) {X : Mt n} (hX : X ∈ lieH (Hm τ)) {u : ι → Mt n} (hu : u ∈ UG Hm) :
    der τ X f u = fderiv ℂ P (fun σ => (u σ * x₀ σ : Mt n)) (tang τ u x₀ X) := by
  have hfun : (fun t : ℝ => f (u * (Pi.mulSingle τ (NormedSpace.exp (t • X)) : ι → Mt n))) =
      fun t : ℝ => P fun σ => (u σ * (Pi.mulSingle τ (NormedSpace.exp (t • X)) : ι → Mt n) σ * x₀ σ : Mt n) := by
    funext t
    exact hfP _ (mul_mem_UG hu (single_mem_UG Hm τ hX t))
  have hmem : (fun σ a b => (u σ * x₀ σ : Mt n) a b) ∈ frDoms Hm q := fun σ => mul_mem_frDom (h σ) (hu σ)
  have hPd : DifferentiableAt ℂ P (fun σ a b => (u σ * x₀ σ : Mt n) a b) :=
    hP.differentiableAt ((isOpen_frDoms Hm q).mem_nhds hmem)
  have hd := hasDerivAt_curve (P := P) τ u x₀ (fun t : ℝ => NormedSpace.exp (t • X)) X
    (by simp only [zero_smul, NormedSpace.exp_zero]) (fun a b => hasDerivAt_exp_entry X a b) hPd
  unfold der
  rw [hfun]
  exact hd.deriv

theorem conj_facts {H : Mt n} (hH : Hᴴ = H) (hd : H.det ≠ 0) (Z : Mt n) :
    (conjH H Z)ᴴ * H = -(H * Z) ∧ H * conjH H Z = -(Zᴴ * H) := by
  have hu : IsUnit H.det := isUnit_iff_ne_zero.mpr hd
  have hi : (H⁻¹)ᴴ = H⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hH]
  unfold conjH
  constructor
  · rw [Matrix.conjTranspose_neg, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hi, hH,
      Matrix.conjTranspose_conjTranspose, Matrix.neg_mul]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
  · rw [Matrix.mul_neg]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

theorem derC_eq {Hm : ι → Mt n} {q : ι → ℕ} {x₀ : ι → Mt n}
    (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) {f : (ι → Mt n) → ℂ} {P : (ι → Fin n → Fin n → ℂ) → ℂ}
    (hP : DifferentiableOn ℂ P (frDoms Hm q)) (hfP : ∀ u ∈ UG Hm, f u = P fun τ => (u τ * x₀ τ : Mt n))
    (τ : ι) (Z : Mt n) {u : ι → Mt n} (hu : u ∈ UG Hm) :
    derC Hm τ Z f u = fderiv ℂ P (fun σ => (u σ * x₀ σ : Mt n)) (tang τ u x₀ Z) := by
  obtain ⟨hH, _⟩ := dets_ne (h τ)
  obtain ⟨c1, c2⟩ := conj_facts (herm_of_orth (h τ)) hH Z
  have s1 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  have s2 : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    simp [Complex.star_def, Complex.conj_I, div_neg]
  have l1 : (1 / 2 : ℂ) • (Z + conjH (Hm τ) Z) ∈ lieH (Hm τ) := by
    show ((1 / 2 : ℂ) • (Z + conjH (Hm τ) Z))ᴴ * Hm τ + Hm τ * ((1 / 2 : ℂ) • (Z + conjH (Hm τ) Z)) = 0
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.add_mul, Matrix.mul_add, c1, c2, s1, ← smul_add]
    rw [show Zᴴ * Hm τ + -(Hm τ * Z) + (Hm τ * Z + -(Zᴴ * Hm τ)) = 0 by abel, smul_zero]
  have l2 : (1 / (2 * Complex.I)) • (Z - conjH (Hm τ) Z) ∈ lieH (Hm τ) := by
    show ((1 / (2 * Complex.I)) • (Z - conjH (Hm τ) Z))ᴴ * Hm τ +
      Hm τ * ((1 / (2 * Complex.I)) • (Z - conjH (Hm τ) Z)) = 0
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.sub_mul, Matrix.mul_sub, c1, c2, s2, neg_smul, neg_add_eq_sub, ← smul_sub]
    rw [show Hm τ * Z - -(Zᴴ * Hm τ) - (Zᴴ * Hm τ - -(Hm τ * Z)) = 0 by abel, smul_zero]
  have e1 := der_eq h hP hfP τ l1 hu
  have e2 := der_eq h hP hfP τ l2 hu
  unfold derC
  rw [e1, e2, ← smul_eq_mul, ← map_smul, ← map_add, ← map_smul, ← map_add]
  congr 2
  rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp, ← smul_add,
    show Z + conjH (Hm τ) Z + (Z - conjH (Hm τ) Z) = (2 : ℂ) • Z by rw [two_smul]; abel, smul_smul]
  norm_num

private theorem hasDerivAt_mul_mulSingle_curve_eq_fderiv {P : (ι → Fin n → Fin n → ℂ) → ℂ} (τ : ι) (y : ι → Mt n) (g : ℝ → Mt n)
    (X : Mt n) (g0 : g 0 = 1) (hg : ∀ a b, HasDerivAt (fun t => g t a b) (X a b) 0)
    (hP : DifferentiableAt ℂ P fun σ a b => y σ a b) :
    HasDerivAt (fun t : ℝ => P fun σ a b => (y σ * (Pi.mulSingle τ (g t) : ι → Mt n) σ) a b)
      (fderiv ℂ P (fun σ a b => y σ a b) (fun σ a b => (y σ * (Pi.single τ X : ι → Mt n) σ) a b)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => fun σ a b => (y σ * (Pi.mulSingle τ (g t) : ι → Mt n) σ) a b)
      (fun σ a b => (y σ * (Pi.single τ X : ι → Mt n) σ) a b) 0 := by
    rw [hasDerivAt_pi]; intro σ
    rw [hasDerivAt_pi]; intro a
    rw [hasDerivAt_pi]; intro b
    by_cases hσ : σ = τ
    · subst hσ
      simp only [Pi.mulSingle_eq_same, Pi.single_eq_same, Matrix.mul_apply]
      exact HasDerivAt.fun_sum fun c _ => (hg c b).const_mul _
    · simp only [Pi.mulSingle_eq_of_ne hσ, Pi.single_eq_of_ne hσ, Matrix.mul_one, Matrix.mul_zero,
        Matrix.zero_apply]
      exact hasDerivAt_const _ _
  have h0 : (fun σ a b => y σ a b) = (fun t : ℝ => fun σ a b => (y σ * (Pi.mulSingle τ (g t) : ι → Mt n) σ) a b) 0 := by
    funext σ a b
    simp [g0]
  exact (hP.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq 0 hc h0

theorem killed_of_holFn {Hm : ι → Mt n} {q : ι → ℕ} {x₀ : ι → Mt n} {w : ι → Fin n → ℤ}
    (h : ∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) {f : (ι → Mt n) → ℂ} (hf : HolFn Hm q x₀ w f) : KilledFn Hm x₀ w f := by
  obtain ⟨P, ⟨hPd, hPw⟩, hfP⟩ := hf
  intro τ a c hac u hu
  obtain ⟨_, hx⟩ := dets_ne (h τ)
  have hxu : IsUnit (x₀ τ).det := isUnit_iff_ne_zero.mpr hx
  rw [derC_eq h hPd hfP τ _ hu, hfP u hu]
  set E : Mt n := Matrix.single a c 1 with hE
  have hy : (fun σ a b => (u σ * x₀ σ : Mt n) a b) ∈ frDoms Hm q := fun σ => mul_mem_frDom (h σ) (hu σ)
  have hPd' : DifferentiableAt ℂ P (fun σ a b => (u σ * x₀ σ : Mt n) a b) :=
    hPd.differentiableAt ((isOpen_frDoms Hm q).mem_nhds hy)
  have hg : ∀ a' b', HasDerivAt (fun t : ℝ => ((1 : Mt n) + (t : ℂ) • E) a' b') (E a' b') 0 := by
    intro a' b'
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact (((hasDerivAt_id' (0 : ℝ)).ofReal_comp.mul_const (E a' b')).const_add _).congr_deriv (by simp)
  have hd := hasDerivAt_mul_mulSingle_curve_eq_fderiv (P := P) τ (fun σ => u σ * x₀ σ) (fun t : ℝ => (1 : Mt n) + (t : ℂ) • E) E
    (by simp) hg hPd'
  have htang : tang τ u x₀ (x₀ τ * E * (x₀ τ)⁻¹) =
      fun σ a b => ((u σ * x₀ σ) * (Pi.single τ E : ι → Mt n) σ) a b := by
    funext σ
    show (u σ * (Pi.single τ (x₀ τ * E * (x₀ τ)⁻¹) : ι → Mt n) σ * x₀ σ : Mt n) =
      (u σ * x₀ σ) * (Pi.single τ E : ι → Mt n) σ
    by_cases hσ : σ = τ
    · subst hσ
      rw [Pi.single_eq_same, Pi.single_eq_same]
      simp only [Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul _ hxu, Matrix.mul_one]
    · rw [Pi.single_eq_of_ne hσ, Pi.single_eq_of_ne hσ, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_zero]
  have upT : ∀ t : ℝ, ((1 : Mt n) + (t : ℂ) • E).det ≠ 0 →
      ∀ σ, UpT ((Pi.mulSingle τ ((1 : Mt n) + (t : ℂ) • E) : ι → Mt n) σ) := by
    intro t ht σ
    by_cases hσ : σ = τ
    · subst hσ
      rw [Pi.mulSingle_eq_same]
      refine ⟨ht, fun a' c' hca => ?_⟩
      have hne : a' ≠ c' := ne_of_gt hca
      simp only [Matrix.add_apply, Matrix.one_apply_ne hne, Matrix.smul_apply, hE, Matrix.single_apply,
        zero_add, smul_eq_mul]
      split_ifs with hh
      · obtain ⟨rfl, rfl⟩ := hh
        exact absurd hac (not_le.mpr hca)
      · simp
    · rw [Pi.mulSingle_eq_of_ne hσ]
      exact ⟨by simp, fun a' c' hca => Matrix.one_apply_ne (ne_of_gt hca)⟩
  have hw : ∀ t : ℝ, ((1 : Mt n) + (t : ℂ) • E).det ≠ 0 →
      P (fun σ a b => ((u σ * x₀ σ) * (Pi.mulSingle τ ((1 : Mt n) + (t : ℂ) • E) : ι → Mt n) σ) a b) =
      (∏ σ, ∏ a', ((Pi.mulSingle τ ((1 : Mt n) + (t : ℂ) • E) : ι → Mt n) σ a' a') ^ w σ a') *
        P (fun σ a b => (u σ * x₀ σ : Mt n) a b) :=
    fun t ht => hPw _ hy _ (upT t ht)
  have hprod : ∀ t : ℝ,
      (∏ σ, ∏ a', ((Pi.mulSingle τ ((1 : Mt n) + (t : ℂ) • E) : ι → Mt n) σ a' a') ^ w σ a') =
      if a = c then (1 + (t : ℂ)) ^ w τ a else 1 := by
    intro t
    rw [Finset.prod_eq_single τ (fun σ _ hσ => by simp [Pi.mulSingle_eq_of_ne hσ]) (by simp),
      Pi.mulSingle_eq_same]
    split_ifs with hh
    · subst hh
      rw [Finset.prod_eq_single a (fun a' _ ha' => by
        simp [hE, Matrix.single_apply, Ne.symm ha']) (by simp)]
      simp [hE, Matrix.single_apply]
    · refine Finset.prod_eq_one fun a' _ => ?_
      have hn : ¬ (a = a' ∧ c = a') := fun hh2 => hh (hh2.1.trans hh2.2.symm)
      simp [hE, Matrix.single_apply, hn]
  have hcont : Continuous fun t : ℝ => ((1 : Mt n) + (t : ℂ) • E).det :=
    (continuous_const.add (Complex.continuous_ofReal.smul continuous_const)).matrix_det
  have hev : ∀ᶠ t : ℝ in nhds (0 : ℝ), ((1 : Mt n) + (t : ℂ) • E).det ≠ 0 :=
    hcont.continuousAt.eventually_ne (by simp)
  have hR : HasDerivAt (fun t : ℝ => (if a = c then (1 + (t : ℂ)) ^ w τ a else 1) *
      P (fun σ a b => (u σ * x₀ σ : Mt n) a b))
      ((if a = c then (w τ a : ℂ) else 0) * P (fun σ a b => (u σ * x₀ σ : Mt n) a b)) 0 := by
    apply HasDerivAt.mul_const
    split_ifs with hh
    · have h0 := (hasDerivAt_zpow (w τ a) (1 + 0 : ℂ) (Or.inl (by norm_num))).comp (0 : ℂ)
        ((hasDerivAt_id' (0 : ℂ)).const_add 1)
      have h1 : HasDerivAt (fun s : ℂ => (1 + s) ^ w τ a) (w τ a : ℂ) ((0 : ℝ) : ℂ) := by
        rw [Complex.ofReal_zero]
        convert h0 using 1
        all_goals first | rfl | simp [Function.comp_def]
      exact h1.comp_ofReal
    · exact hasDerivAt_const _ _
  have hL : HasDerivAt (fun t : ℝ => P (fun σ a b => ((u σ * x₀ σ) *
      (Pi.mulSingle τ ((1 : Mt n) + (t : ℂ) • E) : ι → Mt n) σ) a b))
      ((if a = c then (w τ a : ℂ) else 0) * P (fun σ a b => (u σ * x₀ σ : Mt n) a b)) 0 :=
    hR.congr_of_eventuallyEq (hev.mono fun t ht => by beta_reduce; rw [hw t ht, hprod t])
  rw [htang]
  have hU := hd.unique hL
  rw [hU]
  split_ifs <;> simp

end GlobalTheory.HolDict.HolTo

theorem GlobalTheory.HolDict.smFn_and_killedFn_of_holFn : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ), (∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) → ∀ f, HolFn Hm q x₀ w f → SmFn Hm f ∧ KilledFn Hm x₀ w f :=
  fun _ _ _ _ _ _ _ _ h _ hf => ⟨HolTo.smooth_of_holFn h hf, HolTo.killed_of_holFn h hf⟩
