import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSliceCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FsvMulFsvNeg

open MeasureTheory Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE.JSW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P5

theorem fderiv_apply_sm {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) (v : ℂ) :
    ContDiffOn ℝ ∞ (fun ζ => fderiv ℝ g ζ v) U :=
  (hg.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

theorem dZ_sm {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (NF.dZ g) U := by
  unfold NF.dZ
  exact contDiffOn_const.mul ((fderiv_apply_sm hU hg 1).sub
    (contDiffOn_const.mul (fderiv_apply_sm hU hg Complex.I)))

theorem dZb_sm {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U) :
    ContDiffOn ℝ ∞ (NF.dZb g) U := by
  unfold NF.dZb
  exact contDiffOn_const.mul ((fderiv_apply_sm hU hg 1).add
    (contDiffOn_const.mul (fderiv_apply_sm hU hg Complex.I)))

theorem hasFDerivAt_exponential_character (s t : ℂ) :
    ∃ D : ℂ →L[ℝ] ℂ, HasFDerivAt (fsv s) D t ∧ D 1 = (s - conj s) * fsv s t ∧
      D Complex.I = Complex.I * (s + conj s) * fsv s t := by
  have h1 : HasFDerivAt (fun t' : ℂ => t') (ContinuousLinearMap.id ℝ ℂ) t := hasFDerivAt_id t
  have h2 : HasFDerivAt (fun t' : ℂ => conj t') Complex.conjCLE.toContinuousLinearMap t :=
    Complex.conjCLE.hasFDerivAt
  have h3 := ((h1.const_mul s).sub (h2.const_mul (conj s))).cexp
  refine ⟨_, h3, ?_, ?_⟩
  · simp [fsv]; ring
  · simp [fsv]; ring

theorem dZ_exponential_character (s t : ℂ) : NF.dZ (fsv s) t = s * fsv s t := by
  obtain ⟨D, hD, h1, hI⟩ := hasFDerivAt_exponential_character s t
  simp only [NF.dZ, hD.fderiv, h1, hI]
  linear_combination (-(1 / 2) * (s + conj s) * fsv s t) * Complex.I_sq

theorem dZbar_exponential_character (s t : ℂ) : NF.dZb (fsv s) t = -conj s * fsv s t := by
  obtain ⟨D, hD, h1, hI⟩ := hasFDerivAt_exponential_character s t
  simp only [NF.dZb, hD.fderiv, h1, hI]
  linear_combination ((1 / 2) * (s + conj s) * fsv s t) * Complex.I_sq

theorem fsv_diff (s t : ℂ) : DifferentiableAt ℝ (fsv s) t :=
  (hasFDerivAt_exponential_character s t).choose_spec.1.differentiableAt

theorem dZ_mul_leibniz {φ f : ℂ → ℂ} {c : ℂ} (hφ : DifferentiableAt ℝ φ c) (hf : DifferentiableAt ℝ f c) :
    NF.dZ (fun w => φ w * f w) c = NF.dZ φ c * f c + φ c * NF.dZ f c := by
  have h : HasFDerivAt (fun w => φ w * f w) _ c := hφ.hasFDerivAt.mul hf.hasFDerivAt
  unfold NF.dZ
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem dZbar_mul_leibniz {φ f : ℂ → ℂ} {c : ℂ} (hφ : DifferentiableAt ℝ φ c) (hf : DifferentiableAt ℝ f c) :
    NF.dZb (fun w => φ w * f w) c = NF.dZb φ c * f c + φ c * NF.dZb f c := by
  have h : HasFDerivAt (fun w => φ w * f w) _ c := hφ.hasFDerivAt.mul hf.hasFDerivAt
  unfold NF.dZb
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem mfs_dZ {m : ℂ → ℂ} {t : ℂ} (s : ℂ) (hm : DifferentiableAt ℝ m t) :
    NF.dZ (fun w => m w * fsv s w) t = (NF.dZ m t + s * m t) * fsv s t := by
  rw [dZ_mul_leibniz hm (fsv_diff s t), dZ_exponential_character]; ring

theorem mfs_dZb {m : ℂ → ℂ} {t : ℂ} (s : ℂ) (hm : DifferentiableAt ℝ m t) :
    NF.dZb (fun w => m w * fsv s w) t = (NF.dZb m t + -conj s * m t) * fsv s t := by
  rw [dZbar_mul_leibniz hm (fsv_diff s t), dZbar_exponential_character]; ring

theorem sm_diff {m : ℂ → ℂ} (hm : ContDiffOn ℝ ∞ m {0}ᶜ) {t : ℂ} (ht : t ≠ 0) : DifferentiableAt ℝ m t :=
  (hm.contDiffAt (isOpen_compl_singleton.mem_nhds ht)).differentiableAt (by simp)

section Wirt

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem wirt_comp_smul (l : Fin m) (φ : ℂ → ℂ) (v : (Fin m → ℂ) → E) (c : Fin m → ℂ)
    (hφ : DifferentiableAt ℝ φ (c l)) (hv : DifferentiableAt ℝ v c) :
    Formalism.QuantumDeterminants.wirt l (fun c' => φ (c' l) • v c') c = φ (c l) • Formalism.QuantumDeterminants.wirt l v c + NF.dZ φ (c l) • v c ∧
      Formalism.QuantumDeterminants.wirtBar l (fun c' => φ (c' l) • v c') c = φ (c l) • Formalism.QuantumDeterminants.wirtBar l v c + NF.dZb φ (c l) • v c := by
  have h1 : HasFDerivAt (fun c' : Fin m → ℂ => c' l)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℂ) l) c := hasFDerivAt_apply l c
  have h2 : HasFDerivAt (fun c' : Fin m → ℂ => φ (c' l))
      ((fderiv ℝ φ (c l)).comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℂ) l)) c :=
    hφ.hasFDerivAt.comp c h1
  have hp := h2.fun_smul hv.hasFDerivAt
  unfold Formalism.QuantumDeterminants.wirt Formalism.QuantumDeterminants.wirtBar NF.dZ NF.dZb
  rw [hp.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    Pi.single_eq_same]
  constructor
  · match_scalars <;> ring
  · match_scalars <;> ring

theorem wirt_fsum {ι : Type*} (u : Finset ι) (l : Fin m) (F : ι → (Fin m → ℂ) → E) (c : Fin m → ℂ)
    (hF : ∀ i ∈ u, DifferentiableAt ℝ (F i) c) :
    Formalism.QuantumDeterminants.wirt l (fun c' => ∑ i ∈ u, F i c') c = ∑ i ∈ u, Formalism.QuantumDeterminants.wirt l (F i) c ∧
      Formalism.QuantumDeterminants.wirtBar l (fun c' => ∑ i ∈ u, F i c') c = ∑ i ∈ u, Formalism.QuantumDeterminants.wirtBar l (F i) c := by
  have h : HasFDerivAt (fun c' => ∑ i ∈ u, F i c') (∑ i ∈ u, fderiv ℝ (F i) c) c :=
    HasFDerivAt.fun_sum fun i hi => (hF i hi).hasFDerivAt
  unfold Formalism.QuantumDeterminants.wirt Formalism.QuantumDeterminants.wirtBar
  rw [h.fderiv]
  refine ⟨?_, ?_⟩
  · simp [Finset.smul_sum]
    rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  · simp [Finset.smul_sum, Finset.sum_add_distrib]

end Wirt

section Word

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem op_pt (X : ActualOps k r z z' π π') (l : Fin r) (i : Fin 6) (Ψ : RadSp k r z z' π π') (p : Fin r → ℂ)
    (g : Mx k r) : (X.op l i Ψ : Fn k r (Wq →L[ℂ] Wp)) p g =
      opL l i (fun c' => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c' g) p := by
  rw [X.op_apply]; rfl

theorem wOp_cons (X : ActualOps k r z z' π π') (l : Fin r) (j : Fin 6) (js : List (Fin 6))
    (Ψ : RadSp k r z z' π π') : wOp X l (j :: js) Ψ = X.op l j (wOp X l js Ψ) := by
  simp [wOp, List.map_cons, List.prod_cons, Module.End.mul_apply]

theorem wOp_nil (X : ActualOps k r z z' π π') (l : Fin r) (Ψ : RadSp k r z z' π π') : wOp X l [] Ψ = Ψ := by
  simp [wOp]

theorem slice_diffAt (Ψ : RadSp k r z z' π π') (g : Mx k r) {p : Fin r → ℂ} (hp : p ∈ OmX r) :
    DifferentiableAt ℝ (fun c' => (Ψ : Fn k r (Wq →L[ℂ] Wp)) c' g) p :=
  (radSp_regular Ψ g p).1 hp

theorem isOpen_OmX' (m : ℕ) : IsOpen (OmX m) := by
  have : OmX m = ⋂ l : Fin m, (fun x : Fin m → ℂ => x l) ⁻¹' {0}ᶜ := by
    ext x; simp [OmX]
  rw [this]
  exact isOpen_iInter_of_finite fun l => isOpen_compl_singleton.preimage (continuous_apply l)

def NFP (X : ActualOps k r z z' π π') (l : Fin r) (s : ℂ) (Wv : Module.End ℂ (RadSp k r z z' π π'))
    (js : List (Fin 6)) : Prop :=
  ∃ (K : ℕ) (m : Fin K → ℂ → ℂ) (ab : Fin K → List (Fin 6)),
    (∀ i, ContDiffOn ℝ ∞ (m i) {0}ᶜ) ∧ (∀ i, ∀ j ∈ ab i, j = 0 ∨ j = 3) ∧
    ∀ (Φ : RadSp k r z z' π π') (p : Fin r → ℂ), p ∈ OmX r → ∀ g : Mx k r,
      (wOp X l js (Wv Φ) : Fn k r (Wq →L[ℂ] Wp)) p g =
        ∑ i, (m i (p l) * fsv s (p l)) • (wOp X l (ab i) Φ : Fn k r (Wq →L[ℂ] Wp)) p g

variable (X : ActualOps k r z z' π π') (l : Fin r) (s : ℂ) (Wv : Module.End ℂ (RadSp k r z z' π π'))

theorem nfp_nil (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) : NFP X l s Wv [] := by
  refine ⟨1, fun _ _ => 1, fun _ => [], fun _ => contDiffOn_const, fun _ j hj => by simp at hj, ?_⟩
  intro Φ p _ g
  simp only [wOp_nil, Fin.sum_univ_one, one_mul]
  exact hW Φ p g

theorem nfp_mul (j : Fin 6) (a : ℂ → ℂ) (ha : ContDiffOn ℝ ∞ a {0}ᶜ)
    (hop : ∀ (Ψ : RadSp k r z z' π π') (p : Fin r → ℂ) (g : Mx k r),
      (X.op l j Ψ : Fn k r (Wq →L[ℂ] Wp)) p g = a (p l) • (Ψ : Fn k r (Wq →L[ℂ] Wp)) p g)
    (js : List (Fin 6)) (h : NFP X l s Wv js) : NFP X l s Wv (j :: js) := by
  obtain ⟨K, m, ab, hm, hab, hE⟩ := h
  refine ⟨K, fun i t => a t * m i t, ab, fun i => ha.mul (hm i), hab, ?_⟩
  intro Φ p hp g
  rw [wOp_cons, hop, hE Φ p hp g, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]; ring_nf

theorem nfp_der (b : Bool) (js : List (Fin 6)) (h : NFP X l s Wv js) :
    NFP X l s Wv ((if b then (0 : Fin 6) else 3) :: js) := by
  obtain ⟨K, m, ab, hm, hab, hE⟩ := h
  let mL : Fin K → ℂ → ℂ := fun i t =>
    if b then t * (NF.dZ (m i) t + s * m i t) else star t * (NF.dZb (m i) t + -conj s * m i t)
  have hmL : ∀ i, ContDiffOn ℝ ∞ (mL i) {0}ᶜ := by
    intro i
    cases b
    · exact (Complex.conjCLE.contDiff.contDiffOn).mul
        ((dZb_sm isOpen_compl_singleton (hm i)).add (contDiffOn_const.mul (hm i)))
    · exact contDiffOn_id.mul ((dZ_sm isOpen_compl_singleton (hm i)).add (contDiffOn_const.mul (hm i)))
  refine ⟨K + K, Fin.append mL m, Fin.append ab (fun i => (if b then (0 : Fin 6) else 3) :: ab i),
    ?_, ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_)
    · rw [Fin.append_left]; exact hmL i
    · rw [Fin.append_right]; exact hm i
  · refine Fin.addCases (fun i => ?_) (fun i => ?_)
    · rw [Fin.append_left]; exact hab i
    · rw [Fin.append_right]
      intro j hj
      rcases List.mem_cons.1 hj with hj | hj
      · subst hj; cases b <;> simp
      · exact hab i j hj
  intro Φ p hp g

  set v : Fin K → (Fin r → ℂ) → (Wq →L[ℂ] Wp) := fun i c' => (wOp X l (ab i) Φ : Fn k r (Wq →L[ℂ] Wp)) c' g
    with hv
  have hvd : ∀ i, DifferentiableAt ℝ (v i) p := fun i => slice_diffAt _ g hp
  have hmd : ∀ i, DifferentiableAt ℝ (m i) (p l) := fun i => sm_diff (hm i) (hp l)
  have hqd : ∀ i, DifferentiableAt ℝ (fun t => m i t * fsv s t) (p l) := fun i => (hmd i).mul (fsv_diff s (p l))

  have hev : (fun c' => (wOp X l js (Wv Φ) : Fn k r (Wq →L[ℂ] Wp)) c' g) =ᶠ[𝓝 p]
      fun c' => ∑ i, (fun t => m i t * fsv s t) (c' l) • v i c' := by
    filter_upwards [(isOpen_OmX' r).mem_nhds hp] with c' hc'
    exact hE Φ c' hc' g
  have hsd : ∀ i ∈ (Finset.univ : Finset (Fin K)),
      DifferentiableAt ℝ (fun c' => (fun t => m i t * fsv s t) (c' l) • v i c') p := by
    intro i _
    have h1 : DifferentiableAt ℝ (fun c' : Fin r → ℂ => (fun t => m i t * fsv s t) (c' l)) p :=
      DifferentiableAt.comp (g := fun t => m i t * fsv s t) (f := fun c' : Fin r → ℂ => c' l) p (hqd i)
        (differentiableAt_apply l p)
    exact h1.smul (hvd i)
  have hW1 : Formalism.QuantumDeterminants.wirt l (fun c' => (wOp X l js (Wv Φ) : Fn k r (Wq →L[ℂ] Wp)) c' g) p =
      ∑ i, ((m i (p l) * fsv s (p l)) • Formalism.QuantumDeterminants.wirt l (v i) p + ((NF.dZ (m i) (p l) + s * m i (p l)) * fsv s (p l)) • v i p) := by
    have e1 : Formalism.QuantumDeterminants.wirt l (fun c' => (wOp X l js (Wv Φ) : Fn k r (Wq →L[ℂ] Wp)) c' g) p =
        Formalism.QuantumDeterminants.wirt l (fun c' => ∑ i, (fun t => m i t * fsv s t) (c' l) • v i c') p := by
      unfold Formalism.QuantumDeterminants.wirt; rw [hev.fderiv_eq]
    rw [e1, (wirt_fsum Finset.univ l _ p hsd).1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(wirt_comp_smul l _ (v i) p (hqd i) (hvd i)).1, mfs_dZ s (hmd i)]
  have hW2 : Formalism.QuantumDeterminants.wirtBar l (fun c' => (wOp X l js (Wv Φ) : Fn k r (Wq →L[ℂ] Wp)) c' g) p =
      ∑ i, ((m i (p l) * fsv s (p l)) • Formalism.QuantumDeterminants.wirtBar l (v i) p + ((NF.dZb (m i) (p l) + -conj s * m i (p l)) * fsv s (p l)) • v i p) := by
    have e1 : Formalism.QuantumDeterminants.wirtBar l (fun c' => (wOp X l js (Wv Φ) : Fn k r (Wq →L[ℂ] Wp)) c' g) p =
        Formalism.QuantumDeterminants.wirtBar l (fun c' => ∑ i, (fun t => m i t * fsv s t) (c' l) • v i c') p := by
      unfold Formalism.QuantumDeterminants.wirtBar; rw [hev.fderiv_eq]
    rw [e1, (wirt_fsum Finset.univ l _ p hsd).2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(wirt_comp_smul l _ (v i) p (hqd i) (hvd i)).2, mfs_dZb s (hmd i)]
  rw [wOp_cons, op_pt, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  have hR : ∀ i, (wOp X l ((if b then (0 : Fin 6) else 3) :: ab i) Φ : Fn k r (Wq →L[ℂ] Wp)) p g =
      if b then p l • Formalism.QuantumDeterminants.wirt l (v i) p else star (p l) • Formalism.QuantumDeterminants.wirtBar l (v i) p := by
    intro i
    rw [wOp_cons, op_pt]
    cases b
    · simp only [Bool.false_eq_true, if_false]
      show Formalism.QuantumDeterminants.pbOp l _ p = _
      unfold Formalism.QuantumDeterminants.pbOp; rw [if_pos hp]
    · simp only [if_true]
      show Formalism.QuantumDeterminants.pOp l _ p = _
      unfold Formalism.QuantumDeterminants.pOp; rw [if_pos hp]
  simp only [hR]
  cases b
  · simp only [Bool.false_eq_true, if_false, mL]
    show Formalism.QuantumDeterminants.pbOp l _ p = _
    unfold Formalism.QuantumDeterminants.pbOp
    rw [if_pos hp, hW2, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [v]
    module
  · simp only [if_true, mL]
    show Formalism.QuantumDeterminants.pOp l _ p = _
    unfold Formalism.QuantumDeterminants.pOp
    rw [if_pos hp, hW1, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [v]
    module

theorem nfp_all (hW : multiplicationOperator Wv (fun c _ => fsv s (c l))) : ∀ js, NFP X l s Wv js := by
  intro js
  induction js with
  | nil => exact nfp_nil X l s Wv hW
  | cons j js ih =>
    fin_cases j
    · exact nfp_der X l s Wv true js ih
    · exact nfp_mul X l s Wv 1 (fun t => t) contDiffOn_id (fun Ψ p g => by rw [op_pt]; rfl) js ih
    · exact nfp_mul X l s Wv 2 (fun t => t⁻¹) (contDiffOn_id.inv fun x hx => hx)
        (fun Ψ p g => by rw [op_pt]; rfl) js ih
    · exact nfp_der X l s Wv false js ih
    · exact nfp_mul X l s Wv 4 (fun t => star t) Complex.conjCLE.contDiff.contDiffOn
        (fun Ψ p g => by rw [op_pt]; rfl) js ih
    · exact nfp_mul X l s Wv 5 (fun t => (star t)⁻¹)
        (Complex.conjCLE.contDiff.contDiffOn.inv fun x hx => by simpa using hx)
        (fun Ψ p g => by rw [op_pt]; rfl) js ih

end Word

end Formalism.FourierDecayAlt.P.CutSE.JSW

namespace Formalism.FourierDecayAlt.P.CutSE

theorem spectral_word_normal_form : JSWordNF := by
  intro k r z z' Wp Wq _ _ _ _ _ _ π π' X l s Wv hW js
  obtain ⟨K, m, ab, hm, hab, hE⟩ := JSW.nfp_all X l s Wv hW js
  exact ⟨K, m, ab, fun i => (hm i).continuousOn, hab, hE⟩

end Formalism.FourierDecayAlt.P.CutSE
