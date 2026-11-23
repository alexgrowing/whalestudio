import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormClosedOnCover
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SuperconnDiff

section General

variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem wedge_at {N : ℕ} (i : Fin N) {F : Y → Ext N} {y : Y} (hF : DifferentiableAt ℝ F y) :
    DifferentiableAt ℝ (fun q => wedge i (F q)) y := by
  rw [differentiableAt_pi]
  intro S
  simp only [wedge]
  split_ifs
  · exact ((differentiableAt_pi.1 hF) _).const_mul _
  · exact differentiableAt_const _

theorem contr_at {N : ℕ} (i : Fin N) {F : Y → Ext N} {y : Y} (hF : DifferentiableAt ℝ F y) :
    DifferentiableAt ℝ (fun q => contr i (F q)) y := by
  rw [differentiableAt_pi]
  intro S
  simp only [contr]
  split_ifs
  · exact differentiableAt_const _
  · exact ((differentiableAt_pi.1 hF) _).const_mul _

theorem fderiv_at {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {f : Y → W} {y : Y}
    (hf : ContDiffAt ℝ ∞ f y) : DifferentiableAt ℝ (fderiv ℝ f) y :=
  (hf.fderiv_right (m := 1) (by norm_cast)).differentiableAt one_ne_zero

variable {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W]

theorem differentiableAt_d01_comp_of_differentiableAt {f : V → W} {p v : Y → V} {y : Y} (hf : DifferentiableAt ℝ (fderiv ℝ f) (p y))
    (hp : DifferentiableAt ℝ p y) (hv : DifferentiableAt ℝ v y) :
    DifferentiableAt ℝ (fun q => d01 f (p q) (v q)) y := by
  have hc : DifferentiableAt ℝ (fun q => fderiv ℝ f (p q)) y := hf.comp y hp
  unfold d01
  exact ((hc.clm_apply hv).add
    ((hc.clm_apply (hv.const_smul Complex.I)).const_smul Complex.I)).const_smul _

theorem differentiableAt_d10_comp_of_differentiableAt {f : V → W} {p v : Y → V} {y : Y} (hf : DifferentiableAt ℝ (fderiv ℝ f) (p y))
    (hp : DifferentiableAt ℝ p y) (hv : DifferentiableAt ℝ v y) :
    DifferentiableAt ℝ (fun q => d10 f (p q) (v q)) y := by
  have hc : DifferentiableAt ℝ (fun q => fderiv ℝ f (p q)) y := hf.comp y hp
  unfold d10
  exact ((hc.clm_apply hv).sub
    ((hc.clm_apply (hv.const_smul Complex.I)).const_smul Complex.I)).const_smul _

theorem det_at {ι : Type} [Fintype ι] [DecidableEq ι] {A : Y → Matrix ι ι ℂ} {y : Y}
    (h : ∀ a b, ContDiffAt ℝ ∞ (fun q => A q a b) y) : ContDiffAt ℝ ∞ (fun q => (A q).det) y := by
  simp only [Matrix.det_apply']
  exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun i _ => h _ _)

theorem inv_at {ι : Type} [Fintype ι] [DecidableEq ι] {A : Y → Matrix ι ι ℂ} {y : Y}
    (h : ∀ a b, ContDiffAt ℝ ∞ (fun q => A q a b) y) (h0 : (A y).det ≠ 0) (a b : ι) :
    ContDiffAt ℝ ∞ (fun q => (A q)⁻¹ a b) y := by
  have e : (fun q => (A q)⁻¹ a b) =
      fun q => ((A q).det)⁻¹ * ((A q).updateRow b (Pi.single a 1)).det := by
    funext q
    rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_apply, Ring.inverse_eq_inv',
      smul_eq_mul]
  rw [e]
  refine ((det_at h).inv h0).mul (det_at fun i i' => ?_)
  by_cases hi : i = b
  · subst hi
    simpa using contDiffAt_const
  · simpa [Matrix.updateRow_ne hi] using h i i'

end General

section Family

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

theorem fderiv_per_apply {τ : E → Matrix (Fin g) (Fin g) ℂ} {b : E}
    (hτ : ∀ k l, DifferentiableAt ℂ (fun b' => τ b' k l) b) (x : Fl g) (v : E) :
    fderiv ℂ (fun b' => per (τ b') x) b v =
      fun k => ∑ l, (x (Sum.inl l) : ℂ) * fderiv ℂ (fun b' => τ b' l k) b v := by
  have hk : ∀ k, HasFDerivAt (fun b' => per (τ b') x k)
      (∑ l, (x (Sum.inl l) : ℂ) • fderiv ℂ (fun b' => τ b' l k) b) b := by
    intro k
    have e : (fun b' => per (τ b') x k) =
        fun b' => ∑ l, (x (Sum.inl l) : ℂ) * τ b' l k + (x (Sum.inr k) : ℂ) := by
      funext b'
      simp [per, Matrix.vecMul, dotProduct]
    rw [e]
    exact (HasFDerivAt.fun_sum (u := Finset.univ)
      (A := fun l b' => (x (Sum.inl l) : ℂ) * τ b' l k)
      fun l _ => ((hτ l k).hasFDerivAt.const_mul _)).add_const _
  rw [(hasFDerivAt_pi.2 hk).fderiv]
  funext k
  simp [ContinuousLinearMap.sum_apply, smul_eq_mul]

theorem comp_fst {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {f : E → W} {b : E}
    {z : Fin g → ℂ} (hf : DifferentiableAt ℝ f b) :
    DifferentiableAt ℝ (fun Q : Pt E g => f Q.1) (b, z) :=
  hf.comp (b, z) differentiableAt_fst

variable [FiniteDimensional ℂ E] {m : ℕ}

theorem superconn_at {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ} {M : Submodule ℤ (Fl g)}
    {j : Fl g → Pt E g → ℂ} {h : Pt E g → ℝ} (hD : IsDatum B τ M j h) (β : Fin m → E) {b : E}
    (hb : b ∈ B) (s : Pt E g → Ext (m + m + g)) (hs : ContDiff ℝ ∞ s) (u : ℝ)
    (z : Fin g → ℂ) : DifferentiableAt ℝ (superconn τ h β u s) (b, z) := by
  obtain ⟨hτ, -, -, hh⟩ := hD
  have hP : ((b, z) : Pt E g) ∈ cov B g := ⟨hb, trivial⟩
  have hcov : cov B g ∈ 𝓝 ((b, z) : Pt E g) := (hτ.1.prod isOpen_univ).mem_nhds hP
  have hBn : B ∈ 𝓝 b := hτ.1.mem_nhds hb
  have hsd : DifferentiableAt ℝ s (b, z) := (hs.differentiable (by simp)).differentiableAt
  have hds : DifferentiableAt ℝ (fderiv ℝ s) (b, z) := fderiv_at hs.contDiffAt
  have hlog : ContDiffAt ℝ ∞ (fun Q : Pt E g => (Real.log (h Q) : ℂ)) (b, z) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp (b, z)
      ((hh.1.contDiffAt hcov).log (hh.2.1 _ hP).ne')
  have hdlog := fderiv_at hlog
  have hτc : ∀ k l, ContDiffAt ℂ ∞ (fun b' => τ b' k l) b := fun k l =>
    GlobalTheory.SCV.contDiffAt_of_differentiableOn (hτ.2.1 k l) hBn ∞
  have him : ∀ k l, ContDiffAt ℝ ∞ (fun b' => imPart τ b' k l) b := fun k l =>
    (Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff).contDiffAt.comp b
      ((hτc k l).restrict_scalars ℝ)
  have hdet : (imPart τ b).det ≠ 0 := by
    have e : imPart τ b = Complex.ofRealHom.mapMatrix ((τ b).map Complex.im) := by
      ext k l
      simp [imPart]
    rw [e, ← RingHom.map_det]
    exact Complex.ofReal_ne_zero.2 (hτ.2.2 b hb).2.det_pos.ne'
  have hinvP : ∀ k l, DifferentiableAt ℝ (fun Q : Pt E g => (imPart τ Q.1)⁻¹ k l) (b, z) :=
    fun k l => by
      exact comp_fst ((inv_at him hdet k l).differentiableAt (by simp))
  have himP : ∀ k l, DifferentiableAt ℝ (fun Q : Pt E g => imPart τ Q.1 k l) (b, z) :=
    fun k l => by
      exact comp_fst ((him k l).differentiableAt (by simp))
  have hflat : DifferentiableAt ℝ (flat τ) (b, z) :=
    (GlobalTheory.FlatClosed.contDiffAt_flat hτ hP).differentiableAt (by simp)
  have hhor : ∀ v : E, DifferentiableAt ℝ (fun Q : Pt E g => hor τ Q v) (b, z) := by
    intro v
    have key : (fun Q : Pt E g => hor τ Q v) =ᶠ[𝓝 (b, z)] fun Q => (v, fun k =>
        ∑ l, ((flat τ Q (Sum.inl l) : ℝ) : ℂ) * fderiv ℂ (fun b' => τ b' l k) Q.1 v) := by
      filter_upwards [hcov] with Q hQ
      simp only [hor]
      rw [fderiv_per_apply (fun k l => (hτ.2.1 k l).differentiableAt (hτ.1.mem_nhds hQ.1))]
    refine DifferentiableAt.congr_of_eventuallyEq ?_ key
    refine DifferentiableAt.prodMk (differentiableAt_const v) (differentiableAt_pi.2 fun k => ?_)
    refine DifferentiableAt.fun_sum fun l _ => DifferentiableAt.fun_mul ?_ ?_
    · exact Complex.ofRealCLM.differentiableAt.comp (b, z) (differentiableAt_pi.1 hflat (Sum.inl l))
    · have h1 : DifferentiableAt ℂ (fderiv ℂ (fun b' => τ b' l k)) b :=
        ((hτc l k).fderiv_right (m := 1) (by norm_cast)).differentiableAt one_ne_zero
      exact comp_fst ((h1.clm_apply (differentiableAt_const v)).restrictScalars ℝ)
  have hnab : ∀ v : Pt E g → Pt E g, DifferentiableAt ℝ v (b, z) →
      DifferentiableAt ℝ (fun Q => pointDifference h s Q (v Q)) (b, z) := fun v hv =>
    (differentiableAt_d10_comp_of_differentiableAt (p := fun Q => Q) hds differentiableAt_id hv).fun_add
      ((differentiableAt_d10_comp_of_differentiableAt (p := fun Q => Q) hdlog differentiableAt_id hv).fun_smul hsd)
  have hconn : ∀ v : E, DifferentiableAt ℝ (fun Q : Pt E g => connForm τ Q.1 v (s Q)) (b, z) := by
    intro v
    simp only [connForm]
    refine DifferentiableAt.fun_sum fun a _ => DifferentiableAt.fun_sum fun c _ =>
      DifferentiableAt.fun_smul ?_ (wedge_at _ (contr_at _ hsd))
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact DifferentiableAt.fun_sum fun k _ =>
      (differentiableAt_d01_comp_of_differentiableAt (p := fun Q : Pt E g => Q.1) (fderiv_at (him a k)) (comp_fst differentiableAt_id)
        (differentiableAt_const v)).fun_mul (hinvP k c)
  show DifferentiableAt ℝ (fun P => nablaE τ h β s P +
    (Real.sqrt u : ℂ) • (dbarV s P + dbarAdj τ h s P)) (b, z)
  simp only [nablaE, dbarV, dbarAdj]
  refine DifferentiableAt.fun_add ?_ ((DifferentiableAt.fun_add ?_ ?_).fun_const_smul _)
  · exact DifferentiableAt.fun_sum fun i _ => (wedge_at _ (hnab _ (hhor (β i)))).fun_add
      (wedge_at _ ((differentiableAt_d01_comp_of_differentiableAt (p := fun Q => Q) hds differentiableAt_id (hhor (β i))).fun_add
        (hconn (β i))))
  · exact DifferentiableAt.fun_sum fun a _ => wedge_at _
      (differentiableAt_d01_comp_of_differentiableAt (p := fun Q => Q) hds differentiableAt_id (differentiableAt_const _))
  · exact (DifferentiableAt.fun_sum fun a _ => DifferentiableAt.fun_sum fun c _ =>
      ((himP a c).const_mul 2).fun_smul (contr_at _ (hnab _ (differentiableAt_const _)))).fun_neg

end Family

theorem superconn_differentiableAt : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {g m : ℕ} {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    {M : Submodule ℤ (Fl g)} {j : Fl g → Pt E g → ℂ} {h : Pt E g → ℝ}, IsDatum B τ M j h →
    ∀ (β : Fin m → E) {b : E}, b ∈ B → ∀ (G : (Fin g → ℂ) → Ext (m + m + g)), ContDiff ℝ ∞ G →
    ∀ (u : ℝ) (z : Fin g → ℂ), DifferentiableAt ℝ (superconn τ h β u fun P => G P.2) (b, z) :=
  fun hD β _ hb G hG u z => superconn_at hD β hb (fun P => G P.2) (hG.comp contDiff_snd) u z

end GlobalTheory.SuperconnDiff
