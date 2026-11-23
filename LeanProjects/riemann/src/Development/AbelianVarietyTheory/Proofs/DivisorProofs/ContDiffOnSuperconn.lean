import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicConnectionAddSection

open Matrix Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.SuperconnSmooth

section Gen

variable {X V W : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V] [SMulCommClass ℝ ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace ℂ W] [SMulCommClass ℝ ℂ W]
  {f : V → W} {U : Set V} {p v : X → V} {s : Set X}

theorem contDiffOn_d10 (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hp : ContDiffOn ℝ ∞ p s)
    (hm : MapsTo p s U) (hv : ContDiffOn ℝ ∞ v s) :
    ContDiffOn ℝ ∞ (fun x => d10 f (p x) (v x)) s := by
  have hd : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f (p x)) s :=
    (hf.fderiv_of_isOpen hU (by simp)).comp hp hm
  unfold d10
  exact ((hd.clm_apply hv).sub ((hd.clm_apply (hv.const_smul _)).const_smul _)).const_smul _

theorem contDiffOn_d01 (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) (hp : ContDiffOn ℝ ∞ p s)
    (hm : MapsTo p s U) (hv : ContDiffOn ℝ ∞ v s) :
    ContDiffOn ℝ ∞ (fun x => d01 f (p x) (v x)) s := by
  have hd : ContDiffOn ℝ ∞ (fun x => fderiv ℝ f (p x)) s :=
    (hf.fderiv_of_isOpen hU (by simp)).comp hp hm
  unfold d01
  exact ((hd.clm_apply hv).add ((hd.clm_apply (hv.const_smul _)).const_smul _)).const_smul _

theorem contDiffOn_wedge {m : ℕ} (i : Fin m) {w : X → Ext m} (hw : ContDiffOn ℝ ∞ w s) :
    ContDiffOn ℝ ∞ (fun x => wedge i (w x)) s :=
  ((wedgeL i).restrictScalars ℝ).contDiff.comp_contDiffOn hw

theorem contDiffOn_contr {m : ℕ} (i : Fin m) {w : X → Ext m} (hw : ContDiffOn ℝ ∞ w s) :
    ContDiffOn ℝ ∞ (fun x => contr i (w x)) s :=
  ((contrL i).restrictScalars ℝ).contDiff.comp_contDiffOn hw

theorem contDiffOn_csmul {m : ℕ} {c : X → ℂ} {w : X → Ext m} (hc : ContDiffOn ℝ ∞ c s)
    (hw : ContDiffOn ℝ ∞ w s) : ContDiffOn ℝ ∞ (fun x => c x • w x) s :=
  contDiffOn_pi.2 fun S => hc.mul (contDiffOn_pi.1 hw S)

theorem contDiffOn_ofReal {c : X → ℝ} (hc : ContDiffOn ℝ ∞ c s) :
    ContDiffOn ℝ ∞ (fun x => (c x : ℂ)) s :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn hc

end Gen

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ} [FiniteDimensional ℂ E]
  {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}

theorem contDiffOn_tauC (hτ : IsPeriodMap B τ) (i j : Fin g) :
    ContDiffOn ℂ ∞ (fun b => τ b i j) B :=
  (GlobalTheory.FlatSmooth.analyticOnNhd_of_differentiableOn hτ.1 (hτ.2.1 i j)).contDiffOn hτ.1.uniqueDiffOn

theorem contDiffOn_im (hτ : IsPeriodMap B τ) (i j : Fin g) :
    ContDiffOn ℝ ∞ (fun b => (τ b i j).im) B :=
  Complex.imCLM.contDiff.comp_contDiffOn ((contDiffOn_tauC hτ i j).restrict_scalars ℝ)

theorem contDiffOn_imPart (hτ : IsPeriodMap B τ) (i j : Fin g) :
    ContDiffOn ℝ ∞ (fun b => imPart τ b i j) B :=
  contDiffOn_ofReal (contDiffOn_im hτ i j)

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
theorem imPart_inv (b : E) (hd : ((τ b).map Complex.im).det ≠ 0) :
    (imPart τ b)⁻¹ = ((τ b).map Complex.im)⁻¹.map (fun t : ℝ => (t : ℂ)) := by
  apply Matrix.inv_eq_left_inv
  have e : imPart τ b = ((τ b).map Complex.im).map Complex.ofRealHom := rfl
  have e' : ((τ b).map Complex.im)⁻¹.map (fun t : ℝ => (t : ℂ)) =
    ((τ b).map Complex.im)⁻¹.map Complex.ofRealHom := rfl
  rw [e, e', ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hd),
    Matrix.map_one _ (map_zero _) (map_one _)]

theorem contDiffOn_imPart_inv (hτ : IsPeriodMap B τ) (i j : Fin g) :
    ContDiffOn ℝ ∞ (fun b => (imPart τ b)⁻¹ i j) B := by
  have hd : ∀ b ∈ B, ((τ b).map Complex.im).det ≠ 0 := fun b hb => (hτ.2.2 b hb).2.det_pos.ne'
  have h1 : ContDiffOn ℝ ∞ (fun b => ((τ b).map Complex.im)⁻¹ i j) B :=
    GlobalTheory.FlatSmooth.contDiffOn_inv_real (fun a c => contDiffOn_im hτ a c) hd i j
  refine (contDiffOn_ofReal h1).congr fun b hb => ?_
  rw [imPart_inv b (hd b hb)]
  rfl

omit [FiniteDimensional ℂ E] in
theorem fderiv_per (hτ : IsPeriodMap B τ) {b : E} (hb : b ∈ B) (y : Fl g) (v : E) (k : Fin g) :
    fderiv ℂ (fun b => per (τ b) y) b v k =
      ∑ i, (y (Sum.inl i) : ℂ) * fderiv ℂ (fun b => τ b i k) b v := by
  have hd : ∀ i k, HasFDerivAt (fun b => τ b i k) (fderiv ℂ (fun b => τ b i k) b) b := fun i k =>
    ((hτ.2.1 i k).differentiableAt (hτ.1.mem_nhds hb)).hasFDerivAt
  have h1 : HasFDerivAt (fun b => per (τ b) y) (ContinuousLinearMap.pi fun k =>
      ∑ i, (y (Sum.inl i) : ℂ) • fderiv ℂ (fun b => τ b i k) b) b := by
    refine hasFDerivAt_pi.2 fun k => ?_
    simp only [per, Pi.add_apply, Matrix.vecMul, dotProduct]
    exact (HasFDerivAt.fun_sum fun i _ => (hd i k).const_mul _).add_const _
  rw [h1.fderiv]
  simp

theorem contDiffOn_hor (hτ : IsPeriodMap B τ) (v : E) :
    ContDiffOn ℝ ∞ (fun P : Pt E g => hor τ P v) (cov B g) := by
  refine contDiffOn_const.prodMk (contDiffOn_pi.2 fun k => ?_)
  have h1 : ∀ i, ContDiffOn ℝ ∞ (fun P : Pt E g => fderiv ℂ (fun b => τ b i k) P.1 v) (cov B g) := by
    intro i
    have h0 : ContDiffOn ℂ ∞ (fun b => fderiv ℂ (fun b => τ b i k) b v) B :=
      ((contDiffOn_tauC hτ i k).fderiv_of_isOpen hτ.1 (by simp)).clm_apply contDiffOn_const
    exact (h0.restrict_scalars ℝ).comp contDiff_fst.contDiffOn fun P (hP : P ∈ cov B g) => hP.1
  have h2 : ContDiffOn ℝ ∞ (fun P : Pt E g => ∑ i, (flat τ P (Sum.inl i) : ℂ) *
      fderiv ℂ (fun b => τ b i k) P.1 v) (cov B g) :=
    ContDiffOn.sum fun i _ => (contDiffOn_ofReal
      (contDiffOn_pi.1 (GlobalTheory.FlatSmooth.contDiffOn_flat hτ) (Sum.inl i))).mul (h1 i)
  exact h2.congr fun P hP => fderiv_per hτ hP.1 _ v k

theorem contDiffOn_nab10 (hτ : IsPeriodMap B τ) {h : Pt E g → ℝ} (hh : ContDiffOn ℝ ∞ h (cov B g))
    (hp : ∀ P ∈ cov B g, 0 < h P) {σ : Pt E g → Ext (n + n + g)} (hσ : ContDiffOn ℝ ∞ σ (cov B g))
    {v : Pt E g → Pt E g} (hv : ContDiffOn ℝ ∞ v (cov B g)) :
    ContDiffOn ℝ ∞ (fun P => pointDifference h σ P (v P)) (cov B g) := by
  have hU := GlobalTheory.FlatSmooth.isOpen_cov hτ
  have hl : ContDiffOn ℝ ∞ (fun Q => (Real.log (h Q) : ℂ)) (cov B g) :=
    contDiffOn_ofReal (hh.log fun P hP => (hp P hP).ne')
  unfold pointDifference
  exact (contDiffOn_d10 hU hσ contDiffOn_id (mapsTo_id _) hv).add
    (contDiffOn_csmul (contDiffOn_d10 hU hl contDiffOn_id (mapsTo_id _) hv) hσ)

theorem contDiffOn_connForm (hτ : IsPeriodMap B τ) (v : E) {σ : Pt E g → Ext (n + n + g)}
    (hσ : ContDiffOn ℝ ∞ σ (cov B g)) :
    ContDiffOn ℝ ∞ (fun P => connForm τ P.1 v (σ P)) (cov B g) := by
  have hm : MapsTo (Prod.fst : Pt E g → E) (cov B g) B := fun P hP => hP.1
  unfold connForm
  refine ContDiffOn.sum fun a _ => ContDiffOn.sum fun c _ =>
    contDiffOn_csmul ?_ (contDiffOn_wedge _ (contDiffOn_contr _ hσ))
  simp only [Matrix.mul_apply, Matrix.of_apply]
  exact ContDiffOn.sum fun e _ =>
    (contDiffOn_d01 hτ.1 (contDiffOn_imPart hτ a e) contDiff_fst.contDiffOn hm contDiffOn_const).mul
      ((contDiffOn_imPart_inv hτ e c).comp contDiff_fst.contDiffOn hm)

theorem contDiffOn_superconn (hτ : IsPeriodMap B τ) {h : Pt E g → ℝ}
    (hh : ContDiffOn ℝ ∞ h (cov B g)) (hp : ∀ P ∈ cov B g, 0 < h P) (β : Fin n → E) (u : ℝ)
    {σ : Pt E g → Ext (n + n + g)} (hσ : ContDiffOn ℝ ∞ σ (cov B g)) :
    ContDiffOn ℝ ∞ (superconn τ h β u σ) (cov B g) := by
  have hU := GlobalTheory.FlatSmooth.isOpen_cov hτ
  have hm : MapsTo (Prod.fst : Pt E g → E) (cov B g) B := fun P hP => hP.1
  have h1 : ContDiffOn ℝ ∞ (nablaE τ h β σ) (cov B g) := by
    unfold nablaE
    exact ContDiffOn.sum fun i _ =>
      (contDiffOn_wedge _ (contDiffOn_nab10 hτ hh hp hσ (contDiffOn_hor hτ _))).add
        (contDiffOn_wedge _ ((contDiffOn_d01 hU hσ contDiffOn_id (mapsTo_id _)
          (contDiffOn_hor hτ _)).add (contDiffOn_connForm hτ _ hσ)))
  have h2 : ContDiffOn ℝ ∞ (dbarV σ) (cov B g) := by
    unfold dbarV
    exact ContDiffOn.sum fun a _ =>
      contDiffOn_wedge _ (contDiffOn_d01 hU hσ contDiffOn_id (mapsTo_id _) contDiffOn_const)
  have h3 : ContDiffOn ℝ ∞ (dbarAdj τ h σ) (cov B g) := by
    unfold dbarAdj
    exact (ContDiffOn.sum fun a _ => ContDiffOn.sum fun c _ => contDiffOn_csmul
      (contDiffOn_const.mul ((contDiffOn_imPart hτ a c).comp contDiff_fst.contDiffOn hm))
      (contDiffOn_contr _ (contDiffOn_nab10 hτ hh hp hσ contDiffOn_const))).neg
  unfold superconn
  exact h1.add ((h2.add h3).const_smul _)

end GlobalTheory.SuperconnSmooth

theorem GlobalTheory.SuperconnSmooth.main : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}
    [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ →
    ∀ {h : Pt E g → ℝ}, ContDiffOn ℝ ∞ h (cov B g) → (∀ P ∈ cov B g, 0 < h P) →
    ∀ (β : Fin n → E) (u : ℝ) {σ : Pt E g → Ext (n + n + g)}, ContDiffOn ℝ ∞ σ (cov B g) →
    ContDiffOn ℝ ∞ (superconn τ h β u σ) (cov B g) :=
  fun hτ _ hh hp β u _ hσ => GlobalTheory.SuperconnSmooth.contDiffOn_superconn hτ hh hp β u hσ
