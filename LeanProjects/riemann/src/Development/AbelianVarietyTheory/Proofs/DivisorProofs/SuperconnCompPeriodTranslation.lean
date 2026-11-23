import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicConnectionAddSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationPreservesFlatForm
open Matrix Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped Real ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TranslNatural

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g : ℕ}

theorem per_add' (τ : Matrix (Fin g) (Fin g) ℂ) (y x : Fl g) : per τ (y + x) = per τ y + per τ x := by
  ext i
  simp only [per, Matrix.vecMul, dotProduct, Pi.add_apply, Complex.ofReal_add, add_mul,
    Finset.sum_add_distrib]
  ring

theorem differentiableAt_per {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap B τ) (y : Fl g) {b : E} (hb : b ∈ B) :
    DifferentiableAt ℂ (fun b => per (τ b) y) b := by
  have : DifferentiableOn ℂ (fun b => per (τ b) y) B := by
    rw [differentiableOn_pi]
    intro i
    simp only [per, Matrix.vecMul, dotProduct, Pi.add_apply]
    exact (DifferentiableOn.fun_sum fun j _ => (hτ.2.1 j i).const_mul _).add_const _
  exact this.differentiableAt (hτ.1.mem_nhds hb)

def dTransl (τ : E → Matrix (Fin g) (Fin g) ℂ) (x : Fl g) (b : E) : Pt E g →L[ℂ] Pt E g :=
  (ContinuousLinearMap.fst ℂ E (Fin g → ℂ)).prod (ContinuousLinearMap.snd ℂ E (Fin g → ℂ) +
    (fderiv ℂ (fun b => per (τ b) x) b).comp (ContinuousLinearMap.fst ℂ E (Fin g → ℂ)))

theorem hasFDerivAt_transl {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap B τ) (x : Fl g) {P : Pt E g} (hP : P.1 ∈ B) :
    HasFDerivAt (transl τ x) (dTransl τ x P.1) P := by
  have h1 : HasFDerivAt (fun Q : Pt E g => per (τ Q.1) x)
      ((fderiv ℂ (fun b => per (τ b) x) P.1).comp (ContinuousLinearMap.fst ℂ E (Fin g → ℂ))) P :=
    (differentiableAt_per hτ x hP).hasFDerivAt.comp P hasFDerivAt_fst
  exact hasFDerivAt_fst.prodMk (hasFDerivAt_snd.add h1)

theorem fderiv_transl {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap B τ) (x : Fl g) {P : Pt E g} (hP : P.1 ∈ B) :
    fderiv ℝ (transl τ x) P = (dTransl τ x P.1).restrictScalars ℝ :=
  ((hasFDerivAt_transl hτ x hP).restrictScalars ℝ).fderiv

theorem fderiv_comp_transl {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap B τ) (x : Fl g) {P : Pt E g} (hP : P.1 ∈ B) (f : Pt E g → W) :
    fderiv ℝ (fun Q => f (transl τ x Q)) P =
      (fderiv ℝ f (transl τ x P)).comp (fderiv ℝ (transl τ x) P) := by
  have hT : DifferentiableAt ℝ (transl τ x) P :=
    ((hasFDerivAt_transl hτ x hP).restrictScalars ℝ).differentiableAt
  have hT' : DifferentiableAt ℝ (transl τ (-x)) (transl τ x P) :=
    ((hasFDerivAt_transl hτ (-x) (P := transl τ x P) hP).restrictScalars ℝ).differentiableAt
  by_cases hf : DifferentiableAt ℝ f (transl τ x P)
  · exact fderiv_comp (g := f) P hf hT
  · have hnd : ¬ DifferentiableAt ℝ (fun Q => f (transl τ x Q)) P := by
      intro hc
      apply hf
      have : DifferentiableAt ℝ ((fun Q => f (transl τ x Q)) ∘ transl τ (-x)) (transl τ x P) := by
        apply DifferentiableAt.comp _ _ hT'
        rwa [GlobalTheory.TranslFlat.transl_neg_transl]
      have he : (fun Q => f (transl τ x Q)) ∘ transl τ (-x) = f := by
        funext Q; simp [GlobalTheory.TranslFlat.transl_transl_neg]
      rwa [he] at this
    rw [fderiv_zero_of_not_differentiableAt hf, fderiv_zero_of_not_differentiableAt hnd,
      ContinuousLinearMap.zero_comp]

theorem fderiv_transl_smul {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap B τ) (x : Fl g) {P : Pt E g} (hP : P.1 ∈ B) (v : Pt E g) :
    fderiv ℝ (transl τ x) P (Complex.I • v) = Complex.I • fderiv ℝ (transl τ x) P v := by
  rw [fderiv_transl hτ x hP]
  exact (dTransl τ x P.1).map_smul Complex.I v

theorem fderiv_transl_vert {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap B τ) (x : Fl g) {P : Pt E g} (hP : P.1 ∈ B) (a : Fin g) :
    fderiv ℝ (transl τ x) P (vert E a) = vert E a := by
  rw [fderiv_transl hτ x hP]
  simp [dTransl, vert]

theorem fderiv_transl_hor {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap B τ) (x : Fl g) {P : Pt E g} (hP : P.1 ∈ B) (v : E) :
    fderiv ℝ (transl τ x) P (hor τ P v) = hor τ (transl τ x P) v := by
  have hfl : flat τ (transl τ x P) = flat τ P + x :=
    GlobalTheory.TranslFlat.flat_transl hτ x (P := P) ⟨hP, Set.mem_univ _⟩
  have e : (fun b => per (τ b) (flat τ P + x)) =
      fun b => per (τ b) (flat τ P) + per (τ b) x := by
    funext b; exact per_add' _ _ _
  have hd : fderiv ℂ (fun b => per (τ b) (flat τ P + x)) P.1 =
      fderiv ℂ (fun b => per (τ b) (flat τ P)) P.1 + fderiv ℂ (fun b => per (τ b) x) P.1 := by
    rw [e]
    exact fderiv_add (differentiableAt_per hτ _ hP) (differentiableAt_per hτ _ hP)
  rw [fderiv_transl hτ x hP]
  simp only [hor, hfl]
  show _ = (v, fderiv ℂ (fun b => per (τ b) (flat τ P + x)) P.1 v)
  rw [hd]
  simp [dTransl]

section D

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [SMul ℂ W]

theorem d10_comp_transl_eq_of_isPeriodMap {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap B τ) (x : Fl g) {P : Pt E g} (hP : P.1 ∈ B) (f : Pt E g → W) (v : Pt E g) :
    d10 (fun Q => f (transl τ x Q)) P v = d10 f (transl τ x P) (fderiv ℝ (transl τ x) P v) := by
  simp only [d10, fderiv_comp_transl hτ x hP f, ContinuousLinearMap.comp_apply,
    fderiv_transl_smul hτ x hP]

theorem d01_comp_transl_eq_of_isPeriodMap {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}
    (hτ : IsPeriodMap B τ) (x : Fl g) {P : Pt E g} (hP : P.1 ∈ B) (f : Pt E g → W) (v : Pt E g) :
    d01 (fun Q => f (transl τ x Q)) P v = d01 f (transl τ x P) (fderiv ℝ (transl τ x) P v) := by
  simp only [d01, fderiv_comp_transl hτ x hP f, ContinuousLinearMap.comp_apply,
    fderiv_transl_smul hτ x hP]

end D

theorem superconn_transl : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ} {B : Set E}
    {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → ∀ (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ)
    (x : Fl g) (s : Pt E g → Ext (n + n + g)) {P : Pt E g}, P.1 ∈ B →
    superconn τ (fun Q => h (transl τ x Q)) β u (fun Q => s (transl τ x Q)) P =
      superconn τ h β u s (transl τ x P) := by
  intro E _ _ g n B τ hτ h β u x s P hP
  have e1 : ∀ v, d10 (fun Q => s (transl τ x Q)) P v =
      d10 s (transl τ x P) (fderiv ℝ (transl τ x) P v) := d10_comp_transl_eq_of_isPeriodMap hτ x hP s
  have e2 : ∀ v, d10 (fun Q => (Real.log (h (transl τ x Q)) : ℂ)) P v =
      d10 (fun Q => (Real.log (h Q) : ℂ)) (transl τ x P) (fderiv ℝ (transl τ x) P v) :=
    d10_comp_transl_eq_of_isPeriodMap hτ x hP (fun Q => (Real.log (h Q) : ℂ))
  have e3 : ∀ v, d01 (fun Q => s (transl τ x Q)) P v =
      d01 s (transl τ x P) (fderiv ℝ (transl τ x) P v) := d01_comp_transl_eq_of_isPeriodMap hτ x hP s
  have e4 : (transl τ x P).1 = P.1 := rfl
  simp only [superconn, nablaE, dbarV, dbarAdj, pointDifference, e1, e2, e3, e4,
    fderiv_transl_hor hτ x hP, fderiv_transl_vert hτ x hP]

end GlobalTheory.TranslNatural
