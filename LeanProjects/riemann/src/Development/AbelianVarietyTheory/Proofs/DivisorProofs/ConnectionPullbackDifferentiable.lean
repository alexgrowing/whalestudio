import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.D10D01PullbackHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.D01CompHolomorphicMapStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HorizontalLiftPullbackStatement
open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Pullback
open scoped ContDiff

set_option autoImplicit false

namespace GlobalTheory.TorsionForm.SuperconnComp

theorem superconn_comp {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
    [NormedSpace ℂ E'] {g n : ℕ} (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (φ : E' → E)
    (β : Fin n → E') (u : ℝ) (s : Pt E g → Ext (n + n + g)) (P : Pt E' g)
    (hφ : DifferentiableAt ℂ φ P.1) (hτ : ∀ i j, DifferentiableAt ℂ (fun b => τ b i j) (φ P.1))
    (hh : DifferentiableAt ℝ h (φ P.1, P.2)) (hh0 : h (φ P.1, P.2) ≠ 0)
    (hs : DifferentiableAt ℝ s (φ P.1, P.2)) :
    superconn (τ ∘ φ) (fun Q => h (φ Q.1, Q.2)) β u (fun Q => s (φ Q.1, Q.2)) P =
      superconn τ h (fun i => fderiv ℂ φ P.1 (β i)) u s (φ P.1, P.2) := by
  set L : Pt E g → ℂ := fun Q => (Real.log (h Q) : ℂ) with hL
  have hLd : DifferentiableAt ℝ L (φ P.1, P.2) :=
    Complex.ofRealCLM.differentiableAt.comp _ (hh.log hh0)
  have hch := fun w : Pt E' g => GlobalTheory.T.d10_d01_comp_fst_eq_fderiv_of_holomorphic φ s L P w hφ hs hLd

  have hpair : ∀ v : E', ((fderiv ℂ φ P.1 (hor (τ ∘ φ) P v).1, (hor (τ ∘ φ) P v).2) : Pt E g) =
      hor τ (φ P.1, P.2) (fderiv ℂ φ P.1 v) := by
    intro v; rw [GlobalTheory.T.horizontal_lift_pullback τ φ P v hφ hτ]; rfl
  have hvert : ∀ a : Fin g, ((fderiv ℂ φ P.1 (vert E' a).1, (vert E' a).2) : Pt E g) = vert E a := by
    intro a; simp [vert]
  have hN : ∀ w : Pt E' g, pointDifference (fun Q => h (φ Q.1, Q.2)) (fun Q => s (φ Q.1, Q.2)) P w =
      pointDifference h s (φ P.1, P.2) (fderiv ℂ φ P.1 w.1, w.2) := by
    intro w; unfold pointDifference; rw [(hch w).1, (hch w).2.2]
  have hD : ∀ w : Pt E' g, d01 (fun Q => s (φ Q.1, Q.2)) P w =
      d01 s (φ P.1, P.2) (fderiv ℂ φ P.1 w.1, w.2) := fun w => (hch w).2.1
  have hC : ∀ (v : E') (x : Ext (n + n + g)), connForm (τ ∘ φ) P.1 v x =
      connForm τ (φ P.1) (fderiv ℂ φ P.1 v) x := by
    intro v x
    unfold connForm
    have e : (Matrix.of fun a e => d01 (fun b' => imPart (τ ∘ φ) b' a e) P.1 v) =
        Matrix.of fun a e => d01 (fun b' => imPart τ b' a e) (φ P.1) (fderiv ℂ φ P.1 v) := by
      ext a e
      simp only [Matrix.of_apply]
      have hH : DifferentiableAt ℝ (fun b' => imPart τ b' a e) (φ P.1) := by
        have h1 : DifferentiableAt ℝ (fun b => τ b a e) (φ P.1) := (hτ a e).restrictScalars ℝ
        have h2 := Complex.ofRealCLM.differentiableAt.comp _ (Complex.imCLM.differentiableAt.comp _ h1)
        simpa [imPart, Function.comp_def] using h2
      exact GlobalTheory.T.d01_comp_holomorphic_eq_d01_fderiv φ (fun b' => imPart τ b' a e) P.1 v hφ hH
    rw [e]
    rfl
  unfold superconn nablaE dbarV dbarAdj
  simp only [hN, hD, hC, hpair, hvert]
  rfl

end GlobalTheory.TorsionForm.SuperconnComp
