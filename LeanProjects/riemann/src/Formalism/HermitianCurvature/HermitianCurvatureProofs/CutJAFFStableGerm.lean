import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStable2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.FFS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section germ

variable {k r : ℕ} {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

theorem deriv_const_smul_any (c : ℂ) (h : ℝ → E') (t : ℝ) :
    deriv (fun s => c • h s) t = c • deriv h t := by
  by_cases hc : c = 0
  · simp [hc]
  by_cases hd : DifferentiableAt ℝ h t
  · exact deriv_const_smul c hd
  · have hd' : ¬ DifferentiableAt ℝ (fun s => c • h s) t := by
      intro h'
      apply hd
      have e : h = fun s => c⁻¹ • (c • h s) := by
        funext s
        simp [smul_smul, inv_mul_cancel₀ hc]
      rw [e]
      exact h'.const_smul c⁻¹
    rw [deriv_zero_of_not_differentiableAt hd, deriv_zero_of_not_differentiableAt hd', smul_zero]

theorem rdV_smul (X : B.Mat k r) (c : ℂ) (f : B.Mat k r → E') :
    RdV X (c • f) = c • RdV X f := by
  funext g
  exact deriv_const_smul_any c (fun t => f (g * NormedSpace.exp ((t : ℂ) • X))) 0

theorem rw_smul (w : List (B.Mat k r)) (c : ℂ) (f : B.Mat k r → E') :
    B.Rw w (c • f) = c • B.Rw w f := by
  induction w with
  | nil => rfl
  | cons X w ih =>
    show RdV X (B.Rw w (c • f)) = c • RdV X (B.Rw w f)
    rw [ih, rdV_smul]

theorem rdV_local {X : B.Mat k r} (hX : B.inLie k r X) {U : Set (B.Mat k r)} (hU : IsOpen U)
    {f f' : B.Mat k r → E'} (he : ∀ x ∈ U, x ∈ B.GV k r → f x = f' x) {g : B.Mat k r} (hg : g ∈ U)
    (hgG : g ∈ B.GV k r) : RdV X f g = RdV X f' g := by
  show deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0 =
    deriv (fun t : ℝ => f' (g * NormedSpace.exp ((t : ℂ) • X))) 0
  apply Filter.EventuallyEq.deriv_eq
  have hc : Continuous (fun t : ℝ => g * NormedSpace.exp ((t : ℂ) • X)) :=
    (Formalism.FourierDecayAlt.P.B5.curve_contDiff g X).continuous
  have hev : ∀ᶠ t : ℝ in nhds (0 : ℝ), g * NormedSpace.exp (((t : ℝ) : ℂ) • X) ∈ U := by
    apply hc.continuousAt.preimage_mem_nhds
    show U ∈ nhds (g * NormedSpace.exp (((0 : ℝ) : ℂ) • X))
    rw [Formalism.FourierDecayAlt.P.B5.curve_zero]
    exact hU.mem_nhds hg
  filter_upwards [hev] with t ht
  exact he _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hgG hX t)

theorem rw_local (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X) {U : Set (B.Mat k r)} (hU : IsOpen U)
    {f f' : B.Mat k r → E'} (he : ∀ x ∈ U, x ∈ B.GV k r → f x = f' x) :
    ∀ x ∈ U, x ∈ B.GV k r → B.Rw w f x = B.Rw w f' x := by
  induction w with
  | nil => exact he
  | cons X w ih =>
    intro x hx hxG
    exact rdV_local (hw X (by simp)) hU (ih (fun Y hY => hw Y (by simp [hY]))) hx hxG

theorem sum_map_smul' {ι M : Type*} [AddCommMonoid M] [Module ℂ M] (c : ℂ) (l : List ι) (φ : ι → M) :
    (l.map fun i => c • φ i).sum = c • (l.map φ).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, smul_add]

end germ

theorem germ_operators_holds : GermOps := by
  intro k r Wp Wq _ _ _ _ _ Θ
  refine ⟨fun U f f' hU he g hg hgG => ⟨?_, ?_⟩, fun c f g => ⟨?_, ?_⟩⟩
  · unfold B.opApply
    congr 1
    apply List.map_congr_left
    intro T _
    rw [rw_local T.word T.word_lie hU he g hg hgG]
  · unfold B.opAdj
    congr 1
    apply List.map_congr_left
    intro T _
    rw [rw_local T.word.reverse (fun X hX => T.word_lie X (List.mem_reverse.1 hX)) hU
      (f := fun x => T.coefAdj x (f x)) (f' := fun x => T.coefAdj x (f' x))
      (fun x hx hxG => by simp only [he x hx hxG]) g hg hgG]
  · unfold B.opApply
    rw [← sum_map_smul']
    congr 1
    apply List.map_congr_left
    intro T _
    rw [rw_smul, Pi.smul_apply, map_smul]
  · unfold B.opAdj
    rw [← sum_map_smul']
    congr 1
    apply List.map_congr_left
    intro T _
    have e : (fun x => T.coefAdj x ((c • f) x)) = c • (fun x => T.coefAdj x (f x)) := by
      funext x; simp
    rw [e, rw_smul, Pi.smul_apply, smul_comm]

end Formalism.FourierDecayAlt.P.CutMP.JA.FFS
