import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaAdmissibleLattices
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsRepsImage

noncomputable section

namespace GlobalTheory.TwU.XiTwo

section Abs

open Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Mv
open Formalism.L2.KerInert Formalism.L2.KerInert.PullbackComparison Formalism.L2.KerInert.RepComb

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [DecidableEq W]
  (H : Sesq V) (α : V → ℂ) (H₁ : Sesq W) (α₁ : W → ℂ) (T : V ≃+ W)

omit [DecidableEq W] in
theorem brk_map (hH : ∀ x y, H₁ (T x) (T y) = H x y) (y t : V) : brk H₁ (T y) (T t) = brk H y t := by
  unfold brk altE
  rw [hH]

theorem hatS_map (hH : ∀ x y, H₁ (T x) (T y) = H x y) (vol : ℝ) (SA : Finset V) (Φ : W → ℂ) (x y : V) :
    hatS H₁ vol (SA.image T) (fun s => Φ (s - T x)) (T y) = hatS H vol SA (fun s => Φ (T (s - x))) y := by
  unfold hatS
  rw [Finset.card_image_of_injective _ T.injective, Finset.sum_image (fun a _ b _ h => T.injective h)]
  congr 2
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [brk_map H H₁ T hH]
  simp only [map_sub]

omit [DecidableEq W] in
theorem opU_map (hH : ∀ x y, H₁ (T x) (T y) = H x y) (x : V) (e : W → ℂ) (z : V) :
    opU H₁ (T x) e (T z) = opU H x (fun v => e (T v)) z := by
  unfold opU
  rw [hH, hH, ← map_add]

theorem xiL_map (hH : ∀ x y, H₁ (T x) (T y) = H x y) (hα : ∀ x, α₁ (T x) = α x) (vol : ℝ) (SX SA SB : Finset V)
    (Φ e : W → ℂ) (z : V) :
    xiL H₁ α₁ vol (SX.image T) (SA.image T) (SB.image T) Φ e (T z) =
      xiL H α vol SX SA SB (fun v => Φ (T v)) (fun v => e (T v)) z := by
  rw [xiL_expand, xiL_expand, Finset.sum_image (fun a _ b _ h => T.injective h)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_image (fun a _ b _ h => T.injective h)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [hatS_map H H₁ T hH, hα, hα, hH, hH, ← map_add, opU_map H H₁ T hH]

omit [Module ℂ V] [Module ℂ W] in

theorem isReps_image {Λ₁ Λ₂ : AddSubgroup V} {M₁ M₂ : AddSubgroup W} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S)
    (h1 : ∀ x, T x ∈ M₁ ↔ x ∈ Λ₁) (h2 : ∀ x, T x ∈ M₂ ↔ x ∈ Λ₂) : IsReps M₁ M₂ (S.image T) := by
  first
  | exact @_root_.GlobalTheory.RepresentativesImage.isReps_image
  | exact _root_.GlobalTheory.RepresentativesImage.isReps_image
  | (apply _root_.GlobalTheory.RepresentativesImage.isReps_image <;> assumption)
  | (intros; apply _root_.GlobalTheory.RepresentativesImage.isReps_image <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RepresentativesImage.isReps_image <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RepresentativesImage.isReps_image ..)

omit [Module ℂ V] [Module ℂ W] in

theorem repsOf_eq_image {Λ₁ Λ₂ : AddSubgroup V} {M₁ M₂ : AddSubgroup W} (hS : ∃ S, IsReps Λ₁ Λ₂ S)
    (h1 : ∀ x, T x ∈ M₁ ↔ x ∈ Λ₁) (h2 : ∀ x, T x ∈ M₂ ↔ x ∈ Λ₂) :
    ∃ S : Finset V, IsReps Λ₁ Λ₂ S ∧ repsOf M₁ M₂ = S.image T := by
  classical
  obtain ⟨S, hS⟩ := hS
  have hex : ∃ S₁, IsReps M₁ M₂ S₁ := ⟨_, isReps_image T hS h1 h2⟩
  have hR : IsReps M₁ M₂ (repsOf M₁ M₂) := by
    unfold repsOf
    exact Classical.epsilon_spec hex
  refine ⟨(repsOf M₁ M₂).image T.symm, isReps_image T.symm hR (fun x => ?_) (fun x => ?_), ?_⟩
  · rw [← h1, AddEquiv.apply_symm_apply]
  · rw [← h2, AddEquiv.apply_symm_apply]
  · rw [Finset.image_image]
    have : (T ∘ T.symm : W → W) = id := funext fun x => T.apply_symm_apply x
    rw [this, Finset.image_id]

end Abs

section Main

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV Formalism.L2.Forms Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem xiL_two : ∀ {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (H : Formalism.L2.Th1.H.Sesq V) (α : V → ℂ) (H₁ : Formalism.L2.Th1.H.Sesq W) (α₁ : W → ℂ) (T : V ≃+ W), (∀ x y, H₁ (T x) (T y) = H x y) → (∀ x, α₁ (T x) = α x) → ∀ (A B Λ : AddSubgroup V) (A₁ B₁ Λ₁ : AddSubgroup W), SplitHyp H α A B Λ → (∀ x, T x ∈ Λ₁ ↔ x ∈ Λ) → (∀ x, T x ∈ A₁ ↔ x ∈ A) → (∀ x, T x ∈ B₁ ↔ x ∈ B) → (∃ S, Formalism.L2.Th1.H.IsReps Λ A S) → (∃ S, Formalism.L2.Th1.H.IsReps B (Λ ⊓ A) S) → (∃ S, Formalism.L2.Th1.H.IsReps Λ B S) → ∀ (vol : ℝ) (θ Φ : W → ℂ), (fun v => θ (T v)) ∈ Formalism.L2.Th1.H.fixedBy H α Λ → InvOn A B (fun v => Φ (T v)) → ∀ z, xiL H₁ α₁ vol (repsOf Λ₁ A₁) (repsOf B₁ (Λ₁ ⊓ A₁)) (repsOf Λ₁ B₁) Φ θ (T z) = xiL H α vol (repsOf Λ A) (repsOf B (Λ ⊓ A)) (repsOf Λ B) (fun v => Φ (T v)) (fun v => θ (T v)) z := by
  intro V W _ _ _ _ H α H₁ α₁ T hH hα A B Λ A₁ B₁ Λ₁ hyp hΛ hA hB hX hSA hSB vol θ Φ hθ hΦ z
  classical
  have hΛA : ∀ x, T x ∈ Λ₁ ⊓ A₁ ↔ x ∈ Λ ⊓ A := fun x => by
    rw [AddSubgroup.mem_inf, AddSubgroup.mem_inf, hΛ, hA]
  obtain ⟨SX, rX, eX⟩ := repsOf_eq_image T hX hΛ hA
  obtain ⟨SA, rA, eA⟩ := repsOf_eq_image T hSA hB hΛA
  obtain ⟨SB, rB, eB⟩ := repsOf_eq_image T hSB hΛ hB
  rw [eX, eA, eB, xiL_map H α H₁ α₁ T hH hα]
  exact twist_representatives V H α A B Λ hyp _ _ _ _ _ _ (GlobalTheory.TwU.KerMove.repsOf_of_exists hX) (GlobalTheory.TwU.KerMove.repsOf_of_exists hSA)
    (GlobalTheory.TwU.KerMove.repsOf_of_exists hSB) rX rA rB vol _ hθ _ hΦ z

end Main

end GlobalTheory.TwU.XiTwo
