import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum

noncomputable section

namespace GlobalTheory.PerpFrameTranslate

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

variable {P Q P' Q' : ℕ}

theorem act_mul (g h : UpqT P Q) (x : Sp P Q) : act (g * h) x = act g (act h x) := by
  unfold act
  rw [Matrix.mulVec_mulVec]; rfl

theorem act_one (x : Sp P Q) : act (1 : UpqT P Q) x = x := Matrix.one_mulVec x

theorem act_inv_act (g : UpqT P Q) (x : Sp P Q) : act g⁻¹ (act g x) = x := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_act_inv (g : UpqT P Q) (x : Sp P Q) : act g (act g⁻¹ x) = x := by
  rw [← act_mul, mul_inv_cancel, act_one]

theorem herm_eq_dot (x y : Sp P Q) : herm x y = star y ⬝ᵥ (Formalism.UG.Jpq P Q *ᵥ x) := by
  rw [herm_eq_hform]
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Pi.star_apply]
  rfl

theorem herm_act (g : UpqT P Q) (x y : Sp P Q) : herm (act g x) (act g y) = herm x y := by
  have hu : (UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q * UpqT.mat g = Formalism.UG.Jpq P Q := g.2
  rw [herm_eq_dot, herm_eq_dot, act, act, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hu]

theorem herm_eq_sum (x y : Sp P Q) : herm x y = ∑ i, (sg i : ℂ) * (x i * star (y i)) := by
  simp [herm, sg, Fintype.sum_sum_type, sub_eq_add_neg]

def incl (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) :
    Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ :=
  Matrix.of fun i b => if i = e (some b) then 1 else 0

theorem incl_none (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (u : Sp P' Q') :
    (incl e *ᵥ u) (e none) = 0 := by
  simp [incl, Matrix.mulVec, dotProduct]

theorem incl_some (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (u : Sp P' Q')
    (b : Fin P' ⊕ Fin Q') : (incl e *ᵥ u) (e (some b)) = u b := by
  simp [incl, Matrix.mulVec, dotProduct]

theorem ext_coord (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) {x y : Sp P Q}
    (h0 : x (e none) = y (e none)) (h1 : ∀ b, x (e (some b)) = y (e (some b))) : x = y := by
  funext i
  obtain ⟨i, rfl⟩ := e.surjective i
  rcases i with _ | b
  · exact h0
  · exact h1 b

theorem isPerpEmb_base (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (he : SignCompat e)
    (j₀ : UpqT P' Q' → UpqT P Q) (hj : IsBlockEmb e j₀) :
    IsPerpEmb (baseVec e) (incl e) j₀ := by
  refine ⟨fun u v => ?_, fun y => ?_, fun g => ⟨?_, fun u => ?_⟩⟩
  · rw [herm_eq_sum, herm_eq_sum, ← e.sum_comp, Fintype.sum_option]
    simp only [incl_none, incl_some, he _, zero_mul, mul_zero, zero_add]
  · have h1 : herm y (baseVec e) = (sg (e none) : ℂ) * y (e none) := by
      rw [herm_eq_sum, ← e.sum_comp, Fintype.sum_option]
      simp [baseVec]
    have h2 : (sg (e none) : ℂ) ≠ 0 := by exact_mod_cast sg_ne_zero _
    rw [h1, mul_eq_zero, or_iff_right h2]
    constructor
    · intro h
      exact ⟨fun b => y (e (some b)), ext_coord e (by rw [incl_none, h]) fun b => incl_some e _ b⟩
    · rintro ⟨u, rfl⟩
      exact incl_none e u
  · obtain ⟨h1, -, h3, -⟩ := hj g
    refine ext_coord e ?_ fun b => ?_
    · simp [act, baseVec, h1]
    · simp [act, baseVec, h3]
  · obtain ⟨-, h2, -, h4⟩ := hj g
    have key : ∀ i, act (j₀ g) (incl e *ᵥ u) i =
        ∑ b, UpqT.mat (j₀ g) i (e (some b)) * u b := fun i => by
      change ∑ k, UpqT.mat (j₀ g) i k * (incl e *ᵥ u) k = _
      rw [← e.sum_comp, Fintype.sum_option]
      simp only [incl_none, incl_some, mul_zero, zero_add]
    refine ext_coord e ?_ fun b => ?_
    · rw [key, incl_none]; simp [h2]
    · rw [key, incl_some]; simp only [h4]; rfl

theorem isPerpEmb_translate {x₀ : Sp P Q} {A : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ}
    {j : UpqT P' Q' → UpqT P Q} (h : IsPerpEmb x₀ A j) (g₀ : UpqT P Q) :
    IsPerpEmb (act g₀ x₀) (UpqT.mat g₀ * A) (fun g => g₀ * j g * g₀⁻¹) := by
  have hA : ∀ u, (UpqT.mat g₀ * A) *ᵥ u = act g₀ (A *ᵥ u) := fun u => by
    rw [act, Matrix.mulVec_mulVec]
  refine ⟨fun u v => ?_, fun y => ?_, fun g => ⟨?_, fun u => ?_⟩⟩
  · rw [hA, hA, herm_act, h.1]
  · rw [← act_act_inv g₀ y, herm_act, h.2.1]
    refine exists_congr fun u => ?_
    rw [hA]
    constructor
    · intro hu; rw [hu]
    · intro hu; rw [← act_inv_act g₀ (A *ᵥ u), hu, act_inv_act]
  · simp only [act_mul, act_inv_act, (h.2.2 g).1]
  · simp only [hA, act_mul, act_inv_act, (h.2.2 g).2]

theorem exists_isPerpEmb : ∀ (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)),
    SignCompat e → ∀ j₀ : UpqT P' Q' → UpqT P Q, IsBlockEmb e j₀ → ∀ g₀ : UpqT P Q,
    ∃ A : Matrix (Fin P ⊕ Fin Q) (Fin P' ⊕ Fin Q') ℂ,
      IsPerpEmb (act g₀ (baseVec e)) A (fun g => g₀ * j₀ g * g₀⁻¹) :=
  fun _ _ _ _ e he j₀ hj g₀ => ⟨_, isPerpEmb_translate (isPerpEmb_base e he j₀ hj) g₀⟩

end GlobalTheory.PerpFrameTranslate
