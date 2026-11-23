import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

def PtsIntegralZeroLowerNE.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [Nonempty K] (ι : K → Type) [∀ k, Fintype (ι k)] (W : Ideal (MRing ι))
    (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ),
    IsMultiHomogIdeal W → Finite (McClasses W) →
    (∀ (u : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, u k ≠ 0) → z ∈ mcPts W →
      g (fun p => u p.1 * z p) = g z) →
    (∀ z ∈ mcPts W, c ≤ g z) →
    c * degC W ≤ ptsIntegral (e := 0) W φ g

theorem anchor_minor {R : Type*} [CommRing R] (j m : ℕ) (Z : Matrix (Fin j) (Fin m) R) :
    (colsOf (onePipe Z) (plAnchor j m)).det = 1 := by
  have he : (plAnchor j m).1.orderEmbOfFin (plAnchor j m).2 = Fin.castLEOrderEmb (Nat.le_add_right j m) := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro x
    simp only [plAnchor, Finset.mem_map, Finset.mem_univ, true_and]
    exact ⟨x, rfl⟩
  have : colsOf (onePipe Z) (plAnchor j m) = 1 := by
    ext a b
    simp only [colsOf, Matrix.submatrix_apply, id, he, onePipe, Matrix.of_apply]
    have : (Fin.castLEOrderEmb (Nat.le_add_right j m)) b = Fin.castAdd m b := rfl
    rw [this, Fin.append_left]
  rw [this, Matrix.det_one]

theorem rootCoord_mem {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) :
    rootCoord ζ ∈ mcPts (rootPointIdeal ζ) := by
  refine ⟨fun k => ⟨plAnchor j m, ?_⟩, fun g hg => ?_⟩
  · simp [rootCoord, anchor_minor]
  · have h : mConeMap (rootCoord ζ) g = 0 := hg
    have h2 := congrArg (MvPolynomial.eval (fun _ : Fin f => (1 : ℂ))) h
    have key : (MvPolynomial.eval (fun _ : Fin f => (1 : ℂ))).comp
        (mConeMap (rootCoord ζ) : MRing (plBlocks f j m) →+* MvPolynomial (Fin f) ℂ) =
        (eval (rootCoord ζ)).comp (map (Int.castRingHom ℂ)) := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp
      · intro i; simp [mConeMap]
    have := congrArg (fun φ => φ g) key
    simp only [RingHom.comp_apply, RingHom.coe_coe, h, map_zero] at this
    exact this.symm

example : IsMultiHomogIdeal (⊥ : Ideal (MRing (fun _ : Unit => Unit))) :=
  ⟨∅, by simp, by simp⟩

theorem finite_mcClasses_bot_unit : Finite (McClasses (⊥ : Ideal (MRing (fun _ : Unit => Unit)))) := by
  haveI : Subsingleton (McClasses (⊥ : Ideal (MRing (fun _ : Unit => Unit)))) := by
    constructor
    intro x y
    induction x using Quot.ind with | mk z => ?_
    induction y using Quot.ind with | mk z' => ?_
    apply Quot.sound
    obtain ⟨⟨⟩, hz⟩ := z.2.1 ()
    obtain ⟨⟨⟩, hz'⟩ := z'.2.1 ()
    refine ⟨fun _ => z'.1 ⟨(), ()⟩ / z.1 ⟨(), ()⟩, fun _ => div_ne_zero hz' hz, ?_⟩
    funext p
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    field_simp
  exact Finite.of_subsingleton

end

end GroundTheory.Heights₂.Heights
