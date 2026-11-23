import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.SingleMemDualLatticeStandard
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1 NumberField MvPolynomial

noncomputable section

def OneBlockPointDeg.Statement : Prop :=
  ∀ (Φ Φ' : Type) [Field Φ] [Field Φ'] [Algebra Φ Φ'] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (k₀ : K), (∀ k, k = k₀) →
    ∀ (w : (Σ k, ι k) → Φ') (c : ∀ k, ι k), w ⟨k₀, c k₀⟩ ≠ 0 →
      Module.Finite Φ (Algebra.adjoin Φ (Set.range fun p => w p / w ⟨k₀, c k₀⟩)) →
      Transcendental (Algebra.adjoin Φ (Set.range fun p => w p / w ⟨k₀, c k₀⟩)) (w ⟨k₀, c k₀⟩) →
      IsProjVarF (RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')) 0 ∧
        IsChart (RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')) c ∧
        ptDeg (RingHom.ker (aeval w : MRingOver Φ ι →ₐ[Φ] Φ')) c =
          Module.finrank Φ (Algebra.adjoin Φ (Set.range fun p => w p / w ⟨k₀, c k₀⟩))

def DualStdFibreRatios.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (T : Type) [Fintype T] [DecidableEq T]
    (b : Module.Basis T ℤ (dualLattice (HermLattice.standard K i)))
    (G : GenFibre (inrV (ι := dualBlocks T) (ι₂ := PBlk i))
      (graphIdeal (dualIdeal b) (linForm (ι₂ := PBlk i) (dualStdCoordMat b)))),
    1 ≤ i → ∃ c : T,
      G.x' (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) ≠ 0 ∧
      Module.finrank G.Φ (Algebra.adjoin G.Φ (Set.range fun t : T =>
        G.x' (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) /
          G.x' (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))) = Module.finrank ℚ K ∧
      Transcendental (Algebra.adjoin G.Φ (Set.range fun t : T =>
        G.x' (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) /
          G.x' (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)))
        (G.x' (⟨Sum.inl (), c⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k))

example : ∃ (w : (Σ _ : Unit, Unit) → RatFunc ℚ) (c : ∀ _ : Unit, Unit), w ⟨(), c ()⟩ ≠ 0 ∧
    Module.Finite ℚ (Algebra.adjoin ℚ (Set.range fun p => w p / w ⟨(), c ()⟩)) ∧
    Transcendental (Algebra.adjoin ℚ (Set.range fun p => w p / w ⟨(), c ()⟩)) (w ⟨(), c ()⟩) := by
  have hX : (RatFunc.X : RatFunc ℚ) ≠ 0 := RatFunc.X_ne_zero
  have hb : Algebra.adjoin ℚ (Set.range fun _ : (Σ _ : Unit, Unit) => (RatFunc.X : RatFunc ℚ) / RatFunc.X) = ⊥ := by
    have hr : (Set.range fun _ : (Σ _ : Unit, Unit) => (RatFunc.X : RatFunc ℚ) / RatFunc.X) = {1} := by
      ext y
      simp [div_self hX]
    rw [hr, Algebra.adjoin_singleton_one]
  refine ⟨fun _ => RatFunc.X, fun _ => (), hX, ?_, ?_⟩
  · beta_reduce
    rw [hb]
    exact Subalgebra.finite_bot
  · beta_reduce
    rw [hb]
    intro H
    have : Algebra.IsAlgebraic ℚ (⊥ : Subalgebra ℚ (RatFunc ℚ)) := Algebra.IsAlgebraic.of_finite ℚ _
    exact RatFunc.transcendental_X (K := ℚ) (by convert H.restrictScalars (R := ℚ); exact Subsingleton.elim _ _)

example : ∃ _ : Module.Basis Unit ℤ (dualLattice (HermLattice.standard ℚ 1)), 1 ≤ 1 :=
  ⟨dualBasisStandard, le_rfl⟩

end

end GroundTheory.Heights₂.Heights
