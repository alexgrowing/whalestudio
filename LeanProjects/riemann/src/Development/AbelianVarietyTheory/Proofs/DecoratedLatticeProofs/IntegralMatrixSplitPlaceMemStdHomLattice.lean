import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalSelfDualLatticeSplitPlaceDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceIdempotentMulIdemSumEqZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSplitPlaceHermitianFrameGLEmbedding
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardLatticeHomCompletionStableSplitIdempoten
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitUpStd

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sec_mul' (q : GlobalTheory.FinPl.SplitPt D k) (a : k) (b : AE D) : q.sec a * b = q.sec (a * q.pr b) := by
  have h1 : q.e * q.sec a = q.sec a := by rw [← q.sec_pr, q.pr_sec]
  calc q.sec a * b = q.e * (q.sec a * b) := by rw [← mul_assoc, h1]
    _ = q.sec (q.pr (q.sec a * b)) := (q.sec_pr _).symm
    _ = q.sec (a * q.pr b) := by rw [map_mul, q.pr_sec]

set_option maxHeartbeats 800000 in
theorem int_up_mem_stdHom : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D) (a₀ : D.host.E), a₀ ∈ (D.host.AA : Set D.host.E) → q.pr (incA D a₀) ≠ 0 → ∀ (FS : Frame k S.rank (Fin S.rank)) (FT : Frame k T.rank (Fin T.rank)), FT.β = 1 → FT.γ = 1 → FS.γ = q.pr (incA D a₀) • (HSpace.gram S).map (fun a => q.pr (incA D a)) → ∀ t : Matrix (Fin T.rank) (Fin S.rank) k, (∀ r s, t r s ∈ 𝒪[k]) → (Place.ofSplitPt q).up FS FT t ∈ stdHom S T := by
  intro D k _ _ _ _ q S T a₀ ha₀ _ FS FT hβ _ hγ t ht
  obtain ⟨ε, ⟨α, rfl, h1, h0⟩, hsum⟩ := q.above
  have hα : α ∈ intAf D.host.F := fun u => by
    by_cases hu : u = q.v
    · subst hu; rw [h1]; exact one_mem _
    · rw [h0 u hu]; exact zero_mem _
  have hee : q.e * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) = q.e := by
    rw [← hsum, mul_add, q.split.1, q.split.2.1, add_zero]

  let G : Fin T.rank → Fin S.rank → WO S T := fun i l =>
    Matrix.of fun i' j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
      (a₀ * (Pi.single i (1 : D.host.E) : Fin T.rank → D.host.E) i' *
        ∑ m, star ((Pi.single l (1 : D.host.E) : Fin S.rank → D.host.E) m) * S.gram m j)
  have hsingle : ∀ (n : ℕ) (l : Fin n), (Pi.single l (1 : D.host.E) : Fin n → D.host.E) ∈ intVecSub D n := by
    intro n l m
    by_cases hm : m = l
    · subst hm; rw [Pi.single_eq_same]; exact isIntegral_one
    · rw [Pi.single_eq_of_ne hm]; exact isIntegral_zero
  have hG : ∀ i l, G i l ∈ stdHom S T := fun i l =>
    Formalism.IndefR.Fin.gen_mem S T (intVecSub D S.rank) (intVecSub D T.rank) hα ha₀ (hsingle _ l) (hsingle _ i)
  have htm : ∀ (x : k) (y : D.host.E), q.sec x * (pairA D.host.F 0 α ⊗ₜ[D.host.F] y) = q.sec (x * q.pr (incA D y)) := by
    intro x y
    have e1 : pairA D.host.F 0 α ⊗ₜ[D.host.F] y = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * incA D y := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      change _ = (_ ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] y)
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    have h2 : q.e * q.sec x = q.sec x := by rw [← q.sec_pr, q.pr_sec]
    rw [e1, ← mul_assoc, ← h2, mul_assoc q.e, mul_comm (q.sec x), ← mul_assoc q.e, hee, h2, sec_mul']
  have hrow : ∀ (l : Fin S.rank) j,
      ∑ m, star ((Pi.single l (1 : D.host.E) : Fin S.rank → D.host.E) m) * S.gram m j = S.gram l j := by
    intro l j
    rw [Finset.sum_eq_single l]
    · rw [Pi.single_eq_same, star_one, one_mul]
    · intro m _ hm; rw [Pi.single_eq_of_ne hm, star_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ l) h
  have hGapp : ∀ i l i' j, (q.sec (t i l) • G i l) i' j = q.sec (t i l) * (pairA D.host.F 0 α ⊗ₜ[D.host.F]
      (a₀ * (Pi.single i (1 : D.host.E) : Fin T.rank → D.host.E) i' *
        ∑ m, star ((Pi.single l (1 : D.host.E) : Fin S.rank → D.host.E) m) * S.gram m j)) := fun _ _ _ _ => rfl
  have key : (Place.ofSplitPt q).up FS FT t = ∑ i, ∑ l, q.sec (t i l) • G i l := by
    ext i' j
    change q.sec ((FT.β * t * FS.γ) i' j) = _
    rw [hβ, hγ, Matrix.one_mul, Matrix.sum_apply, Finset.sum_eq_single i']
    · rw [Matrix.sum_apply, Matrix.mul_apply, map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hGapp, htm, hrow, Pi.single_eq_same, mul_one, map_mul (incA D), map_mul q.pr, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    · intro i _ hi
      rw [Matrix.sum_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [hGapp, Pi.single_eq_of_ne (Ne.symm hi), mul_zero, zero_mul, TensorProduct.tmul_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ i') h
  rw [key]
  refine sum_mem fun i _ => sum_mem fun l _ => ?_
  exact Formalism.IndefR.Fin.latO_smul_mem S T (intVecSub D S.rank) (intVecSub D T.rank) ((q.int_iff _).1 (ht i l)) (hG i l)

end GlobalTheory.SplitUpStd
