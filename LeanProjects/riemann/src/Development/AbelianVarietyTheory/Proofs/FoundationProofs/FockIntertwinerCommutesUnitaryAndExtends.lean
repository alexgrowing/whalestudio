import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompactCoverUnHcModuleFiniteDimIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairKEquivariantOfLieAlgebraCompat
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCoverUpqKsetGeneratedByExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDerivedActionsTensorMembers
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.FockExtGroup

theorem pi_comm {p q r s : ℕ} {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q}
    {T2 : GrpData r s} (F : FockData T0 T1 T2) (g : T1.G) (h : T2.G) (x : F.H) :
    F.π (g, 1) (F.π (1, h) x) = F.π (1, h) (F.π (g, 1) x) := by
  rw [← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← map_mul, ← map_mul]
  simp

theorem comm_and_extend : ∀ (p q n : ℕ) (T0 : GrpData (p * n + q * 0) (p * 0 + q * n)) (T1 : GrpData p q) (T2 : GrpData n 0) (F : FockData T0 T1 T2), 1 ≤ n → ∀ (D : DSRep T1) (τ : URep T2) (M : GKMod n 0) (j : M.V →ₗ[ℂ] τ.H) (I : D.HK.V ⊗[ℂ] M.V →ₗ[ℂ] Pol p q n 0) (v₀ : M.V), IrrU τ → IsHCMod τ M j → v₀ ≠ 0 → IsGIntw F D.HK M I → (∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v₀))) ∧ ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y)) → (∀ (h : T2.G) (x : D.HK.V) (v v' : M.V), j v' = τ.π h (j v) → F.π (1, h) (F.ι (I (x ⊗ₜ v))) = F.ι (I (x ⊗ₜ v'))) ∧ ∀ v : M.V, ∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v))) ∧ ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y) := by
  intro p q n T0 T1 T2 F hn D τ M j I v₀ hτ hM hv₀ hI hJ
  obtain ⟨hfin, -, -, hirr⟩ := GlobalTheory.CompactCoverIrr.hcMod_finite_irr n hn T2 τ M j hτ hM ⟨v₀, 0, hv₀⟩
  obtain ⟨hF, -, hder⟩ := GlobalTheory.FockEmbExp.fock_derived p q n 0 T0 T1 T2 F
  let σ : URep T2 :=
    { H := F.H
      π := F.π.comp (MonoidHom.inr _ _)
      isom := fun _ x => F.isom _ x
      cont := fun x => (F.cont x).comp (hF.comp (continuous_const.prodMk continuous_id)) }
  have h1 : ∀ (h : T2.G) (x : D.HK.V) (v v' : M.V), j v' = τ.π h (j v) →
      F.π (1, h) (F.ι (I (x ⊗ₜ v))) = F.ι (I (x ⊗ₜ v')) := by
    intro h x v v' hv
    have hK : h ∈ T2.Kset := by
      rintro (a | a) (b | b) hab
      · exact (hab trivial).elim
      · exact b.elim0
      · exact a.elim0
      · exact a.elim0
    let j₂ : M.V →ₗ[ℂ] σ.H := F.ι ∘ₗ I ∘ₗ TensorProduct.mk ℂ D.HK.V M.V x
    obtain ⟨w, hw1, hw2⟩ := GlobalTheory.RealPar.pair_kEquivariant_of_lie n 0 T2
      (GlobalTheory.CoverKGen.kset_gen n 0 (by omega) T2) τ σ M.V (fun Y => M.act Y) j j₂
      (fun Y hY _ w => ⟨hM.2.2 Y hY w, by
        have h2 := hder Y hY (I (x ⊗ₜ w))
        have h3 : fockAct2 p q n 0 Y (I (x ⊗ₜ w)) = I (x ⊗ₜ M.act Y w) := hI.2 Y x w
        rw [h3] at h2
        exact h2⟩) h hK v
    obtain rfl : v' = w := hM.1 (hv.trans hw1)
    exact hw2
  refine ⟨h1, ?_⟩
  let N : Submodule ℂ M.V :=
    { carrier := {v | ∃ J : D.U.H →L[ℂ] F.H, (∀ x, J (D.ι x) = F.ι (I (x ⊗ₜ v))) ∧
        ∀ g y, F.π (g, 1) (J y) = J (D.U.π g y)}
      add_mem' := by
        rintro a b ⟨J, hJ1, hJ2⟩ ⟨J', hJ1', hJ2'⟩
        exact ⟨J + J', fun x => by simp [hJ1, hJ1', TensorProduct.tmul_add],
          fun g y => by simp [hJ2, hJ2']⟩
      zero_mem' := ⟨0, fun x => by simp, fun g y => by simp⟩
      smul_mem' := by
        rintro c a ⟨J, hJ1, hJ2⟩
        exact ⟨c • J, fun x => by simp [hJ1, TensorProduct.tmul_smul],
          fun g y => by simp [hJ2]⟩ }
  rcases hirr N (by
    rintro h v ⟨J, hJ1, hJ2⟩ v' hv
    refine ⟨F.π (1, h) ∘L J, fun x => ?_, fun g y => ?_⟩
    · rw [ContinuousLinearMap.comp_apply, hJ1, h1 h x v v' hv]
    · rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, pi_comm, hJ2]) with h | h
  · have : v₀ ∈ N := hJ
    rw [h] at this
    exact (hv₀ this).elim
  · intro v
    have : v ∈ N := h ▸ Submodule.mem_top
    exact this

end GlobalTheory.FockExtGroup
