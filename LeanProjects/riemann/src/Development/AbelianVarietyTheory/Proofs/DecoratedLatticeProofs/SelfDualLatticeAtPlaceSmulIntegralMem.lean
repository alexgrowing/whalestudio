import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingPreservesSupportedUnitarySubgro
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix

namespace GlobalTheory.IwaPlace.SDStable

variable {D : D7}

theorem hermAt_smul_left (S : HSp D) (a : AE D) (y x : Fin S.rank → AE D) :
    hermAt S (a • y) x = a * hermAt S y x := by
  unfold hermAt
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem mul_mem_intAt {v : Pl D} {a b : AE D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_left _ _ hb.1, by rw [RingHom.map_mul]; exact FrameLat.mul_mem_intAE ha.2 hb.2⟩

theorem smul_mem : ∀ (D : D7) (S : HSp D) (v : Pl D) (Λ : AddSubgroup (Fin S.rank → AE D)), IsSDAt S v Λ →
    ∀ a ∈ intAt D (· = v), ∀ y ∈ Λ, a • y ∈ Λ := by
  intro D S v Λ hΛ a ha y hy
  have hsupp : ∀ i, (a • y) i ∈ idAt D (· = v) := fun i => by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_left _ _ (hΛ.1 y hy i)
  refine (hΛ.2.2 (a • y) hsupp).2 fun x hx => ?_
  rw [hermAt_smul_left]
  exact mul_mem_intAt ha ((hΛ.2.2 y (hΛ.1 y hy)).1 hy x hx)

end GlobalTheory.IwaPlace.SDStable

end
