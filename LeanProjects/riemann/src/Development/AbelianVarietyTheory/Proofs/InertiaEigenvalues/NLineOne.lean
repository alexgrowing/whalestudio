import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInhabitants

noncomputable section
namespace GlobalTheory.UnitLemma
open Polynomial IsLocalRing

theorem c_mem (K : UQ) {z : K.E} (hz : z ∈ (algebraMap K.O K.E).range) : K.c z ∈ (algebraMap K.O K.E).range := by
  obtain ⟨x, rfl⟩ := hz
  obtain ⟨y, hy⟩ := K.c_int x
  exact ⟨y, hy.symm⟩

end GlobalTheory.UnitLemma
