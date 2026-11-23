import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
open IsLocalRing GlobalTheory.Henselisation

namespace GlobalTheory.Henselisation

theorem EtNbhd.exists_sub_mem_maximalIdeal :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (i : EtNbhd R) (b : i.B),
      ∃ r : R, b - algebraMap R i.B r ∈ maximalIdeal i.B := by
  intro R _ _ i b
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective i.q.primeCompl b
  obtain ⟨r₁, hr₁⟩ := residue_surjective (i.pt a)
  obtain ⟨r₂, hr₂⟩ := residue_surjective (i.pt (s : i.A))
  have hs : i.pt (s : i.A) ≠ 0 := by
    intro h
    exact s.2 (show (s : i.A) ∈ RingHom.ker i.pt from h)
  have hu : IsUnit r₂ := by
    by_contra hn
    apply hs
    rw [← hr₂]
    exact (residue_eq_zero_iff r₂).2 hn
  obtain ⟨u, rfl⟩ := hu
  refine ⟨r₁ * ((u⁻¹ : Rˣ) : R), ?_⟩
  have key : IsLocalization.mk' i.B a s - algebraMap R i.B (r₁ * ((u⁻¹ : Rˣ) : R)) =
      IsLocalization.mk' i.B (a - (s : i.A) * algebraMap R i.A (r₁ * ((u⁻¹ : Rˣ) : R))) s := by
    rw [IsLocalization.eq_mk'_iff_mul_eq, sub_mul, IsLocalization.mk'_spec, map_sub]
    simp only [map_mul, ← IsScalarTower.algebraMap_apply R i.A i.B]
    ring
  rw [key, IsLocalization.AtPrime.mk'_mem_maximal_iff (S := i.B) (I := i.q)]
  show _ ∈ RingHom.ker i.pt
  rw [RingHom.mem_ker, map_sub, map_mul, AlgHom.commutes, ← hr₁, ← hr₂]
  rw [show algebraMap R (ResidueField R) = residue R from rfl, ← map_mul, ← map_sub]
  rw [residue_eq_zero_iff]
  have : r₁ - (u : R) * (r₁ * ((u⁻¹ : Rˣ) : R)) = 0 := by
    rw [mul_left_comm, Units.mul_inv, mul_one, sub_self]
  rw [this]
  exact zero_mem _

end GlobalTheory.Henselisation
