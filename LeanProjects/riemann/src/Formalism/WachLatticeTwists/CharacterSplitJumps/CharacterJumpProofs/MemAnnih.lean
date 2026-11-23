import Formalism.WachLatticeTwists.CharacterSplitJumps.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JT

open Formalism.NG

theorem transport {ℓ : ℕ} [Fact ℓ.Prime] (O : Type) [CommRing O] {X : Type} [AddCommGroup X]
    [Module O X] {Y : Type} [AddCommGroup Y] [Module ℤ_[ℓ] Y] (b : Y →+ X) (c : ℕ) (y : Y) :
    b (((ℓ : ℤ_[ℓ]) ^ c) • y) = ((ℓ : O) ^ c) • b y := by
  rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]

theorem mem_annih {O Cw Cs P : Type*} [CommRing O] [AddCommGroup Cw] [Module O Cw]
    [AddCommGroup Cs] [Module O Cs] [AddCommGroup P] [Module O P] (pr : Cw →ₗ[O] Cs →ₗ[O] P)
    (U : Submodule O Cs) (x : Cw) : x ∈ annih pr U ↔ ∀ t ∈ U, pr x t = 0 := by
  simp only [annih, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]

end Formalism.RepresentationBoundsCohomology.JT
