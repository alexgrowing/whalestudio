import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresGrZeroIsCOOfMemMaximalIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.co_B :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∃ h : IsCO O S.B, @maximalIdeal _ _ h.toIsLocalRing = S.mB := by
  intro l _ O _ _ _ _ F C₀ n hF hn S
  obtain ⟨W, hz, -, hB, -, -⟩ := UpperTheory.V.Fr.wpres hF hn S
  haveI h0 : IsCO O (W.gr 0) := UpperTheory.V.Alg.wPres_gr_zero_isCO_of_mem_maximalIdeal O ℤ S.R W hz
  let p : W.gr 0 →ₐ[O] S.B :=
    { toFun := fun b => ⟨((b : W.A) : S.R), (hB _).2 b.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have hp : Function.Surjective p := fun y =>
    ⟨⟨⟨y.1, W.part_le_A ((hB _).1 y.2)⟩, (hB _).1 y.2⟩, rfl⟩
  haveI h : IsCO O S.B := UpperTheory.V.Alg.co_quot O (W.gr 0) S.B p hp
  refine ⟨h, ?_⟩
  ext b
  show _ ↔ S.B.val b ∈ maximalIdeal S.R
  rw [← res_eq_zero_iff O, ← res_eq_zero_iff O, res_map]
