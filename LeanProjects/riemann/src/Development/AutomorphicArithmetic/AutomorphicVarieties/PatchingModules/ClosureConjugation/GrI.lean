import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UnitsBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UnitsOneBlock

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.gr_I :
    ∀ {B E F : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field F] [Algebra B F] {n : ℕ} (T : TrInv B E) (r : E →ₐ[B] Matrix (Fin n) (Fin n) F) (U : T.Units (Fin n) (oB n n)), 1 ≤ n → (∀ y, r (T.st y) = (r y)ᵀ) → (∀ i, r (U.x i) = single (oB n n i) i 1) → Nonempty (GrAlg T n n r U.ep) := by
  intro B E F _ _ _ _ _ _ n T r U hn hr hx
  have ho : ∀ i : Fin n, oB n n i = ⟨0, by omega⟩ := fun i => Fin.ext (by simp [oB, i.isLt])
  obtain ⟨φ, hφ, hst, -⟩ := units_one_block T (oB n n) U ⟨0, by omega⟩ ho
  have hU := units_basic T (oB n n) U
  have hxe : ∀ i' i : Fin n, U.x i' * U.ep i = if i' = i then U.x i' else 0 := by
    intro i' i
    conv_lhs => rw [← U.x_mem i']
    split_ifs with h
    · subst h
      rw [mul_assoc, (U.coi.idem i').eq, U.x_mem]
    · rw [mul_assoc, U.coi.ortho h, mul_zero]
  have hone : (1 : Submodule B B) = ⊤ :=
    eq_top_iff.2 fun x _ => Submodule.mem_one.2 ⟨x, rfl⟩
  refine ⟨@GrAlg.mk B E F _ _ _ _ _ _ T n n r U.ep B _ _ inferInstance (fun a b h => h) ⊥
    ?_ ?_ (fun _ => rfl) φ.toAlgHom φ.injective ?_ hst ?_ ?_⟩
  · rw [hone]
    exact isCompl_top_bot
  · intro y hy z hz
    rw [Submodule.mem_bot] at hy
    subst hy
    exact ⟨0, zero_mem _, by simp⟩
  · intro Y
    constructor
    · intro _
      intro i j
      refine ⟨fun _ => by rw [hone]; trivial, fun h => absurd ⟨fun _ => j.isLt, fun _ => i.isLt⟩ h⟩
    · intro _
      exact φ.surjective Y
  · intro i
    show φ (U.ep i) = _
    ext i' j'
    rw [hφ, hxe]
    split_ifs with h1
    · subst h1
      by_cases h2 : i' = j'
      · subst h2
        rw [U.x_st, U.tr_ep]
        simp [Matrix.single_apply]
      · rw [hU.1 i' j' h2, map_zero]
        simp [Matrix.single_apply, h2, Ne.symm h2]
    · simp [Matrix.single_apply, Ne.symm h1]
  · intro y i j b h
    rw [Submodule.mem_bot, sub_eq_zero] at h
    change φ y i j = b at h
    rw [← h, hφ]
    have he0 : r (U.ep ⟨0, by omega⟩) = single ⟨0, by omega⟩ ⟨0, by omega⟩ 1 := by
      have h0 := U.x_base ⟨0, by omega⟩
      rw [ho] at h0
      rw [← h0, hx, ho]
    have hk := hU.2.2.2.2.1 i j y (by rw [ho, ho])
    have hr2 := congrArg (fun M => M ⟨0, by omega⟩ ⟨0, by omega⟩) (congrArg r hk)
    simp only [map_mul, map_smul, hr, hx, ho, he0] at hr2
    simp [Matrix.mul_apply, Matrix.single_apply, Algebra.smul_def] at hr2
    rw [hr2]
