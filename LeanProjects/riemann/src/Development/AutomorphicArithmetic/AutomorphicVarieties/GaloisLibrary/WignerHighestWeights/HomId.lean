import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.homId :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (L : Lie E a →ₗ[ℝ] Module.End ℂ M) (q : ℕ) (ω : Herm E a [⋀^Fin (q + 1)]→ₗ[ℝ] M),
      dCo L ω = 0 → InfEq L ω → ∀ (X : Matrix (Fin a) (Fin a) (Cinf E)) (Y : Fin (q + 1) → Herm E a),
        ∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • (L (toL (Y i).1) (ω (Matrix.vecCons (hp (toL X)) (i.removeNth Y))) -
          ω (Matrix.vecCons (hp (toL ((Y i).1 * X - X * (Y i).1))) (i.removeNth Y))) = L (toL X) (ω Y) := by
  intro E _ _ _ a M _ _ _ _ L q ω hd hinf X Y
  let Z : Matrix (Fin a) (Fin a) (Cinf E) := (1 / 2 : ℝ) • (X - star X)
  have hZ : star Z = -Z := by
    simp only [Z]
    rw [star_smul, star_sub, star_star, star_trivial, ← smul_neg, neg_sub]
  have hX : toL X = toL (hp (toL X)).1 + toL Z := by
    have h : X = (hp (toL X)).1 + Z := by
      rw [hp_val]; simp only [Z]; module
    exact congrArg toL h
  have hb : ∀ U : Herm E a, hp (toL (U.1 * X - X * U.1)) = -brH Z hZ U := by
    intro U
    apply Subtype.ext
    have h : star U.1 = U.1 := U.2
    rw [hp_val]
    change _ = -(Z * U.1 - U.1 * Z)
    simp only [Z, star_sub, star_mul, h, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub]
    module
  have h1 := dCo_cons (L := L) ω (hp (toL X)) Y
  rw [hd, AlternatingMap.zero_apply, eq_comm, sub_eq_zero, dCo_apply] at h1
  rw [congrArg L hX, map_add, LinearMap.add_apply, h1, hinf Z hZ Y, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : ω (Matrix.vecCons (-brH Z hZ (Y i)) (i.removeNth Y)) =
      -ω (Matrix.vecCons (brH Z hZ (Y i)) (i.removeNth Y)) := by
    rw [← AlternatingMap.curryLeft_apply_apply, ← AlternatingMap.curryLeft_apply_apply, map_neg,
      AlternatingMap.neg_apply]
  rw [hb, h2, sub_neg_eq_add, smul_add, ← Fin.insertNth_removeNth, AlternatingMap.map_insertNth,
    AlternatingMap.curryLeft_apply_apply]
