import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Tpr
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CochainInv

theorem continuous_multilinear {ι : Type} [Fintype ι] {V G : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup G] [NormedSpace ℝ G] (f : MultilinearMap ℝ (fun _ : ι => V) G) :
    Continuous f := by
  classical
  let b := Module.finBasis ℝ V
  have h : ∀ x : ι → V, f x = ∑ r : ι → Fin (Module.finrank ℝ V), (∏ i, b.coord (r i) (x i)) • f (fun i => b (r i)) := by
    intro x
    conv_lhs => rw [show x = fun i => ∑ j, b.coord j (x i) • b j from funext fun i => (b.sum_repr (x i)).symm]
    rw [MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← MultilinearMap.map_smul_univ]
  rw [show (f : (ι → V) → G) = fun x => ∑ r : ι → Fin (Module.finrank ℝ V), (∏ i, b.coord (r i) (x i)) • f (fun i => b (r i))
    from funext h]
  refine continuous_finsetSum _ fun r _ => (continuous_finsetProd _ fun i _ => ?_).smul continuous_const
  exact ((b.coord (r i)).continuous_of_finiteDimensional).comp (continuous_apply i)

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def hermPart : Lie E a →ₗ[ℝ] Herm E a where
  toFun X := (2⁻¹ : ℝ) • ⟨Matrix.of X + star (Matrix.of X), IsSelfAdjoint.add_star_self _⟩
  map_add' X Y := by
    rw [← smul_add]; congr 1; ext1
    simp only [Submodule.coe_add, ← Matrix.of_add_of, star_add]; abel
  map_smul' c X := by
    rw [RingHom.id_apply, smul_comm]; congr 1; ext1
    simp only [SetLike.val_smul, ← Matrix.smul_of, star_smul, star_trivial, smul_add]

theorem hermPart_toL (X : Herm E a) : hermPart (toL X.1) = X := by
  ext1
  have h : star X.1 = X.1 := X.2.star_eq
  change (2⁻¹ : ℝ) • (Matrix.of (toL X.1) + star (Matrix.of (toL X.1))) = X.1
  rw [show Matrix.of (toL X.1) = X.1 from Matrix.of.apply_symm_apply _, h, ← two_smul ℝ, smul_smul,
    inv_mul_cancel₀ two_ne_zero, one_smul]

end GlobalTheory.CochainInv

namespace GlobalTheory.CochainInv

open GlobalTheory.GKCoh in

theorem lie_apply_eq_sum : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M) (S : Set (Module.Dual ℂ M)) (c : ℝ → Kinf E a) (Z : Matrix (Fin a) (Fin a) (Cinf E)), star Z = -Z → c 0 = 1 → HasDerivAt (fun t => toL (c t).1) (toL Z) 0 → (∀ m, (∀ l ∈ S, l m = 0) → m = 0) → (∀ l ∈ S, ∀ m, HasDerivAt (fun t => l (κ (c t) m)) (l (L (toL Z) m)) 0) → ∀ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M), IsCochain κ ω → ∀ Y W : Fin q → Herm E a, (∀ i, (W i).1 = Z * (Y i).1 - (Y i).1 * Z) → L (toL Z) (ω Y) = ∑ i, ω (Function.update Y i (W i)) := by
  intro E _ _ a M _ _ _ _ κ L S c Z hZ hc0 hc hS hκ q ω hω Y W hW
  classical
  have hE : ∀ r m, HasDerivAt (fun t => (c t).1 r m) (Z r m) 0 := fun r m => hasDerivAt_pi.1 (hasDerivAt_pi.1 hc r) m
  let u : ℝ → Fin q → Lie E a := fun t i => toL ((c t).1 * (Y i).1 * star (c t).1)
  have hu : HasDerivAt u (fun i => toL (W i).1) 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun r => hasDerivAt_pi.2 fun s => ?_
    have key : HasDerivAt (fun t => ((c t).1 * (Y i).1 * star (c t).1) r s)
        ((Z * (Y i).1 * star (c 0).1 + (c 0).1 * (Y i).1 * star Z) r s) 0 := by
      simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
      refine HasDerivAt.fun_sum fun k _ => ?_
      have h1 : HasDerivAt (fun t => ∑ m, (c t).1 r m * (Y i).1 m k) (∑ m, Z r m * (Y i).1 m k) 0 :=
        HasDerivAt.fun_sum fun m _ => (hE r m).mul_const _
      exact h1.mul (hE s k).star
    have e : Z * (Y i).1 * star (c 0).1 + (c 0).1 * (Y i).1 * star Z = (W i).1 := by
      rw [hW, hc0, hZ]; simp [sub_eq_add_neg]
    rw [e] at key
    exact key
  refine sub_eq_zero.1 (hS _ fun l hl => ?_)
  rw [map_sub, sub_eq_zero]
  let f : MultilinearMap ℝ (fun _ : Fin q => Lie E a) ℂ :=
    (l.restrictScalars ℝ).compMultilinearMap (ω.toMultilinearMap.compLinearMap fun _ => hermPart)
  let F : ContinuousMultilinearMap ℝ (fun _ : Fin q => Lie E a) ℂ := ⟨f, continuous_multilinear f⟩
  have hF : ∀ x, F x = l (ω (fun i => hermPart (x i))) := fun x => rfl
  have h1 := (F.hasFDerivAt (u 0)).comp_hasDerivAt (0 : ℝ) hu
  have h2 : (F ∘ u) = fun t => l (κ (c t) (ω Y)) := by
    funext t
    rw [Function.comp_apply, hF, ← hω (c t) Y]
    congr 2
    funext i
    exact hermPart_toL (adHerm (c t) (Y i))
  rw [h2, ContinuousMultilinearMap.linearDeriv_apply] at h1
  rw [(hκ l hl (ω Y)).unique h1, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hF]
  congr 2
  funext j
  rcases eq_or_ne j i with rfl | hj
  · simp [hermPart_toL]
  · rw [Function.update_of_ne hj, Function.update_of_ne hj]
    change hermPart (toL ((c 0).1 * (Y j).1 * star (c 0).1)) = Y j
    simp [hc0, hermPart_toL]

end GlobalTheory.CochainInv

end
