import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

noncomputable section

namespace UpperTheory.V.Cj.H

private theorem multi_cont {H : Type} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [ContinuousSMul ℝ H] [T2Space H] [FiniteDimensional ℝ H] {q : ℕ} (f : MultilinearMap ℝ (fun _ : Fin q => H) ℂ) :
    Continuous f := by
  classical
  let b := Module.finBasis ℝ H
  have h : (f : (Fin q → H) → ℂ) = fun x => ∑ r : Fin q → Fin (Module.finrank ℝ H),
      (∏ i, b.coord (r i) (x i)) • f fun i => b (r i) := by
    funext x
    have e : x = fun i => ∑ j, b.coord j (x i) • b j := funext fun i => (b.sum_repr (x i)).symm
    conv_lhs => rw [e]
    rw [f.map_sum]
    exact Finset.sum_congr rfl fun r _ => f.map_smul_univ _ _
  rw [h]
  refine continuous_finset_sum _ fun r _ => Continuous.fun_smul (continuous_finset_prod _ fun i _ => ?_) continuous_const
  exact (b.coord (r i)).continuous_of_finiteDimensional.comp (continuous_apply i)

private def contr {S : Type} [AddCommGroup S] [Module ℂ S] {d : ℕ} :
    (Fin d → ℂ) →ₗ[ℂ] S ⊗[ℂ] (Fin d → ℂ) →ₗ[ℂ] S :=
  ∑ i, (LinearMap.proj i : (Fin d → ℂ) →ₗ[ℂ] ℂ).smulRight (Bor.cmp i)

private theorem contr_tmul {S : Type} [AddCommGroup S] [Module ℂ S] {d : ℕ} (v u : Fin d → ℂ) (φ : S) :
    contr v (φ ⊗ₜ[ℂ] u) = (v ⬝ᵥ u) • φ := by
  simp [contr, LinearMap.sum_apply, dotProduct, Finset.sum_smul, smul_smul]

private theorem contr_single {S : Type} [AddCommGroup S] [Module ℂ S] {d : ℕ} (i : Fin d) (m : S ⊗[ℂ] (Fin d → ℂ)) :
    contr (Pi.single i 1) m = Bor.cmp i m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | tmul φ u => simp [contr_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem abs_type {K H S : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [AddCommGroup H] [Module ℝ H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [ContinuousSMul ℝ H] [T2Space H] [FiniteDimensional ℝ H] [AddCommGroup S] [Module ℂ S] [Module ℝ S] [IsScalarTower ℝ ℂ S]
    {d : ℕ} (q : ℕ) (ad : K →* (H →ₗ[ℝ] H)) (had : ∀ X, Continuous fun k => ad k X)
    (M : K →* Matrix (Fin d) (Fin d) ℂ) (hM : Continuous M) (π : Representation ℂ K S) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
      (ρ : Representation ℂ K W), GlobalTheory.Published.AutFin.IsContRep ρ ∧
      ∀ ω : MultilinearMap ℝ (fun _ : Fin q => H) (S ⊗[ℂ] (Fin d → ℂ)),
        (∀ k X, ω (fun i => ad k (X i)) = TensorProduct.map (π k) (Matrix.toLin' (M k)) (ω X)) → ∀ X i,
      ∃ (T : W →ₗ[ℂ] S) (w : W), (∀ k v, T (ρ k v) = π k (T v)) ∧ T w = Bor.cmp i (ω X) := by
  classical
  let P := PiTensorProduct ℝ fun _ : Fin q => H
  let A : K → P →ₗ[ℝ] P := fun k => PiTensorProduct.map fun _ => ad k
  let B : K → (Fin d → ℂ) →ₗ[ℂ] (Fin d → ℂ) := fun k => Matrix.toLin' (M k⁻¹)ᵀ
  let ρ : Representation ℂ K ((Fin d → ℂ) ⊗[ℝ] P) :=
    { toFun := fun k => TensorProduct.AlgebraTensorModule.map (B k) (A k)
      map_one' := by
        have h1 : A 1 = LinearMap.id := by
          simp only [A, map_one]; exact PiTensorProduct.map_one
        have h2 : B 1 = LinearMap.id := by simp [B]
        rw [h1, h2, TensorProduct.AlgebraTensorModule.map_id]; rfl
      map_mul' := fun k l => by
        have h1 : A (k * l) = A k ∘ₗ A l := by
          simp only [A, map_mul]; exact PiTensorProduct.map_mul _ _
        have h2 : B (k * l) = B k ∘ₗ B l := by simp [B, Matrix.toLin'_mul]
        rw [h1, h2, TensorProduct.AlgebraTensorModule.map_comp]; rfl }
  have hρ : ∀ k v (X : Fin q → H), ρ k (v ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ X) =
      ((M k⁻¹)ᵀ *ᵥ v) ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ fun i => ad k (X i) := fun k v X => by
    change TensorProduct.AlgebraTensorModule.map (B k) (A k) _ = _
    rw [TensorProduct.AlgebraTensorModule.map_tmul]
    exact congrArg₂ _ rfl (PiTensorProduct.map_tprod _ _)
  have ind : ∀ (p : (Fin d → ℂ) ⊗[ℝ] P → Prop) (h0 : p 0) (ha : ∀ x y, p x → p y → p (x + y))
      (ht : ∀ v (X : Fin q → H), p (v ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ X)) (w : (Fin d → ℂ) ⊗[ℝ] P), p w := by
    intro p h0 ha ht w
    induction w using TensorProduct.induction_on with
    | zero => exact h0
    | add x y hx hy => exact ha x y hx hy
    | tmul v t =>
      induction t using PiTensorProduct.induction_on with
      | smul_tprod r X => rw [← TensorProduct.smul_tmul]; exact ht _ _
      | add x y hx hy => rw [TensorProduct.tmul_add]; exact ha _ _ hx hy
  refine ⟨(Fin d → ℂ) ⊗[ℝ] P, inferInstance, inferInstance, Module.Finite.of_restrictScalars_finite ℝ ℂ _, ρ,
    fun ℓ w => ?_, fun ω hω X i => ?_⟩
  · induction w using ind with
    | h0 => simpa using continuous_const
    | ha x y hx hy => simpa only [map_add] using hx.fun_add hy
    | ht v X =>
      have e : (fun k => ℓ (ρ k (v ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ X))) = fun k => ∑ j, ((M k⁻¹)ᵀ *ᵥ v) j *
          ((ℓ.restrictScalars ℝ ∘ₗ TensorProduct.mk ℝ (Fin d → ℂ) P (Pi.single j 1)).compMultilinearMap
            (PiTensorProduct.tprod ℝ)) fun i => ad k (X i) := by
        funext k
        rw [hρ]
        generalize (M k⁻¹)ᵀ *ᵥ v = u
        conv_lhs => rw [pi_eq_sum_univ' u]
        rw [TensorProduct.sum_tmul, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← TensorProduct.smul_tmul', map_smul]
        rfl
      rw [e]
      refine continuous_finset_sum _ fun j _ => Continuous.mul ?_ ?_
      · exact (continuous_apply j).comp ((hM.comp continuous_inv).matrix_transpose.matrix_mulVec continuous_const)
      · exact (multi_cont _).comp (continuous_pi fun i => had _)
  · let T : (Fin d → ℂ) ⊗[ℝ] P →ₗ[ℂ] S := TensorProduct.AlgebraTensorModule.lift
      { toFun := fun v => (contr v).restrictScalars ℝ ∘ₗ PiTensorProduct.lift ω
        map_add' := fun u v => by ext; simp
        map_smul' := fun c v => by ext; simp }
    have hT : ∀ v (Y : Fin q → H), T (v ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ Y) = contr v (ω Y) := fun v Y => by
      exact congrArg (contr v) (PiTensorProduct.lift.tprod (φ := ω) Y)
    refine ⟨T, Pi.single i 1 ⊗ₜ[ℝ] PiTensorProduct.tprod ℝ X, fun k w => ?_, by rw [hT, contr_single]⟩
    induction w using ind with
    | h0 => simp
    | ha x y hx hy => simp only [map_add, hx, hy]
    | ht v Y =>
      rw [hρ, hT, hT, hω]
      induction ω Y using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul φ u =>
        rw [TensorProduct.map_tmul, contr_tmul, contr_tmul, map_smul, Matrix.toLin'_apply, Matrix.mulVec_transpose,
          ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]

end UpperTheory.V.Cj.H

theorem UpperTheory.V.Cj.H.kType :
    UpperTheory.V.Cj.H.KType := by
  intro E _ _ _ a Ξ q
  let ad : Kinf E a →* (Herm E a →ₗ[ℝ] Herm E a) :=
    { toFun := fun k =>
        { toFun := adHerm k
          map_add' := fun X Y => Subtype.ext (by simp [adHerm, mul_add, add_mul])
          map_smul' := fun c X => Subtype.ext (by simp [adHerm]) }
      map_one' := LinearMap.ext fun X => Subtype.ext (by simp [adHerm])
      map_mul' := fun k l => LinearMap.ext fun X => Subtype.ext (by simp [adHerm, mul_assoc]) }
  have had : ∀ X, Continuous fun k => ad k X := fun X =>
    Continuous.subtype_mk ((continuous_subtype_val.mul continuous_const).mul continuous_subtype_val.star) _
  have hM : Continuous (Ξ.mat.comp (Unitary.toUnits : Kinf E a →* _)) := by
    refine continuous_matrix fun i j => continuous_iff_continuousAt.2 fun k => ?_
    have h := (differentiableAt_extGL (Ξ.reg i j) (x := toL (Unitary.toUnits k).val) (Unitary.toUnits k).isUnit).continuousAt
    have h2 : Continuous fun l : Kinf E a => (toL (Unitary.toUnits l).val : Lie E a) := continuous_subtype_val
    have h3 := ContinuousAt.comp (f := fun l : Kinf E a => (toL (Unitary.toUnits l).val : Lie E a)) h h2.continuousAt
    simp only [Function.comp_def, extGL_val] at h3
    exact h3
  obtain ⟨W, i1, i2, i3, ρ, h1, h2⟩ := abs_type q ad had _ hM (cptRep E a)
  exact ⟨W, i1, i2, i3, ρ, h1, fun ω hω => h2 ω.toMultilinearMap hω⟩
