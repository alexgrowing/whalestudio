import Mathlib
import GroundTheory.GlobalFields.HerbrandQuotients.UnitsHerbrand

namespace GroundTheory.Global

open NumberField NumberField.Units NumberField.InfinitePlace MulAction Module
open scoped TensorProduct

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem piScalarRight_baseChange_funPermRep {G X : Type*} [Group G] [MulAction G X] [Fintype X]
    [DecidableEq X] (g : G) (y : ℝ ⊗[ℤ] (X → ℤ)) :
    TensorProduct.piScalarRight ℤ ℝ ℝ X ((funPermRep ℤ G X g).baseChange ℝ y) =
      funPermRep ℝ G X g (TensorProduct.piScalarRight ℤ ℝ ℝ X y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r f =>
    funext x
    simp [LinearMap.baseChange_tmul, TensorProduct.piScalarRightHom_tmul, funPermRep_apply]
  | add y z hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]

def logLatticeProdMap : logLattice L × ℤ →ₗ[ℤ] (InfinitePlace L → ℝ) :=
  (logLattice L).subtype.coprod (LinearMap.toSpanSingleton ℤ (InfinitePlace L → ℝ) 1)

omit [NumberField L] in
theorem logLatticeProdMap_apply (m : logLattice L) (n : ℤ) :
    logLatticeProdMap (m, n) = (m : InfinitePlace L → ℝ) + n • (1 : InfinitePlace L → ℝ) :=
  rfl

omit [NumberField K] [NumberField L] in
theorem logLatticeProdMap_comm (g : L ≃ₐ[K] L) (x : logLattice L × ℤ) :
    logLatticeProdMap (((logLatticeRep K L).prod (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) g x) =
      funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g (logLatticeProdMap x) := by
  obtain ⟨m, n⟩ := x
  funext w
  simp [logLatticeProdMap_apply, Representation.prod_apply_apply, coe_logLatticeRep,
    funPermRep_apply]

theorem linearIndependent_logLattice_one {ι : Type*} (b : Basis ι ℤ (logLattice L)) :
    LinearIndependent ℝ (Sum.elim (fun i => (b i : InfinitePlace L → ℝ))
      (fun _ : Unit => (1 : InfinitePlace L → ℝ))) := by
  classical
  refine LinearIndependent.sum_type (linearIndependent_logLattice_basis L b) ?_ ?_
  · rw [linearIndependent_unique_iff]
    exact one_ne_zero
  · let s : (InfinitePlace L → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun y => ∑ w, y w
        map_add' := fun y z => by simp [Finset.sum_add_distrib]
        map_smul' := fun c y => by simp [Finset.mul_sum] }
    have hs : Submodule.span ℝ (Set.range fun i => (b i : InfinitePlace L → ℝ)) ≤
        LinearMap.ker s := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨x, hx⟩ := (b i).2
      change ∑ w, (b i : InfinitePlace L → ℝ) w = 0
      rw [← hx]
      exact sum_fullLog L x
    rw [Submodule.disjoint_def]
    intro y hy1 hy2
    rw [Set.range_const, Submodule.mem_span_singleton] at hy2
    obtain ⟨c, rfl⟩ := hy2
    have h1 : s (c • 1) = 0 := hs hy1
    have h2 : s (c • 1) = c * Fintype.card (InfinitePlace L) := by
      simp [s, Finset.sum_const]
    rw [h2] at h1
    have h3 : (Fintype.card (InfinitePlace L) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    rw [mul_eq_zero, or_iff_left h3] at h1
    rw [h1, zero_smul]

theorem cycHerbrand_logLatticeRep_mul_card {σ : L ≃ₐ[K] L} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (logLatticeRep K L) σ * Fintype.card (L ≃ₐ[K] L) =
      cycHerbrand (funPermRep ℤ (L ≃ₐ[K] L) (InfinitePlace L)) σ := by
  classical
  let bM := Module.Free.chooseBasis ℤ (logLattice L)
  let b := bM.prod (Basis.singleton Unit ℤ)
  let B := Algebra.TensorProduct.basis ℝ b
  let E := (logLatticeProdMap (L := L)).liftBaseChange ℝ
  let v := Sum.elim (fun i => (bM i : InfinitePlace L → ℝ))
    (fun _ : Unit => (1 : InfinitePlace L → ℝ))
  have hEB : ∀ j, E (B j) = v j := by
    intro j
    rw [Algebra.TensorProduct.basis_apply, LinearMap.liftBaseChange_tmul, one_smul]
    rcases j with i | u
    · simp [b, v, Basis.prod_apply, logLatticeProdMap_apply]
    · simp [b, v, Basis.prod_apply, logLatticeProdMap_apply]
  have hli : LinearIndependent ℝ v := linearIndependent_logLattice_one bM
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ (logLattice L) ⊕ Unit) =
      finrank ℝ (InfinitePlace L → ℝ) := by
    rw [Fintype.card_sum, Fintype.card_unit, Module.finrank_fintype_fun_eq_card,
      ← Module.finrank_eq_card_chooseBasisIndex, finrank_logLattice, rank]
    have : 0 < Fintype.card (InfinitePlace L) := Fintype.card_pos
    omega
  have hspan := hli.span_eq_top_of_card_eq_finrank hcard
  have hsurj : Function.Surjective E := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact ⟨B j, hEB j⟩
  have hdim : finrank ℝ (ℝ ⊗[ℤ] (logLattice L × ℤ)) = finrank ℝ (InfinitePlace L → ℝ) := by
    rw [Module.finrank_eq_card_basis B, hcard]
  have hinj : Function.Injective E :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).2 hsurj
  have hbij : Function.Bijective E := ⟨hinj, hsurj⟩
  let P := TensorProduct.piScalarRight ℤ ℝ ℝ (InfinitePlace L)
  let e : ℝ ⊗[ℤ] (logLattice L × ℤ) ≃ₗ[ℝ] ℝ ⊗[ℤ] (InfinitePlace L → ℤ) :=
    (LinearEquiv.ofBijective E hbij).trans P.symm
  have hE : ∀ (g : L ≃ₐ[K] L) y, E ((((logLatticeRep K L).prod
      (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) g).baseChange ℝ y) =
      funPermRep ℝ (L ≃ₐ[K] L) (InfinitePlace L) g (E y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r x =>
      rw [LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, LinearMap.liftBaseChange_tmul,
        map_smul, logLatticeProdMap_comm]
    | add y z hy hz => rw [map_add, map_add, hy, hz, map_add, map_add]
  have he : ∀ (g : L ≃ₐ[K] L) y, e ((((logLatticeRep K L).prod
      (Representation.trivial ℤ (L ≃ₐ[K] L) ℤ)) g).baseChange ℝ y) =
      (funPermRep ℤ (L ≃ₐ[K] L) (InfinitePlace L) g).baseChange ℝ (e y) := by
    intro g y
    apply P.injective
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [piScalarRight_baseChange_funPermRep, LinearEquiv.apply_symm_apply,
      LinearEquiv.ofBijective_apply, LinearEquiv.ofBijective_apply, hE]
  rw [← cycHerbrand_eq_of_real_equiv _ _ σ e he,
    cycHerbrand_prod _ _ σ (hasHerbrandQuotient_cycSubOne_of_finite _ hσ)
      (hasHerbrandQuotient_cycSubOne_of_finite _ hσ), cycHerbrand_trivial_int]

variable [IsGalois K L]

open scoped Classical in

theorem cycHerbrand_unitsRep {σ : L ≃ₐ[K] L} (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    cycHerbrand (unitsRep K L) σ =
      (∏ v : InfinitePlace K, (if v.IsUnramifiedIn L then 1 else 2 : ℚ)) / finrank K L := by
  have h1 := cycHerbrand_logLatticeRep_mul_card hσ
  rw [cycHerbrand_funPermRep hσ, prod_card_stabilizer_infinitePlace] at h1
  have h2 : (Fintype.card (L ≃ₐ[K] L) : ℚ) = finrank K L := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  have h3 : (finrank K L : ℚ) ≠ 0 := by
    exact_mod_cast Module.finrank_pos.ne'
  rw [cycHerbrand_unitsRep_eq_logLattice hσ, eq_div_iff h3, ← h2, h1]

end

end GroundTheory.Global
