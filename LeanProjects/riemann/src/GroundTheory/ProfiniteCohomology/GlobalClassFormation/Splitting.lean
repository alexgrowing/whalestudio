import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.ResLocal
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalResConj
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalResKill
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalInvariants
import GroundTheory.GlobalFields.Adele.BaseChange.FiniteMap
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField GroundTheory.Global FiniteSubfield IsDedekindDomain
  GroundTheory.Global.SemiLocal

open scoped DirectSum

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K E : FiniteSubfield} [Fact (K ≤ E)]

section Finite

variable {v : HeightOneSpectrum (𝓞 K.1)}

theorem finiteDimensional_adicCompletion_placesOver (w : PlacesOver E.1 v) :
    FiniteDimensional (v.adicCompletion K.1) (w.1.adicCompletion E.1) :=
  Module.finite_of_finrank_pos (by
    rw [finrank_eq_ramificationIdx_mul_inertiaDeg]
    exact Nat.mul_pos (Ideal.ramificationIdx_pos w.1.asIdeal (𝓞 K.1)) (Ideal.inertiaDeg_pos w.1.asIdeal (𝓞 K.1)))

theorem exists_placeOfEmbedding_eq (w : PlacesOver E.1 v) :
    ∃ ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1), placeOfEmbedding ι E = w := by
  have := finiteDimensional_adicCompletion_placesOver (E := E) w
  let j : w.1.adicCompletion E.1 →ₐ[v.adicCompletion K.1] AlgebraicClosure (v.adicCompletion K.1) :=
    IsAlgClosed.lift
  let j' : E.1 →+* AlgebraicClosure (v.adicCompletion K.1) :=
    j.toRingHom.comp (algebraMap E.1 (w.1.adicCompletion E.1))
  let : Algebra E.1 (AlgebraicClosure (v.adicCompletion K.1)) := j'.toAlgebra
  have hK : ∀ a : K.1, algebraMap E.1 (AlgebraicClosure (v.adicCompletion K.1)) (algebraMap K.1 E.1 a) =
      algebraMap K.1 (AlgebraicClosure (v.adicCompletion K.1)) a := by
    intro a
    change j (algebraMap E.1 (w.1.adicCompletion E.1) (algebraMap K.1 E.1 a)) = _
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K.1 (v.adicCompletion K.1)
      (w.1.adicCompletion E.1), AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  have : IsScalarTower K.1 E.1 (AlgebraicClosure (v.adicCompletion K.1)) :=
    IsScalarTower.of_algebraMap_eq fun a => (hK a).symm
  let ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure (v.adicCompletion K.1) :=
    (nonempty_algHom_of_isSepClosed : Nonempty (ℚ̄ →ₐ[E.1] AlgebraicClosure (v.adicCompletion K.1))).some
  refine ⟨ιE.restrictScalars K.1, (eq_placeOfEmbedding _ E j fun x => ?_).symm⟩
  change j' x = ιE (algebraMap E.1 ℚ̄ x)
  rw [AlgHom.commutes]
  rfl

set_option maxHeartbeats 2000000 in
variable (v) in

theorem exists_unitsLocalRes_unitsResField_eq_zero_of_placeOfEmbedding
    (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1)) (x : cohomology (unitsLimitRep K) 2)
    (hx : Module.finrank (v.adicCompletion K.1) ((placeOfEmbedding ι E).1.adicCompletion E.1) •
      brauerInvZOfIsSepClosure (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))
        ((unitsLocalRes (v.adicCompletion K.1) ι 2).hom x) = 0) :
    ∃ ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure ((placeOfEmbedding ι E).1.adicCompletion E.1),
      (unitsLocalRes ((placeOfEmbedding ι E).1.adicCompletion E.1) ιE 2).hom ((unitsResField K E 2).hom x) = 0 := by
  have := finiteDimensional_adicCompletion_placesOver (E := E) (placeOfEmbedding ι E)
  set Ew := (placeOfEmbedding ι E).1.adicCompletion E.1
  set Kv := v.adicCompletion K.1
  let c := completionEmbedding ι E
  let L := c.fieldRange
  let : Algebra Ew (AlgebraicClosure Kv) := c.toRingHom.toAlgebra
  have : IsScalarTower Kv Ew (AlgebraicClosure Kv) :=
    IsScalarTower.of_algebraMap_eq fun a => (c.commutes a).symm
  have : Algebra.IsAlgebraic Ew (AlgebraicClosure Kv) := Algebra.IsAlgebraic.tower_top (K := Kv) Ew
  have : IsAlgClosure Ew (AlgebraicClosure Kv) := ⟨inferInstance, inferInstance⟩
  let θ : AlgebraicClosure Ew ≃ₐ[Ew] AlgebraicClosure Kv := IsAlgClosure.equiv Ew _ _
  let : Algebra E.1 (AlgebraicClosure Kv) :=
    ((algebraMap Ew (AlgebraicClosure Kv)).comp (algebraMap E.1 Ew)).toAlgebra
  have : IsScalarTower E.1 Ew (AlgebraicClosure Kv) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ιE' : ℚ̄ →ₐ[E.1] AlgebraicClosure Kv :=
    { ι.toRingHom with commutes' := fun y => (completionEmbedding_algebraMap ι E y).symm }
  let ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure Ew := (θ.symm.toAlgHom.restrictScalars E.1).comp ιE'
  have hι : ∀ y, θ.toRingEquiv (ιE y) = ι y := fun y => θ.apply_symm_apply (ι y)
  have hL : ∀ l ∈ L, ∃ y : Ew, θ.toRingEquiv (algebraMap Ew (AlgebraicClosure Ew) y) = l := by
    intro l hl
    obtain ⟨y, rfl⟩ := (AlgHom.mem_fieldRange).1 hl
    exact ⟨y, θ.commutes y⟩
  have : FiniteDimensional Kv L := LinearEquiv.finiteDimensional c.equivFieldRange.toLinearEquiv
  have : Algebra.IsIntegral L (AlgebraicClosure Kv) := Algebra.IsIntegral.tower_top Kv
  have hfin : Module.finrank Kv L = Module.finrank Kv Ew := c.equivFieldRange.toLinearEquiv.finrank_eq.symm
  refine ⟨ιE, unitsLocalRes_unitsResField_eq_zero Kv Ew L θ.toRingEquiv hL ι ιE hι 2 x ?_⟩
  exact brauerResZ_eq_zero_of_finrank_smul Kv (AlgebraicClosure Kv) L _ (by rw [hfin]; exact hx)

end Finite

section Infinite

open scoped NumberField.LiesOver

variable {v : InfinitePlace K.1}

theorem exists_infPlaceOfEmbedding_eq (w : v.placesOver E.1) :
    ∃ ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion, infPlaceOfEmbedding ι E = w := by
  have : (w : InfinitePlace E.1).LiesOver v := w.2
  let j : (w : InfinitePlace E.1).Completion →ₐ[v.Completion] AlgebraicClosure v.Completion := IsAlgClosed.lift
  let j' : E.1 →+* AlgebraicClosure v.Completion :=
    j.toRingHom.comp (algebraMap E.1 (w : InfinitePlace E.1).Completion)
  let : Algebra E.1 (AlgebraicClosure v.Completion) := j'.toAlgebra
  have hK : ∀ a : K.1, algebraMap E.1 (AlgebraicClosure v.Completion) (algebraMap K.1 E.1 a) =
      algebraMap K.1 (AlgebraicClosure v.Completion) a := by
    intro a
    change j (algebraMap E.1 (w : InfinitePlace E.1).Completion (algebraMap K.1 E.1 a)) = _
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply K.1 v.Completion
      (w : InfinitePlace E.1).Completion, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  have : IsScalarTower K.1 E.1 (AlgebraicClosure v.Completion) :=
    IsScalarTower.of_algebraMap_eq fun a => (hK a).symm
  let ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure v.Completion :=
    (nonempty_algHom_of_isSepClosed : Nonempty (ℚ̄ →ₐ[E.1] AlgebraicClosure v.Completion)).some
  refine ⟨ιE.restrictScalars K.1, (eq_infPlaceOfEmbedding _ E j fun x => ?_).symm⟩
  change j' x = ιE (algebraMap E.1 ℚ̄ x)
  rw [AlgHom.commutes]
  rfl

set_option maxHeartbeats 2000000 in

theorem exists_unitsLocalRes_unitsResField_eq_zero_of_infPlaceOfEmbedding
    (ι : ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion) (x : cohomology (unitsLimitRep K) 2)
    (hx : (unitsLocalRes v.Completion ι 2).hom x = 0) :
    ∃ ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion,
      (unitsLocalRes (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion ιE 2).hom
        ((unitsResField K E 2).hom x) = 0 := by
  have : (infPlaceOfEmbedding ι E : InfinitePlace E.1).LiesOver v := (infPlaceOfEmbedding ι E).2
  set Ew := (infPlaceOfEmbedding ι E : InfinitePlace E.1).Completion
  set Kv := v.Completion
  let c := infCompletionEmbedding ι E
  let L := c.fieldRange
  let : Algebra Ew (AlgebraicClosure Kv) := c.toRingHom.toAlgebra
  have : IsScalarTower Kv Ew (AlgebraicClosure Kv) :=
    IsScalarTower.of_algebraMap_eq fun a => (c.commutes a).symm
  have : Algebra.IsAlgebraic Ew (AlgebraicClosure Kv) := Algebra.IsAlgebraic.tower_top (K := Kv) Ew
  have : IsAlgClosure Ew (AlgebraicClosure Kv) := ⟨inferInstance, inferInstance⟩
  let θ : AlgebraicClosure Ew ≃ₐ[Ew] AlgebraicClosure Kv := IsAlgClosure.equiv Ew _ _
  let : Algebra E.1 (AlgebraicClosure Kv) :=
    ((algebraMap Ew (AlgebraicClosure Kv)).comp (algebraMap E.1 Ew)).toAlgebra
  have : IsScalarTower E.1 Ew (AlgebraicClosure Kv) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ιE' : ℚ̄ →ₐ[E.1] AlgebraicClosure Kv :=
    { ι.toRingHom with commutes' := fun y => (infCompletionEmbedding_algebraMap ι E y).symm }
  let ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure Ew := (θ.symm.toAlgHom.restrictScalars E.1).comp ιE'
  have hι : ∀ y, θ.toRingEquiv (ιE y) = ι y := fun y => θ.apply_symm_apply (ι y)
  have hL : ∀ l ∈ L, ∃ y : Ew, θ.toRingEquiv (algebraMap Ew (AlgebraicClosure Ew) y) = l := by
    intro l hl
    obtain ⟨y, rfl⟩ := (AlgHom.mem_fieldRange).1 hl
    exact ⟨y, θ.commutes y⟩
  have : Algebra.IsIntegral L (AlgebraicClosure Kv) := Algebra.IsIntegral.tower_top Kv
  refine ⟨ιE, unitsLocalRes_unitsResField_eq_zero Kv Ew L θ.toRingEquiv hL ι ιE hι 2 x ?_⟩
  rw [hx, map_zero]

end Infinite

section Main

open scoped NumberField.LiesOver

set_option maxHeartbeats 2000000 in

theorem unitsResField_eq_zero_of_dvd_finrank (ι : LocalEmbeddings K) (x : cohomology (unitsLimitRep K) 2)
    (m : ℕ) (hm : m • x = 0) (hinf : ∀ v : InfinitePlace K.1, brauerLocal ι x (.inl v) = 0)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K.1), brauerLocal ι x (.inr v) ≠ 0 →
      ∀ w : PlacesOver E.1 v, m ∣ Module.finrank (v.adicCompletion K.1) (w.1.adicCompletion E.1)) :
    (unitsResField K E 2).hom x = 0 := by
  have Hfin : ∀ w : HeightOneSpectrum (𝓞 E.1), ∃ ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure (w.adicCompletion E.1),
      (unitsLocalRes (w.adicCompletion E.1) ιE 2).hom ((unitsResField K E 2).hom x) = 0 := by
    intro w
    let v : HeightOneSpectrum (𝓞 K.1) := AdeleBaseChange.below K.1 w
    let w' : PlacesOver E.1 v := ⟨w, AdeleBaseChange.liesOver_below w⟩
    obtain ⟨ι', hι'⟩ := exists_placeOfEmbedding_eq w'
    have key : ∀ u : PlacesOver E.1 v, placeOfEmbedding ι' E = u →
        ∃ ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure (u.1.adicCompletion E.1),
          (unitsLocalRes (u.1.adicCompletion E.1) ιE 2).hom ((unitsResField K E 2).hom x) = 0 := by
      rintro u rfl
      apply exists_unitsLocalRes_unitsResField_eq_zero_of_placeOfEmbedding v ι' x
      rw [unitsLocalRes_eq_of_algHom _ (ι.fin v) ι' 2, ← brauerLocal_apply_inr]
      by_cases h : brauerLocal ι x (.inr v) = 0
      · have h' : placeInv (K := K) (.inr v) (brauerLocal ι x (.inr v)) = 0 := by rw [h, map_zero]
        exact (congrArg (_ • ·) h').trans (smul_zero _)
      · obtain ⟨k, hk⟩ := hfin v h (placeOfEmbedding ι' E)
        have h0 : m • (placeInv (K := K) (.inr v)) (brauerLocal ι x (.inr v)) = 0 := by
          rw [← map_nsmul, ← DFinsupp.smul_apply, ← map_nsmul, hm, map_zero]
          exact map_zero _
        rw [hk, mul_comm, mul_smul]
        exact (congrArg (k • ·) h0).trans (smul_zero k)
    exact key w' hι'
  have Hinf : ∀ w : InfinitePlace E.1, ∃ ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure w.Completion,
      (unitsLocalRes w.Completion ιE 2).hom ((unitsResField K E 2).hom x) = 0 := by
    intro w
    let v : InfinitePlace K.1 := w.comap (algebraMap K.1 E.1)
    let w' : v.placesOver E.1 := ⟨w, ⟨rfl⟩⟩
    obtain ⟨ι', hι'⟩ := exists_infPlaceOfEmbedding_eq w'
    have key : ∀ u : v.placesOver E.1, infPlaceOfEmbedding ι' E = u →
        ∃ ιE : ℚ̄ →ₐ[E.1] AlgebraicClosure (u : InfinitePlace E.1).Completion,
          (unitsLocalRes (u : InfinitePlace E.1).Completion ιE 2).hom ((unitsResField K E 2).hom x) = 0 := by
      rintro u rfl
      apply exists_unitsLocalRes_unitsResField_eq_zero_of_infPlaceOfEmbedding ι' x
      rw [unitsLocalRes_eq_of_algHom _ (ι.inf v) ι' 2, ← brauerLocal_apply_inl]
      exact hinf v
    exact key w' hι'
  let ιE : LocalEmbeddings E := ⟨fun w => (Hfin w).choose, fun w => (Hinf w).choose⟩
  refine eq_zero_of_brauerLocal_apply_eq_zero ιE _ fun u => ?_
  rcases u with w | w
  · rw [brauerLocal_apply_inl]
    exact (Hinf w).choose_spec
  · rw [brauerLocal_apply_inr]
    exact (Hfin w).choose_spec

end Main

end

end GroundTheory.ProfCoh
