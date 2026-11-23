import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfInd
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatDesc
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace PositivityTheory.HtPt.Mh

theorem ind_id : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (A : Subalgebra R (T → R)), IsHopfOrder A → indOrder (MonoidHom.id T) A = A := by
  intro R _ T _ A hA
  ext f
  refine ⟨fun h => ?_, fun h t => Twhopf.translate_mem R T A hA f h t⟩
  have := h 1
  simpa using this

theorem ext_tensor : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (A : Subalgebra R (T → R)), IsHopfOrder A → (∃ d : R, algebraMap R R' d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A) → IsHopfOrder (extOrder (algebraMap R R') A) ∧ ∃ e : R' ⊗[R] A ≃ₐ[R'] extOrder (algebraMap R R') A, ∀ (a : A) (t : T), (e (1 ⊗ₜ a)).1 t = algebraMap R R' (a.1 t) := by
  intro R _ _ T _ _ R' _ _ _ A hA ⟨d, hd, hdA⟩
  classical
  cases nonempty_fintype T
  have := hA.finite
  have := hA.projective
  let c : A →ₐ[R] (T → R') :=
    AlgHom.pi fun t => (Algebra.ofId R R').comp (evalAt A t)
  let L : R' ⊗[R] A →ₐ[R'] (T → R') :=
    Algebra.TensorProduct.lift (Algebra.ofId R' (T → R')) c (fun _ _ => Commute.all _ _)
  have hL : ∀ (r : R') (a : A) (t : T), L (r ⊗ₜ a) t = r * algebraMap R R' (a.1 t) := fun r a t => rfl
  let m : T → A := fun t => ⟨_, hdA (Pi.single t 1)⟩
  let M : (T → R') →ₗ[R'] R' ⊗[R] A :=
    ∑ t, (LinearMap.proj t : (T → R') →ₗ[R'] R').smulRight ((1 : R') ⊗ₜ[R] m t)
  have hM : ∀ x, M (L x) = algebraMap R R' d • x := by
    intro x
    induction x with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]
    | tmul r a =>
      have e : ∑ t, a.1 t • m t = d • a := by
        apply Subtype.ext
        funext s
        simp [m, Pi.single_apply, Finset.sum_apply, mul_comm]
      have e2 : ∀ t, (r * algebraMap R R' (a.1 t)) • ((1 : R') ⊗ₜ[R] m t) = r ⊗ₜ[R] (a.1 t • m t) := by
        intro t
        rw [TensorProduct.smul_tmul', ← TensorProduct.smul_tmul, smul_eq_mul, mul_one, Algebra.smul_def, mul_comm]
      simp only [M, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply, hL, e2]
      rw [← TensorProduct.tmul_sum, e, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', algebraMap_smul]
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h := hM x
    rw [hx, map_zero] at h
    exact (smul_eq_zero_iff_right hd).1 h.symm
  have hrange : L.range = extOrder (algebraMap R R') A := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      induction x with
      | zero => exact (map_zero L.toRingHom).symm ▸ zero_mem _
      | add x y hx hy => exact (map_add L.toRingHom x y).symm ▸ add_mem hx hy
      | tmul r a =>
        exact (extOrder (algebraMap R R') A).smul_mem (OrderApi.comp_mem_extOrder (algebraMap R R') a.2) r
    · refine Algebra.adjoin_le ?_
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨(1 : R') ⊗ₜ ⟨f, hf⟩, funext fun t => (hL _ _ t).trans (one_mul _)⟩
  let e : R' ⊗[R] A ≃ₐ[R'] extOrder (algebraMap R R') A :=
    (AlgEquiv.ofInjective L hinj).trans (Subalgebra.equivOfEq _ _ hrange)
  refine ⟨⟨Module.Finite.equiv e.toLinearEquiv, Module.Projective.of_equiv e.toLinearEquiv,
    ⟨algebraMap R R' d, hd, fun g => ?_⟩, fun g hg => ?_, fun g hg => ?_⟩,
    e, fun a t => (hL 1 a t).trans (one_mul _)⟩
  · rw [← hrange]
    refine ⟨M g, funext fun s => ?_⟩
    change L (M g) s = _
    simp only [M, LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.proj_apply, map_sum, map_smul,
      Finset.sum_apply, Pi.smul_apply, hL, m]
    simp [Pi.single_apply, apply_ite, mul_comm]
  · rw [Htat.ext_span] at hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨f, hf, rfl⟩ := hg
      have key : ∀ n ∈ prodSpan A, (fun z => algebraMap R R' (n z)) ∈ prodSpan (extOrder (algebraMap R R') A) := by
        intro n hn
        induction hn using Submodule.span_induction with
        | mem n hn =>
          obtain ⟨a, ha, b, hb, rfl⟩ := hn
          simpa using OrderApi.mul_mem_prodSpan (OrderApi.comp_mem_extOrder (algebraMap R R') ha)
            (OrderApi.comp_mem_extOrder (algebraMap R R') hb)
        | zero =>
          convert Submodule.zero_mem (prodSpan (extOrder (algebraMap R R') A)) using 1
          ext z; simp
        | add x y _ _ hx hy =>
          convert Submodule.add_mem _ hx hy using 1
          ext z; simp
        | smul r x _ hx =>
          convert Submodule.smul_mem _ (algebraMap R R' r) hx using 1
          ext z; simp
      exact key _ (hA.comul f hf)
    | zero => exact Submodule.zero_mem _
    | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
    | smul r x _ hx => exact Submodule.smul_mem _ r hx
  · rw [Htat.ext_span] at hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨f, hf, rfl⟩ := hg
      exact OrderApi.comp_mem_extOrder (algebraMap R R') (hA.inv f hf)
    | zero => exact Subalgebra.zero_mem _
    | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
    | smul r x _ hx => exact Subalgebra.smul_mem _ hx r

end PositivityTheory.HtPt.Mh
