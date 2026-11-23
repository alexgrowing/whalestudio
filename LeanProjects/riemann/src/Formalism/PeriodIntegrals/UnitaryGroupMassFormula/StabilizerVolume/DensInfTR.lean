import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfSS

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open scoped TensorProduct
open PI.AdicCompletionValuation

theorem exists_coord_pi {X : Type} [AddCommGroup X] [TopologicalSpace X] {k : ℕ}
    (e : X ≃ₜ (Fin k → ℝ)) (he : ∀ x y, e (x + y) = e x + e y) (κ : Type) [Fintype κ] :
    ∃ (n : ℕ) (e' : (κ → X) ≃ₜ (Fin n → ℝ)), ∀ x y, e' (x + y) = e' x + e' y := by
  classical
  let L : (κ → Fin k → ℝ) ≃L[ℝ] (Fin (Module.finrank ℝ (κ → Fin k → ℝ)) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  refine ⟨Module.finrank ℝ (κ → Fin k → ℝ), (Homeomorph.piCongrRight fun _ => e).trans L.toHomeomorph, ?_⟩
  intro x y
  simp only [Homeomorph.trans_apply, Homeomorph.piCongrRight_apply, ContinuousLinearEquiv.coe_toHomeomorph]
  rw [← map_add]
  congr 1
  funext i
  simp [he]

theorem exists_coord_Ainf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] :
    ∃ (k : ℕ) (e : Ainf F ≃ₜ (Fin k → ℝ)), ∀ x y, e (x + y) = e x + e y := by
  classical
  have hreal : ∀ v : NumberField.InfinitePlace F, v.IsReal := fun v => NumberField.IsTotallyReal.isReal v
  let e1 : Ainf F ≃ₜ (NumberField.InfinitePlace F → ℝ) :=
    Homeomorph.piCongrRight fun v =>
      (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal (hreal v)).toHomeomorph
  let L : (NumberField.InfinitePlace F → ℝ) ≃L[ℝ]
      (Fin (Module.finrank ℝ (NumberField.InfinitePlace F → ℝ)) → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  refine ⟨Module.finrank ℝ (NumberField.InfinitePlace F → ℝ), e1.trans L.toHomeomorph, ?_⟩
  intro x y
  simp only [Homeomorph.trans_apply, ContinuousLinearEquiv.coe_toHomeomorph]
  rw [← map_add]
  congr 1
  funext v
  have hx : e1 (x + y) v = NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (hreal v) (x v + y v) := rfl
  have hx1 : e1 x v = NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (hreal v) (x v) := rfl
  have hx2 : e1 y v = NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal (hreal v) (y v) := rfl
  rw [Pi.add_apply, hx, hx1, hx2, map_add]

theorem exists_coord_tens (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E]
    [NumberField E] [Algebra F E] :
    ∃ (k : ℕ) (e : Ainf F ⊗[F] E ≃ₜ (Fin k → ℝ)), ∀ x y, e (x + y) = e x + e y := by
  classical
  obtain ⟨k, eA, heA⟩ := exists_coord_Ainf F
  let b : Module.Basis (Fin (Module.finrank F E)) F E := Module.finBasis F E
  let bR := Algebra.TensorProduct.basis (Ainf F) b
  let ℓ : (Ainf F ⊗[F] E) ≃ₗ[Ainf F] (Fin (Module.finrank F E) → Ainf F) := bR.equivFun
  have hc1 : Continuous ℓ := IsModuleTopology.continuous_of_linearMap ℓ.toLinearMap
  have hc2 : Continuous ℓ.symm := IsModuleTopology.continuous_of_linearMap ℓ.symm.toLinearMap
  let h1 : (Ainf F ⊗[F] E) ≃ₜ (Fin (Module.finrank F E) → Ainf F) :=
    { toEquiv := ℓ.toEquiv, continuous_toFun := hc1, continuous_invFun := hc2 }
  obtain ⟨n, e', he'⟩ := exists_coord_pi eA heA (Fin (Module.finrank F E))
  refine ⟨n, h1.trans e', ?_⟩
  intro x y
  simp only [Homeomorph.trans_apply]
  rw [show h1 (x + y) = h1 x + h1 y from map_add ℓ x y, he']

theorem exists_coord_sub {X : Type} [AddCommGroup X] [TopologicalSpace X] {N : ℕ}
    (e : X ≃ₜ (Fin N → ℝ)) (he : ∀ x y, e (x + y) = e x + e y) (H : AddSubgroup X)
    (hH : IsClosed (H : Set X)) (hdiv : ∀ n : ℕ, 0 < n → ∀ x ∈ H, ∃ y ∈ H, n • y = x) :
    ∃ (m : ℕ) (eH : H ≃ₜ (Fin m → ℝ)), ∀ x y, eH (x + y) = eH x + eH y := by
  classical
  have e0 : e 0 = 0 := by simpa using he 0 0
  let eA : X →+ (Fin N → ℝ) := { toFun := e, map_zero' := e0, map_add' := he }
  have hcl : IsClosed (e '' (H : Set X)) := e.isClosed_image.mpr hH
  have hrat : ∀ x ∈ H, ∀ q : ℚ, (q : ℝ) • e x ∈ e '' (H : Set X) := by
    intro x hx q
    obtain ⟨y, hy, hyx⟩ := hdiv q.den q.pos x hx
    refine ⟨q.num • y, H.zsmul_mem hy _, ?_⟩
    have h1 : e (q.num • y) = q.num • e y := map_zsmul eA q.num y
    have h2 : (q.den : ℝ) • e y = e x := by
      rw [← hyx]
      have := map_nsmul eA q.den y
      simp only [eA, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
      rw [this, Nat.cast_smul_eq_nsmul]
    rw [h1, ← h2, smul_smul, ← Int.cast_smul_eq_zsmul ℝ]
    congr 1
    have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_nz
    rw [Rat.cast_def]
    field_simp
  have hreal : ∀ x ∈ H, ∀ r : ℝ, r • e x ∈ e '' (H : Set X) := by
    intro x hx r
    have hS : IsClosed {t : ℝ | t • e x ∈ e '' (H : Set X)} :=
      hcl.preimage (continuous_id.smul continuous_const)
    have hsub : Set.range (Rat.cast : ℚ → ℝ) ⊆ {t : ℝ | t • e x ∈ e '' (H : Set X)} := by
      rintro _ ⟨q, rfl⟩; exact hrat x hx q
    have := hS.closure_subset_iff.mpr hsub
    rw [Rat.denseRange_cast.closure_range] at this
    exact this (Set.mem_univ r)
  let V : Submodule ℝ (Fin N → ℝ) :=
    { carrier := e '' (H : Set X)
      add_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, H.add_mem ha hb, he a b⟩
      zero_mem' := ⟨0, H.zero_mem, e0⟩
      smul_mem' := by
        rintro r _ ⟨a, ha, rfl⟩
        exact hreal a ha r }
  let L : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  let eI : H ≃ₜ V := e.image (H : Set X)
  refine ⟨Module.finrank ℝ V, eI.trans L.toHomeomorph, ?_⟩
  intro x y
  simp only [Homeomorph.trans_apply, ContinuousLinearEquiv.coe_toHomeomorph]
  rw [← map_add]
  congr 1
  apply Subtype.ext
  show e ((x : X) + (y : X)) = e x + e y
  exact he x y

end PI.VolStabS
