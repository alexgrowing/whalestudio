import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

namespace GlobalTheory.SmGL.EvalInj

open ValuativeRel Topology in
private theorem eq_zero_of_sum_intertwining_apply_eq_zero {H X Y : Type} [Group H] [AddCommGroup X]
    [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ H X)
    (ρ : Representation ℂ H Y) (hρ : ρ.IsIrreducible)
    (hschur : ∀ T : ρ.IntertwiningMap ρ, ∃ c : ℂ, ∀ v, T v = c • v) :
    ∀ (m : ℕ) (φ : Fin m → (Y →ₗ[ℂ] X)), LinearIndependent ℂ φ →
      (∀ i g v, φ i (ρ g v) = τ g (φ i v)) → ∀ y : Fin m → Y, ∑ i, φ i (y i) = 0 → y = 0 := by
  intro m
  induction m with
  | zero => intro φ _ _ y _; exact Subsingleton.elim _ _
  | succ m ih =>
    intro φ hli hφ y hy
    let Φ : (Fin (m + 1) → Y) →ₗ[ℂ] X := ∑ i, (φ i).comp (LinearMap.proj i)
    have hΦ : ∀ w, Φ w = ∑ i, φ i (w i) := fun w => by simp [Φ]
    let S := LinearMap.ker Φ
    have hSinv : ∀ g, ∀ w ∈ S, (fun i => ρ g (w i)) ∈ S := by
      intro g w hw
      rw [LinearMap.mem_ker, hΦ] at hw ⊢
      simp_rw [hφ]
      rw [← map_sum, hw, map_zero]
    let p : S →ₗ[ℂ] Y := (LinearMap.proj (Fin.last m)).comp S.subtype
    have hp : Function.Injective p := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro w hw
      have hw0 : (w : Fin (m + 1) → Y) (Fin.last m) = 0 := hw
      have hsum : ∑ i : Fin m, φ (Fin.castSucc i) ((w : Fin (m + 1) → Y) (Fin.castSucc i)) = 0 := by
        have hw' := w.2
        rw [LinearMap.mem_ker, hΦ, Fin.sum_univ_castSucc, hw0, map_zero, add_zero] at hw'
        exact hw'
      have hzero := ih (fun i => φ (Fin.castSucc i)) (hli.comp _ (Fin.castSucc_injective m))
        (fun i => hφ _) _ hsum
      apply Subtype.ext
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact hw0
      · exact congrFun hzero j
    let R : Subrepresentation ρ := ⟨LinearMap.range p, by
      rintro g _ ⟨w, rfl⟩
      exact ⟨⟨fun i => ρ g ((w : Fin (m + 1) → Y) i), hSinv g w w.2⟩, rfl⟩⟩
    have hyS : y ∈ S := by rw [LinearMap.mem_ker, hΦ]; exact hy
    haveI := hρ
    rcases IsSimpleOrder.eq_bot_or_eq_top R with hR | hR
    · have hrange : LinearMap.range p = ⊥ := congrArg Subrepresentation.toSubmodule hR
      have hpy : p ⟨y, hyS⟩ = 0 := by
        rw [LinearMap.range_eq_bot] at hrange
        rw [hrange]
        rfl
      exact congrArg Subtype.val (hp (hpy.trans (map_zero p).symm))
    · exfalso
      have hrange : LinearMap.range p = ⊤ := congrArg Subrepresentation.toSubmodule hR
      let e := LinearEquiv.ofBijective p ⟨hp, LinearMap.range_eq_top.mp hrange⟩
      have hlast : ∀ v, (e.symm v : Fin (m + 1) → Y) (Fin.last m) = v := fun v =>
        e.apply_symm_apply v
      have he : ∀ g v, e.symm (ρ g v) =
          ⟨fun i => ρ g ((e.symm v : Fin (m + 1) → Y) i), hSinv g _ (e.symm v).2⟩ := by
        intro g v
        apply e.injective
        rw [LinearEquiv.apply_symm_apply]
        show ρ g v = ρ g ((e.symm v : Fin (m + 1) → Y) (Fin.last m))
        rw [hlast]
      let T : Fin m → ρ.IntertwiningMap ρ := fun j =>
        ⟨(LinearMap.proj (Fin.castSucc j)).comp (S.subtype.comp e.symm.toLinearMap), by
          intro g
          ext v
          simp [he]⟩
      choose c hc using fun j => hschur (T j)
      have hT : ∀ j v, (e.symm v : Fin (m + 1) → Y) (Fin.castSucc j) = c j • v := fun j v => hc j v
      have hzero : ∑ i, (Fin.snoc (α := fun _ => ℂ) c 1 i) • φ i = 0 := by
        ext v
        have hv := (e.symm v).2
        rw [LinearMap.mem_ker, hΦ, Fin.sum_univ_castSucc] at hv
        simp only [hT, hlast, map_smul] at hv
        simpa [Fin.sum_univ_castSucc] using hv
      have h1 := (Fintype.linearIndependent_iff.mp hli) _ hzero (Fin.last m)
      simp at h1

open ValuativeRel Topology in

theorem _root_.GlobalTheory.SmGL.EvalInj.lift_subtype_injective :
    ∀ (H X Y : Type) [Group H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
      (τ : Representation ℂ H X) (ρ : Representation ℂ H Y), ρ.IsIrreducible →
      (∀ T : ρ.IntertwiningMap ρ, ∃ c : ℂ, ∀ v, T v = c • v) →
      ∀ (M : Submodule ℂ (Y →ₗ[ℂ] X)), (∀ φ ∈ M, ∀ g v, φ (ρ g v) = τ g (φ v)) →
      Function.Injective (TensorProduct.lift M.subtype) := by
  intro H X Y _ _ _ _ _ τ ρ hρ hschur M hM
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨M', hfin, hsub⟩ :=
    TensorProduct.exists_finite_submodule_left_of_setFinite {t} (Set.finite_singleton t)
  obtain ⟨t₀, rfl⟩ := hsub (Set.mem_singleton t)
  haveI := hfin
  let b := Module.finBasis ℂ M'
  set y : Fin (Module.finrank ℂ M') → Y := fun i => TensorProduct.equivFinsuppOfBasisLeft b t₀ i
    with hy
  have ht₀ : t₀ = ∑ i, b i ⊗ₜ[ℂ] y i := by
    conv_lhs => rw [← (TensorProduct.equivFinsuppOfBasisLeft b).symm_apply_apply t₀]
    rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype]
    intro i
    exact TensorProduct.tmul_zero _ _
  let φ : Fin (Module.finrank ℂ M') → (Y →ₗ[ℂ] X) := fun i => ((b i : M) : Y →ₗ[ℂ] X)
  have hli : LinearIndependent ℂ φ :=
    (b.linearIndependent.map' M'.subtype (Submodule.ker_subtype _)).map' M.subtype
      (Submodule.ker_subtype _)
  have hsum : ∑ i, φ i (y i) = 0 := by
    rw [ht₀] at ht
    simpa [map_sum, φ] using ht
  have hy0 := eq_zero_of_sum_intertwining_apply_eq_zero τ ρ hρ hschur _ φ hli
    (fun i g v => hM _ (b i : M).2 g v) y hsum
  rw [ht₀, hy0]
  simp

end GlobalTheory.SmGL.EvalInj
