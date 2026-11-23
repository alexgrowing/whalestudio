import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite

open CompanionTheory.Rg.Fl GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AutMult
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.RgFl

variable {G X H : Type} [Group G] [TopologicalSpace G] [NormedAddCommGroup X] [InnerProductSpace ℂ X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {δ : G →* (X →L[ℂ] X)} {ρ : G →* (H →L[ℂ] H)}

def evalHom (δ : G →* (X →L[ℂ] X)) (ρ : G →* (H →L[ℂ] H)) (u : X) : homIn δ ρ ⊤ →ₗ[ℂ] H where
  toFun T := T.1 u
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem norm_evalHom (hδ : IsIrrUnitary δ) (hρ : IsUnitaryRep ρ) {u : X} (hu : ‖u‖ = 1) (y : X)
    (T : homIn δ ρ ⊤) : ‖evalHom δ ρ y T‖ = ‖y‖ * ‖evalHom δ ρ u T‖ := by
  change ‖T.1 y‖ = ‖y‖ * ‖T.1 u‖
  rw [norm_apply_eq hδ hρ T.2 y, norm_apply_eq hδ hρ T.2 u, hu, mul_one, mul_comm]

theorem evalHom_injective (hδ : IsIrrUnitary δ) (hρ : IsUnitaryRep ρ) {u : X} (hu : ‖u‖ = 1) :
    Function.Injective (evalHom δ ρ u) := by
  refine (injective_iff_map_eq_zero _).2 fun T hT => Subtype.ext (ContinuousLinearMap.ext fun x => ?_)
  have h := norm_evalHom hδ hρ hu x T
  rw [hT, norm_zero, mul_zero] at h
  exact norm_eq_zero.1 h

theorem exists_op_unit (hδ : IsIrrUnitary δ) (hρ : IsUnitaryRep ρ) (y : X) {u : X} (hu : ‖u‖ = 1) :
    ∃ A : H →L[ℂ] H, ∀ T ∈ homIn δ ρ ⊤, ∀ x, A (T x) = ⟪u, x⟫_ℂ • T y := by
  have hinj := evalHom_injective hδ hρ hu
  let S : Submodule ℂ H := LinearMap.range (evalHom δ ρ u)
  let e := LinearEquiv.ofInjective (evalHom δ ρ u) hinj
  let L : S →ₗ[ℂ] H := evalHom δ ρ y ∘ₗ e.symm.toLinearMap
  have hL : ∀ v : S, ‖L v‖ ≤ ‖y‖ * ‖v‖ := fun v => by
    have h := norm_evalHom hδ hρ hu y (e.symm v)
    have h2 : evalHom δ ρ u (e.symm v) = v := congrArg Subtype.val (e.apply_symm_apply v)
    rw [h2] at h
    exact h.le
  have hLe : ∀ T : homIn δ ρ ⊤, L ⟨T.1 u, T, rfl⟩ = T.1 y := fun T => by
    have h : e.symm ⟨T.1 u, T, rfl⟩ = T := e.symm_apply_apply T
    change evalHom δ ρ y (e.symm ⟨T.1 u, T, rfl⟩) = T.1 y
    rw [h]
    rfl
  let K : Submodule ℂ H := S.topologicalClosure
  haveI : IsClosed (K : Set H) := S.isClosed_topologicalClosure
  haveI : CompleteSpace K := IsClosed.completeSpace_coe (s := (K : Set H))
  let i : S →ₗᵢ[ℂ] K := ⟨Submodule.inclusion S.le_topologicalClosure, fun _ => rfl⟩
  have hd : DenseRange i.toContinuousLinearMap := by
    refine Topology.IsInducing.subtypeVal.dense_iff.2 fun w => closure_mono (fun z hz => ?_) w.2
    exact ⟨⟨z, S.le_topologicalClosure hz⟩, ⟨⟨z, hz⟩, rfl⟩, rfl⟩
  let B : K →L[ℂ] H := (L.mkContinuous ‖y‖ hL).extend i.toContinuousLinearMap
  have hB : ∀ v : S, B (i v) = L v := fun v =>
    ((L.mkContinuous ‖y‖ hL).extend_eq hd i.isometry.isUniformInducing v)
  refine ⟨B ∘L K.orthogonalProjection, fun T hT x => ?_⟩
  have hmem : ⟪u, x⟫_ℂ • T u ∈ K := K.smul_mem _ (S.le_topologicalClosure ⟨⟨T, hT⟩, rfl⟩)
  have horth : T x - ⟪u, x⟫_ℂ • T u ∈ Kᗮ := by
    rw [Submodule.orthogonal_closure, Submodule.mem_orthogonal]
    rintro _ ⟨T', rfl⟩
    change ⟪T'.1 u, T x - ⟪u, x⟫_ℂ • T u⟫_ℂ = 0
    rw [inner_sub_right, inner_smul_right, inner_eq_be hδ hρ hT T'.2, inner_eq_be hδ hρ hT T'.2,
      inner_self_eq_norm_sq_to_K, hu]
    simp [mul_comm]
  have hproj : K.orthogonalProjection (T x) = ⟪u, x⟫_ℂ • i ⟨T u, ⟨T, hT⟩, rfl⟩ :=
    Subtype.ext (Submodule.eq_starProjection_of_mem_orthogonal hmem horth)
  change B (K.orthogonalProjection (T x)) = _
  rw [hproj, map_smul, hB, hLe ⟨T, hT⟩]

theorem exists_op (hδ : IsIrrUnitary δ) (hρ : IsUnitaryRep ρ) (y ξ : X) :
    ∃ A : H →L[ℂ] H, ∀ T ∈ homIn δ ρ ⊤, ∀ x, A (T x) = ⟪ξ, x⟫_ℂ • T y := by
  by_cases h0 : ξ = 0
  · exact ⟨0, fun T _ x => by simp [h0]⟩
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 h0
  have hn' : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast hn
  obtain ⟨A, hA⟩ := exists_op_unit hδ hρ y (u := (‖ξ‖ : ℂ)⁻¹ • ξ) (by
    rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hn])
  refine ⟨(‖ξ‖ : ℂ) • A, fun T hT x => ?_⟩
  rw [ContinuousLinearMap.smul_apply, hA T hT, inner_smul_left, smul_smul, map_inv₀, Complex.conj_ofReal,
    ← mul_assoc, mul_inv_cancel₀ hn', one_mul]

theorem stOp : StOp := by
  intro G X H _ _ _ _ _ _ _ δ ρ hδ hρ _
  choose A hA using fun y ξ : X => exists_op (H := H) hδ hρ y ξ
  exact ⟨A, hA⟩

end GlobalTheory.CompanionTheory.RgFl
