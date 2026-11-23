import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StDefinite
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.FinOfPI
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HilbertSchurOfAdjointClosed
open CompanionTheory.D.gk.admitted (stdPoly)
open GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.CyclicScalar

theorem inner_map_map {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖) (g : G) (x y : H) :
    ⟪σ g x, σ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (LinearIsometry.mk (σ g).toLinearMap (hσ g)).inner_map_map x y

theorem map_inv_map {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : G →* (H →L[ℂ] H)) (g : G) (x : H) : σ g (σ g⁻¹ x) = x := by
  have h : σ g * σ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  exact DFunLike.congr_fun h x

theorem orthogonal_stable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖) (U : Submodule ℂ H)
    (hU : ∀ g, ∀ v ∈ U, σ g v ∈ U) (g : G) (v : H) (hv : v ∈ Uᗮ) : σ g v ∈ Uᗮ := by
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  rw [← map_inv_map σ g u, inner_map_map σ hσ]
  exact hv _ (hU _ _ hu)

theorem starProjection_commute {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖) (U : Submodule ℂ H)
    [U.HasOrthogonalProjection] (hU : ∀ g, ∀ v ∈ U, σ g v ∈ U) (g : G) :
    U.starProjection * σ g = σ g * U.starProjection := by
  ext v
  simp only [ContinuousLinearMap.mul_apply]
  have h1 : U.starProjection v ∈ U := Submodule.starProjection_apply_mem U v
  have h2 : v - U.starProjection v ∈ Uᗮ := Submodule.sub_starProjection_mem_orthogonal v
  have h3 : σ g v = σ g (U.starProjection v) + σ g (v - U.starProjection v) := by
    rw [← map_add]; simp
  rw [h3, map_add, Submodule.starProjection_eq_self_iff.2 (hU g _ h1),
    (Submodule.starProjection_apply_eq_zero_iff U).2 (orthogonal_stable σ hσ U hU g _ h2), add_zero]

theorem exists_isIrredSubrep : ∀ (G H : Type) [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)),
    (∀ g v, ‖σ g v‖ = ‖v‖) → ∀ (Q : Submodule ℂ H) (ξ : H), IsClosed (Q : Set H) → ξ ∈ Q → ξ ≠ 0 →
    (∀ T : H →L[ℂ] H, (∀ g, T * σ g = σ g * T) → ∀ v ∈ Q, T v ∈ Q) →
    (∀ g, ∃ c : ℂ, σ g ξ - c • ξ ∈ Qᗮ) → ∃ W, IsIrredSubrep σ W := by
  intro G H _ _ _ _ σ hσ Q ξ hQ hξQ hξ hcomm hscal
  haveI : CompleteSpace Q := hQ.completeSpace_coe

  let S : Submodule ℂ H := Submodule.span ℂ (Set.range fun g => σ g ξ)
  have hSstable : ∀ g, ∀ v ∈ S, σ g v ∈ S := by
    intro g v hv
    have : S ≤ S.comap (σ g : H →ₗ[ℂ] H) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h, rfl⟩
      refine Submodule.subset_span ⟨g * h, ?_⟩
      simp [map_mul]
    exact this hv
  have hW : IsSubrep σ S.topologicalClosure := isSubrep_topologicalClosure hSstable
  have horbit : ∀ g, σ g ξ ∈ S.topologicalClosure := fun g =>
    S.le_topologicalClosure (Submodule.subset_span ⟨g, rfl⟩)
  have hξW : ξ ∈ S.topologicalClosure := by simpa using horbit 1

  have hmin : ∀ A : Submodule ℂ H, IsClosed (A : Set H) → (∀ g, σ g ξ ∈ A) → S.topologicalClosure ≤ A := by
    intro A hA h
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_) hA
    rintro _ ⟨g, rfl⟩
    exact h g

  have hline : ∀ w ∈ S.topologicalClosure, Q.starProjection w ∈ (ℂ ∙ ξ) := by
    have hclosed : IsClosed (((ℂ ∙ ξ).comap (Q.starProjection : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) :=
      (Submodule.closed_of_finiteDimensional (ℂ ∙ ξ)).preimage Q.starProjection.continuous
    refine fun w hw => hmin _ hclosed (fun g => ?_) hw
    obtain ⟨c, hc⟩ := hscal g
    have e : σ g ξ = c • ξ + (σ g ξ - c • ξ) := by abel
    change Q.starProjection (σ g ξ) ∈ (ℂ ∙ ξ)
    rw [e, map_add, (Submodule.starProjection_apply_eq_zero_iff Q).2 hc, add_zero, map_smul,
      Submodule.starProjection_eq_self_iff.2 hξQ]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self ξ)
  refine ⟨S.topologicalClosure, hW, fun h => hξ (by simpa [h] using hξW), fun U hUW hU => ?_⟩
  haveI : CompleteSpace U := hU.1.completeSpace_coe
  have hPc := starProjection_commute σ hσ U hU.2
  have hPQ : U.starProjection ξ ∈ Q := hcomm _ hPc ξ hξQ
  have hPU : U.starProjection ξ ∈ U := Submodule.starProjection_apply_mem U ξ
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c • ξ = U.starProjection ξ := by
    have := hline _ (hUW hPU)
    rw [Submodule.starProjection_eq_self_iff.2 hPQ] at this
    exact Submodule.mem_span_singleton.1 this
  have hcc : c * c = c := by
    have h1 : U.starProjection (c • ξ) = c • ξ := by
      rw [hc]; exact Submodule.starProjection_eq_self_iff.2 hPU
    rw [map_smul, ← hc, smul_smul] at h1
    have h2 : (c * c - c) • ξ = 0 := by rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right hξ)
  have hc01 : c = 0 ∨ c = 1 := by
    have : c * (c - 1) = 0 := by rw [mul_sub, hcc]; ring
    exact (mul_eq_zero.1 this).imp id sub_eq_zero.1
  rcases hc01 with rfl | rfl
  · left
    have hP0 : U.starProjection ξ = 0 := by rw [← hc, zero_smul]
    have hle : S.topologicalClosure ≤ Uᗮ := by
      refine hmin _ (Submodule.isClosed_orthogonal U) fun g => ?_
      refine (Submodule.starProjection_apply_eq_zero_iff U).1 ?_
      have := DFunLike.congr_fun (hPc g) ξ
      simpa [hP0] using this
    refine (Submodule.eq_bot_iff U).2 fun x hx => ?_
    exact inner_self_eq_zero.1 ((Submodule.mem_orthogonal U x).1 (hle (hUW hx)) x hx)
  · right
    have hξU : ξ ∈ U := by
      rw [one_smul] at hc
      rw [hc]; exact hPU
    exact le_antisymm hUW (hmin _ hU.1 fun g => hU.2 g ξ hξU)

end GlobalTheory.CompanionTheory.CyclicScalar
