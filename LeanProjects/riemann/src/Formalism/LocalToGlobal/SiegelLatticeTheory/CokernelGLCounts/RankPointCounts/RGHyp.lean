import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SmulCancelQ

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

structure RGHyp (t₁ t₂ : Term V M r) (Λ₂ : Submodule M.L.O V) (ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f'))
    (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂) (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f') : Prop where
  hU₂ : IsCompl (Submodule.span E (Set.range (Sum.elim t₂.f t₂.f'))) (H.W0 t₂.f t₂.f')
  hU₁ : IsCompl (Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (H.W0 t₁.f t₁.f')
  hsd₁ : H.IsSelfDual t₁.abelian₂
  hsd₂ : H.IsSelfDual Λ₂
  hMM₁ : MMo H t₁ ≤ t₁.abelian₂
  hMM₂ : MMo H t₂ ≤ Λ₂
  hth : ∀ w : ↥(H.W0 t₁.f t₁.f'), (w : V) ∈ t₁.abelian₂ ↔ (ψ w : V) ∈ Λ₂
  hθ : ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H t₂ m₂ ↔
      ∃ w : ↥(H.W0 t₁.f t₁.f'), (m₁ : V) + w ∈ t₁.abelian₂ ∧ (m₂ : V) + ψ w ∈ Λ₂
  hsurj₁ : ∀ m₁ : ↥(MMsharp H t₁), ∃ w : ↥(H.W0 t₁.f t₁.f'), (m₁ : V) + w ∈ t₁.abelian₂
  hC1 : ∀ w : ↥(H.W0 t₁.f t₁.f'),
      φ (H.mkW t₁.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H w.2⟩) = H.mkW t₂.f ⟨ψ w, mem_perp_isotropicSpan_of_mem_framePerp H (ψ w).2⟩
  hC1' : ∀ w : ↥(H.W0 t₁.f t₁.f'),
      φ' (H.mkW t₁.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H w.2⟩) = H.mkW t₂.f' ⟨ψ w, mem_perp_isotropicSpan_of_mem_framePerp' H (ψ w).2⟩
  hC2 : ∀ u ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f')), ∀ hu : u ∈ H.perp (H.X t₁.f),
      ∃ u' ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')), ∃ hu' : u' ∈ H.perp (H.X t₂.f),
        φ (H.mkW t₁.f ⟨u, hu⟩) = H.mkW t₂.f ⟨u', hu'⟩
  hC2' : ∀ u ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f')), ∀ hu : u ∈ H.perp (H.X t₁.f'),
      ∃ u' ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')), ∃ hu' : u' ∈ H.perp (H.X t₂.f'),
        φ' (H.mkW t₁.f' ⟨u, hu⟩) = H.mkW t₂.f' ⟨u', hu'⟩

theorem RGHyp.trF {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V} {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')}
    {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂} {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'}
    (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    {u₁ : V} (hu₁U : u₁ ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (hu₁p : u₁ ∈ H.perp (H.X t₁.f))
    (n : ↥(H.W0 t₁.f t₁.f')) (hx₁ : u₁ + n ∈ H.perp (H.X t₁.f))
    {a b : V} (ha : a ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f'))) (hb : b ∈ H.W0 t₂.f t₂.f')
    (hap : a ∈ H.perp (H.X t₂.f)) (hx₂ : a + b ∈ H.perp (H.X t₂.f))
    (h : φ (H.mkW t₁.f ⟨u₁ + n, hx₁⟩) = H.mkW t₂.f ⟨a + b, hx₂⟩) :
    b = ψ n ∧ φ (H.mkW t₁.f ⟨u₁, hu₁p⟩) = H.mkW t₂.f ⟨a, hap⟩ := by
  obtain ⟨u', hu'U, hu'p, hφ⟩ := D.hC2 u₁ hu₁U hu₁p
  have hn : (n : V) ∈ H.perp (H.X t₁.f) := mem_perp_isotropicSpan_of_mem_framePerp H n.2
  have hsplit : H.mkW t₁.f ⟨u₁ + n, hx₁⟩ = H.mkW t₁.f ⟨u₁, hu₁p⟩ + H.mkW t₁.f ⟨n, hn⟩ := by
    rw [← map_add]
    rfl
  rw [hsplit, map_add, hφ, D.hC1 n, ← map_add] at h
  have hX : ((u' + ψ n : V)) - (a + b) ∈ H.X t₂.f := sub_mem_X_of_mkW_eq H h
  have hXle : H.X t₂.f ≤ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨Sum.inl i.castSucc, rfl⟩
  have hdiff : (ψ n : V) - b = ((u' + ψ n) - (a + b)) - (u' - a) := by abel
  have hmemS : (ψ n : V) - b ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')) := by
    rw [hdiff]
    exact Submodule.sub_mem _ (hXle hX) (Submodule.sub_mem _ hu'U ha)
  have hmemW : (ψ n : V) - b ∈ H.W0 t₂.f t₂.f' := Submodule.sub_mem _ (ψ n).2 hb
  have h0 : (ψ n : V) - b = 0 := (Submodule.disjoint_def.1 D.hU₂.disjoint) _ hmemS hmemW
  have hbψ : b = ψ n := (sub_eq_zero.1 h0).symm
  refine ⟨hbψ, ?_⟩
  rw [hφ]
  have hua : (u' : V) - a ∈ H.X t₂.f := by
    have e1 : (u' : V) - a = (u' + ψ n) - (a + b) := by
      rw [hbψ]
      abel
    rw [e1]
    exact hX
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  exact hua

theorem RGHyp.trF' {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V} {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')}
    {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂} {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'}
    (D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ')
    {u₁ : V} (hu₁U : u₁ ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (hu₁p : u₁ ∈ H.perp (H.X t₁.f'))
    (n : ↥(H.W0 t₁.f t₁.f')) (hx₁ : u₁ + n ∈ H.perp (H.X t₁.f'))
    {a b : V} (ha : a ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f'))) (hb : b ∈ H.W0 t₂.f t₂.f')
    (hap : a ∈ H.perp (H.X t₂.f')) (hx₂ : a + b ∈ H.perp (H.X t₂.f'))
    (h : φ' (H.mkW t₁.f' ⟨u₁ + n, hx₁⟩) = H.mkW t₂.f' ⟨a + b, hx₂⟩) :
    b = ψ n ∧ φ' (H.mkW t₁.f' ⟨u₁, hu₁p⟩) = H.mkW t₂.f' ⟨a, hap⟩ := by
  obtain ⟨u', hu'U, hu'p, hφ⟩ := D.hC2' u₁ hu₁U hu₁p
  have hn : (n : V) ∈ H.perp (H.X t₁.f') := mem_perp_isotropicSpan_of_mem_framePerp' H n.2
  have hsplit : H.mkW t₁.f' ⟨u₁ + n, hx₁⟩ = H.mkW t₁.f' ⟨u₁, hu₁p⟩ + H.mkW t₁.f' ⟨n, hn⟩ := by
    rw [← map_add]
    rfl
  rw [hsplit, map_add, hφ, D.hC1' n, ← map_add] at h
  have hX : ((u' + ψ n : V)) - (a + b) ∈ H.X t₂.f' := sub_mem_X_of_mkW_eq H h
  have hXle : H.X t₂.f' ≤ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')) := by
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    exact ⟨Sum.inr i.castSucc, rfl⟩
  have hdiff : (ψ n : V) - b = ((u' + ψ n) - (a + b)) - (u' - a) := by abel
  have hmemS : (ψ n : V) - b ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')) := by
    rw [hdiff]
    exact Submodule.sub_mem _ (hXle hX) (Submodule.sub_mem _ hu'U ha)
  have hmemW : (ψ n : V) - b ∈ H.W0 t₂.f t₂.f' := Submodule.sub_mem _ (ψ n).2 hb
  have h0 : (ψ n : V) - b = 0 := (Submodule.disjoint_def.1 D.hU₂.disjoint) _ hmemS hmemW
  have hbψ : b = ψ n := (sub_eq_zero.1 h0).symm
  refine ⟨hbψ, ?_⟩
  rw [hφ]
  have hua : (u' : V) - a ∈ H.X t₂.f' := by
    have e1 : (u' : V) - a = (u' + ψ n) - (a + b) := by
      rw [hbψ]
      abel
    rw [e1]
    exact hX
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  rw [Submodule.Quotient.eq, Submodule.mem_comap]
  exact hua

theorem RGHyp.θs {t₁ t₂ : Term V M r} {Λ₂ : Submodule M.L.O V} {ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f')}
    {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂} {φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f} {φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f'}
    (_D : RGHyp H t₁ t₂ Λ₂ ψ θ φ φ') (m₂ : ↥(MMsharp H t₂)) :
    ∃ m₁ : ↥(MMsharp H t₁), θ (ddMk H t₁ m₁) = ddMk H t₂ m₂ := by
  obtain ⟨m₁, hm₁⟩ := Submodule.Quotient.mk_surjective _ (θ.symm (ddMk H t₂ m₂))
  refine ⟨m₁, ?_⟩
  show θ (Submodule.Quotient.mk m₁) = _
  rw [hm₁, LinearEquiv.apply_symm_apply]

end RG3

end Formalism.L2.SG.LsDatumA
