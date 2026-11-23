import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGP

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section CR

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

def GamG (t : Term V M r) (g : Fin (r + 1) → V) : Set (DDt H t × H.Wb g) :=
  {p | ∃ (u : ↥(MMsharp H t)) (hu : (u : V) ∈ H.perp (H.X g)), p = (ddMk H t u, H.mkW g ⟨u, hu⟩)}

theorem mkW_add {g : Fin (r + 1) → V} (a b : V) (ha : a ∈ H.perp (H.X g)) (hb : b ∈ H.perp (H.X g)) :
    H.mkW g ⟨a + b, Submodule.add_mem _ ha hb⟩ = H.mkW g ⟨a, ha⟩ + H.mkW g ⟨b, hb⟩ := by
  rw [← map_add]
  rfl

theorem mkW_sub {g : Fin (r + 1) → V} (a b : V) (ha : a ∈ H.perp (H.X g)) (hb : b ∈ H.perp (H.X g)) :
    H.mkW g ⟨a - b, Submodule.sub_mem _ ha hb⟩ = H.mkW g ⟨a, ha⟩ - H.mkW g ⟨b, hb⟩ := by
  rw [← map_sub]
  rfl

theorem mkW_congr {g : Fin (r + 1) → V} {a b : V} (ha : a ∈ H.perp (H.X g)) (hb : b ∈ H.perp (H.X g))
    (h : a = b) : H.mkW g ⟨a, ha⟩ = H.mkW g ⟨b, hb⟩ := by
  subst h
  rfl

theorem spanMM_le_U (t : Term V M r) :
    Submodule.span E (Set.range (H.MMfam t)) ≤ Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
  have hsup : Submodule.span E (Set.range (Sum.elim t.f t.f')) = H.Xp t.f ⊔ H.Xp t.f' := by
    rw [Set.Sum.elim_range, Submodule.span_union]
    rfl
  rw [hsup]
  exact Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact MMfam_mem_sup H t i)

theorem claimR_side (t₁ t₂ : Term V M r) (Λ₂ : Submodule M.L.O V)
    (ψ : ↥(H.W0 t₁.f t₁.f') ≃ₗ[E] ↥(H.W0 t₂.f t₂.f'))
    (hU₂ : IsCompl (Submodule.span E (Set.range (Sum.elim t₂.f t₂.f'))) (H.W0 t₂.f t₂.f'))
    (hU₁ : IsCompl (Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (H.W0 t₁.f t₁.f'))
    (hsd₁ : H.IsSelfDual t₁.abelian₂) (hsd₂ : H.IsSelfDual Λ₂)
    (hMM₁ : MMo H t₁ ≤ t₁.abelian₂) (hMM₂ : MMo H t₂ ≤ Λ₂)
    (hth : ∀ w : ↥(H.W0 t₁.f t₁.f'), (w : V) ∈ t₁.abelian₂ ↔ (ψ w : V) ∈ Λ₂)
    (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂)
    (hθ : ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H t₂ m₂ ↔
      ∃ w : ↥(H.W0 t₁.f t₁.f'), (m₁ : V) + w ∈ t₁.abelian₂ ∧ (m₂ : V) + ψ w ∈ Λ₂)
    (hsurj₁ : ∀ m₁ : ↥(MMsharp H t₁), ∃ w : ↥(H.W0 t₁.f t₁.f'), (m₁ : V) + w ∈ t₁.abelian₂)
    (g₁ g₂ : Fin (r + 1) → V)
    (hY₂ : H.X g₂ ≤ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')))
    (hW₁ : H.W0 t₁.f t₁.f' ≤ H.perp (H.X g₁)) (hW₂ : H.W0 t₂.f t₂.f' ≤ H.perp (H.X g₂))
    (χ : H.Wb g₁ ≃ₗ[E] H.Wb g₂)
    (hC1 : ∀ w : ↥(H.W0 t₁.f t₁.f'), χ (H.mkW g₁ ⟨w, hW₁ w.2⟩) = H.mkW g₂ ⟨ψ w, hW₂ (ψ w).2⟩)
    (hC2 : ∀ u ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f')), ∀ hu : u ∈ H.perp (H.X g₁),
      ∃ u' ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')), ∃ hu' : u' ∈ H.perp (H.X g₂),
        χ (H.mkW g₁ ⟨u, hu⟩) = H.mkW g₂ ⟨u', hu'⟩) :
    χ '' H.Lset t₁.abelian₂ g₁ = H.Lset Λ₂ g₂ ↔
      (fun p => (θ p.1, χ p.2)) '' GamG H t₁ g₁ = GamG H t₂ g₂ := by

  have hsep₂ : ∀ (a b : V) (ha : a ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')))
      (hb : b ∈ H.W0 t₂.f t₂.f') (ha' : a ∈ H.perp (H.X g₂)),
      H.mkW g₂ ⟨a, ha'⟩ = H.mkW g₂ ⟨b, hW₂ hb⟩ → b = 0 := by
    intro a b ha hb ha' hab
    have h1 := sub_mem_X_of_mkW_eq H hab
    have h2 : b = a - (a - b) := by abel
    have h3 : b ∈ Submodule.span E (Set.range (Sum.elim t₂.f t₂.f')) := by
      rw [h2]; exact Submodule.sub_mem _ ha (hY₂ h1)
    exact (Submodule.disjoint_def.1 hU₂.disjoint) b h3 hb
  have hpart : ∀ (t : Term V M r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → MMo H t ≤ Λ →
      ∀ a b : V, a ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) → b ∈ H.W0 t.f t.f' → a + b ∈ Λ →
        a ∈ MMsharp H t := by
    intro t Λ hsd hMM a b ha hb hab
    refine ⟨span_frames_le_MM H t ha, fun μ hμ => ?_⟩
    have hμU : μ ∈ Submodule.span E (Set.range (H.MMfam t)) := Submodule.span_le_restrictScalars M.L.O E _ hμ
    have h1 : H.h (a + b) μ ∈ M.L.O := (hsd.2.2 _).1 hab μ (hMM hμ)
    rw [H.h_add_left, hermitian_W0_span_zero H t hb hμU, add_zero] at h1
    exact h1
  have hdec : ∀ (U W : Submodule E V), IsCompl U W → ∀ x : V, ∃ a ∈ U, ∃ b ∈ W, a + b = x := by
    intro U W hUW x
    have hx : x ∈ U ⊔ W := by rw [hUW.sup_eq_top]; exact Submodule.mem_top
    exact Submodule.mem_sup.1 hx
  have hperp_a : ∀ {g : Fin (r + 1) → V} (a b : V), b ∈ H.perp (H.X g) → a + b ∈ H.perp (H.X g) →
      a ∈ H.perp (H.X g) := by
    intro g a b hb hab
    have : a = (a + b) - b := by abel
    rw [this]
    exact Submodule.sub_mem _ hab hb

  have hθs : ∀ m₂ : ↥(MMsharp H t₂), ∃ m₁ : ↥(MMsharp H t₁), θ (ddMk H t₁ m₁) = ddMk H t₂ m₂ := by
    intro m₂
    obtain ⟨m₁, hm₁⟩ := Submodule.Quotient.mk_surjective _ (θ.symm (ddMk H t₂ m₂))
    refine ⟨m₁, ?_⟩
    rw [show ddMk H t₁ m₁ = θ.symm (ddMk H t₂ m₂) from hm₁, LinearEquiv.apply_symm_apply]
  constructor
  · intro hL
    apply Set.Subset.antisymm
    · rintro _ ⟨q, ⟨u₁, hu₁, rfl⟩, rfl⟩
      obtain ⟨n₁, hn₁⟩ := hsurj₁ u₁
      have hx₁p : (u₁ : V) + n₁ ∈ H.perp (H.X g₁) := Submodule.add_mem _ hu₁ (hW₁ n₁.2)
      have hmem : χ (H.mkW g₁ ⟨(u₁ : V) + n₁, hx₁p⟩) ∈ H.Lset Λ₂ g₂ := by
        rw [← hL]
        exact ⟨_, ⟨⟨_, hx₁p⟩, hn₁, rfl⟩, rfl⟩
      obtain ⟨x₂, hx₂Λ, hx₂e⟩ := hmem
      obtain ⟨a, ha, b, hb, hab⟩ := hdec _ _ hU₂ (x₂ : V)
      have hap : a ∈ H.perp (H.X g₂) := hperp_a a b (hW₂ hb) (by rw [hab]; exact x₂.2)
      have haMM : a ∈ MMsharp H t₂ := hpart t₂ Λ₂ hsd₂ hMM₂ a b ha hb (by rw [hab]; exact hx₂Λ)
      obtain ⟨u', hu'U, hu'p, hχu⟩ := hC2 u₁ (spanMM_le_U H t₁ u₁.2.1) hu₁
      have e1 : χ (H.mkW g₁ ⟨(u₁ : V) + n₁, hx₁p⟩) = H.mkW g₂ ⟨u', hu'p⟩ + H.mkW g₂ ⟨ψ n₁, hW₂ (ψ n₁).2⟩ := by
        rw [mkW_add H _ _ hu₁ (hW₁ n₁.2), map_add, hχu, hC1]
      have e2 : H.mkW g₂ x₂ = H.mkW g₂ ⟨a, hap⟩ + H.mkW g₂ ⟨b, hW₂ hb⟩ := by
        rw [← mkW_add H _ _ hap (hW₂ hb)]
        exact mkW_congr H _ _ hab.symm
      have e3 : H.mkW g₂ ⟨a - u', Submodule.sub_mem _ hap hu'p⟩ =
          H.mkW g₂ ⟨(ψ n₁ : V) - b, Submodule.sub_mem _ (hW₂ (ψ n₁).2) (hW₂ hb)⟩ := by
        rw [mkW_sub H a u' hap hu'p, mkW_sub H (ψ n₁ : V) b (hW₂ (ψ n₁).2) (hW₂ hb), sub_eq_sub_iff_add_eq_add,
          ← e2, hx₂e, e1, add_comm]
      have hb0 := hsep₂ (a - u') ((ψ n₁ : V) - b) (Submodule.sub_mem _ ha hu'U)
        (Submodule.sub_mem _ (ψ n₁).2 hb) (Submodule.sub_mem _ hap hu'p) e3
      have hbψ : b = (ψ n₁ : V) := (sub_eq_zero.1 hb0).symm
      have e4 : H.mkW g₂ ⟨a, hap⟩ = H.mkW g₂ ⟨u', hu'p⟩ := by
        have := e3
        rw [mkW_sub H a u' hap hu'p, mkW_sub H (ψ n₁ : V) b (hW₂ (ψ n₁).2) (hW₂ hb)] at this
        rw [mkW_congr H (hW₂ (ψ n₁).2) (hW₂ hb) hbψ.symm, sub_self, sub_eq_zero] at this
        exact this
      have hθu : θ (ddMk H t₁ u₁) = ddMk H t₂ ⟨a, haMM⟩ :=
        (hθ u₁ ⟨a, haMM⟩).2 ⟨n₁, hn₁, by rw [← hbψ, hab]; exact hx₂Λ⟩
      refine ⟨⟨a, haMM⟩, hap, ?_⟩
      simp only [Prod.mk.injEq]
      exact ⟨hθu, hχu.trans e4.symm⟩
    · rintro _ ⟨u₂, hu₂, rfl⟩
      obtain ⟨m₁, hm₁⟩ := hθs u₂
      obtain ⟨n₁, hn₁, hx₂Λ⟩ := (hθ m₁ u₂).1 hm₁
      have hx₂p : (u₂ : V) + ψ n₁ ∈ H.perp (H.X g₂) := Submodule.add_mem _ hu₂ (hW₂ (ψ n₁).2)
      have hmem : H.mkW g₂ ⟨(u₂ : V) + ψ n₁, hx₂p⟩ ∈ χ '' H.Lset t₁.abelian₂ g₁ := by
        rw [hL]
        exact ⟨⟨_, hx₂p⟩, hx₂Λ, rfl⟩
      obtain ⟨_, ⟨x₁, hx₁Λ, rfl⟩, hx₁e⟩ := hmem
      obtain ⟨a₁, ha₁, b₁, hb₁, hab₁⟩ := hdec _ _ hU₁ (x₁ : V)
      have ha₁p : a₁ ∈ H.perp (H.X g₁) := hperp_a a₁ b₁ (hW₁ hb₁) (by rw [hab₁]; exact x₁.2)
      have ha₁MM : a₁ ∈ MMsharp H t₁ := hpart t₁ t₁.abelian₂ hsd₁ hMM₁ a₁ b₁ ha₁ hb₁ (by rw [hab₁]; exact hx₁Λ)
      obtain ⟨u', hu'U, hu'p, hχu⟩ := hC2 a₁ ha₁ ha₁p
      have e1 : χ (H.mkW g₁ x₁) = H.mkW g₂ ⟨u', hu'p⟩ + H.mkW g₂ ⟨ψ ⟨b₁, hb₁⟩, hW₂ (ψ ⟨b₁, hb₁⟩).2⟩ := by
        rw [mkW_congr H x₁.2 (Submodule.add_mem _ ha₁p (hW₁ hb₁)) hab₁.symm, mkW_add H _ _ ha₁p (hW₁ hb₁),
          map_add, hχu]
        rw [← hC1 ⟨b₁, hb₁⟩]
      have e3 : H.mkW g₂ ⟨(u₂ : V) - u', Submodule.sub_mem _ hu₂ hu'p⟩ =
          H.mkW g₂ ⟨(ψ ⟨b₁, hb₁⟩ : V) - ψ n₁, Submodule.sub_mem _ (hW₂ (ψ ⟨b₁, hb₁⟩).2) (hW₂ (ψ n₁).2)⟩ := by
        rw [mkW_sub H (u₂ : V) u' hu₂ hu'p,
          mkW_sub H (ψ ⟨b₁, hb₁⟩ : V) (ψ n₁ : V) (hW₂ (ψ ⟨b₁, hb₁⟩).2) (hW₂ (ψ n₁).2),
          sub_eq_sub_iff_add_eq_add, ← mkW_add H _ _ hu₂ (hW₂ (ψ n₁).2), ← hx₁e, e1, add_comm]
      have hb0 := hsep₂ ((u₂ : V) - u') ((ψ ⟨b₁, hb₁⟩ : V) - ψ n₁)
        (Submodule.sub_mem _ (spanMM_le_U H t₂ u₂.2.1) hu'U)
        (Submodule.sub_mem _ (ψ ⟨b₁, hb₁⟩).2 (ψ n₁).2) (Submodule.sub_mem _ hu₂ hu'p) e3
      have hψeq : ψ ⟨b₁, hb₁⟩ = ψ n₁ := Subtype.ext (sub_eq_zero.1 hb0)
      have hbn : (⟨b₁, hb₁⟩ : ↥(H.W0 t₁.f t₁.f')) = n₁ := ψ.injective hψeq
      have e4 : H.mkW g₂ ⟨u₂, hu₂⟩ = H.mkW g₂ ⟨u', hu'p⟩ := by
        have := e3
        rw [mkW_sub H (u₂ : V) u' hu₂ hu'p,
          mkW_sub H (ψ ⟨b₁, hb₁⟩ : V) (ψ n₁ : V) (hW₂ (ψ ⟨b₁, hb₁⟩).2) (hW₂ (ψ n₁).2)] at this
        rw [mkW_congr H (hW₂ (ψ ⟨b₁, hb₁⟩).2) (hW₂ (ψ n₁).2) (congrArg Subtype.val hψeq), sub_self,
          sub_eq_zero] at this
        exact this
      have hθa : θ (ddMk H t₁ ⟨a₁, ha₁MM⟩) = ddMk H t₂ u₂ :=
        (hθ ⟨a₁, ha₁MM⟩ u₂).2 ⟨⟨b₁, hb₁⟩, by rw [hab₁]; exact hx₁Λ, by rw [hψeq]; exact hx₂Λ⟩
      refine ⟨(ddMk H t₁ ⟨a₁, ha₁MM⟩, H.mkW g₁ ⟨a₁, ha₁p⟩), ⟨⟨a₁, ha₁MM⟩, ha₁p, rfl⟩, ?_⟩
      simp only [Prod.mk.injEq]
      exact ⟨hθa, hχu.trans e4.symm⟩
  · intro hG
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨x₁, hx₁Λ, rfl⟩, rfl⟩
      obtain ⟨a₁, ha₁, b₁, hb₁, hab₁⟩ := hdec _ _ hU₁ (x₁ : V)
      have ha₁p : a₁ ∈ H.perp (H.X g₁) := hperp_a a₁ b₁ (hW₁ hb₁) (by rw [hab₁]; exact x₁.2)
      have ha₁MM : a₁ ∈ MMsharp H t₁ := hpart t₁ t₁.abelian₂ hsd₁ hMM₁ a₁ b₁ ha₁ hb₁ (by rw [hab₁]; exact hx₁Λ)
      have hin : (θ (ddMk H t₁ ⟨a₁, ha₁MM⟩), χ (H.mkW g₁ ⟨a₁, ha₁p⟩)) ∈ GamG H t₂ g₂ := by
        rw [← hG]
        exact ⟨_, ⟨⟨a₁, ha₁MM⟩, ha₁p, rfl⟩, rfl⟩
      obtain ⟨u₂, hu₂, hue⟩ := hin
      simp only [Prod.mk.injEq] at hue
      obtain ⟨n₁, hn₁, hx₂'⟩ := (hθ ⟨a₁, ha₁MM⟩ u₂).1 hue.1
      have hd : (⟨b₁, hb₁⟩ : ↥(H.W0 t₁.f t₁.f')) - n₁ ∈ {w : ↥(H.W0 t₁.f t₁.f') | (w : V) ∈ t₁.abelian₂} := by
        show b₁ - (n₁ : V) ∈ t₁.abelian₂
        have := t₁.abelian₂.sub_mem hx₁Λ hn₁
        rwa [← hab₁, show a₁ + b₁ - (a₁ + (n₁ : V)) = b₁ - n₁ by abel] at this
      have hdψ := (hth _).1 hd
      rw [map_sub, Submodule.coe_sub] at hdψ
      have hx₂Λ : (u₂ : V) + ψ ⟨b₁, hb₁⟩ ∈ Λ₂ := by
        have := Λ₂.add_mem hx₂' hdψ
        rwa [show (u₂ : V) + ψ n₁ + ((ψ ⟨b₁, hb₁⟩ : V) - ψ n₁) = u₂ + ψ ⟨b₁, hb₁⟩ by abel] at this
      have hx₂p : (u₂ : V) + ψ ⟨b₁, hb₁⟩ ∈ H.perp (H.X g₂) := Submodule.add_mem _ hu₂ (hW₂ (ψ ⟨b₁, hb₁⟩).2)
      refine ⟨⟨_, hx₂p⟩, hx₂Λ, ?_⟩
      rw [mkW_add H _ _ hu₂ (hW₂ (ψ ⟨b₁, hb₁⟩).2), ← hC1 ⟨b₁, hb₁⟩, ← hue.2, ← map_add,
        ← mkW_add H _ _ ha₁p (hW₁ hb₁)]
      exact congrArg χ (mkW_congr H _ _ hab₁)
    · rintro _ ⟨x₂, hx₂Λ, rfl⟩
      obtain ⟨a, ha, b, hb, hab⟩ := hdec _ _ hU₂ (x₂ : V)
      have hap : a ∈ H.perp (H.X g₂) := hperp_a a b (hW₂ hb) (by rw [hab]; exact x₂.2)
      have haMM : a ∈ MMsharp H t₂ := hpart t₂ Λ₂ hsd₂ hMM₂ a b ha hb (by rw [hab]; exact hx₂Λ)
      have hin : (ddMk H t₂ ⟨a, haMM⟩, H.mkW g₂ ⟨a, hap⟩) ∈
          (fun p => (θ p.1, χ p.2)) '' GamG H t₁ g₁ := by
        rw [hG]
        exact ⟨⟨a, haMM⟩, hap, rfl⟩
      obtain ⟨_, ⟨u₁, hu₁, rfl⟩, hue⟩ := hin
      simp only [Prod.mk.injEq] at hue
      obtain ⟨n₁, hn₁, hx₂'⟩ := (hθ u₁ ⟨a, haMM⟩).1 hue.1
      set bb : ↥(H.W0 t₁.f t₁.f') := ψ.symm ⟨b, hb⟩
      have hψbb : (ψ bb : V) = b := by simp [bb]
      have hd2 : (ψ (bb - n₁) : V) ∈ Λ₂ := by
        rw [map_sub, Submodule.coe_sub, hψbb]
        have := Λ₂.sub_mem hx₂Λ hx₂'
        rwa [← hab, show a + b - (a + (ψ n₁ : V)) = b - ψ n₁ by abel] at this
      have hd1 : ((bb - n₁ : ↥(H.W0 t₁.f t₁.f')) : V) ∈ t₁.abelian₂ := (hth _).2 hd2
      have hx₁Λ : (u₁ : V) + bb ∈ t₁.abelian₂ := by
        have := t₁.abelian₂.add_mem hn₁ hd1
        rwa [Submodule.coe_sub, show (u₁ : V) + n₁ + ((bb : V) - n₁) = u₁ + bb by abel] at this
      have hx₁p : (u₁ : V) + bb ∈ H.perp (H.X g₁) := Submodule.add_mem _ hu₁ (hW₁ bb.2)
      refine ⟨_, ⟨⟨_, hx₁p⟩, hx₁Λ, rfl⟩, ?_⟩
      rw [mkW_add H _ _ hu₁ (hW₁ bb.2), map_add, hue.2, hC1]
      rw [← mkW_add H _ _ hap (hW₂ (ψ bb).2)]
      exact mkW_congr H _ _ (by rw [hψbb, hab])

end CR

end Formalism.L2.SG.LsDatumA
