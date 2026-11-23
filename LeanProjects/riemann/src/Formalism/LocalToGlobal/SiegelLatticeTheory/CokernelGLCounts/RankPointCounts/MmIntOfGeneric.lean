import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGlueCut

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section G3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def GlueFwd (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    ∀ Λ₂ : Submodule M.L.O V, H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ →
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' →
    ∃ θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩, IsomD H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ θ ∧
      ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H _ m₂ ↔ GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' m₁ m₂

def GlueBack (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    IsUnit (H.Dl f₂ f₂' (r + 1)) → MMInt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ →
    ∀ θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩, IsomD H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ θ →
    ∃ Λ₂ : Submodule M.L.O V, H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ ∧
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' ∧
      ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H _ m₂ ↔ GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' m₁ m₂

def GlueInj (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    ∀ Λ₂ Λ₂' : Submodule M.L.O V, H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ →
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' → H.IsGeneric ⟨Λ₂', f₂, f₂', t₁.T, t₁.T'⟩ →
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂' φ φ' →
      (∀ m₁ m₂, GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' m₁ m₂ ↔
        GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂' φ φ' m₁ m₂) → Λ₂ = Λ₂'

theorem mmInt_of_generic {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (Λ₂ : Submodule M.L.O V) (f₂ f₂' : Fin (r + 1) → V) (T T' : F)
    (hg : H.IsGeneric ⟨Λ₂, f₂, f₂', T, T'⟩) : MMInt H (⟨⊥, f₂, f₂', T, T'⟩ : Term V M r) := by
  have hsub : MMo H (⟨⊥, f₂, f₂', T, T'⟩ : Term V M r) ≤ Λ₂ := by
    refine (Submodule.span_le (R := M.L.O)).2 ?_
    rintro _ ⟨a, rfl⟩
    exact hg.2.1 a
  intro m hm m' hm'
  exact (hg.1.1.2.2 m).1 (hsub hm) m' (hsub hm')

theorem dd_ext {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    {t₁ t₂ : Term V M r} (θ θ' : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂)
    (h : ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H t₂ m₂ ↔ θ' (ddMk H t₁ m₁) = ddMk H t₂ m₂) : θ = θ' := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨m₁, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨m₂, hm₂⟩ := Submodule.Quotient.mk_surjective _ (θ (Submodule.Quotient.mk m₁))
  have h₁ : θ (ddMk H t₁ m₁) = ddMk H t₂ m₂ := hm₂.symm
  exact h₁.trans ((h m₁ m₂).1 h₁).symm

theorem glue_of (M : Model F E) (r n : ℕ) (hF : GlueFwd M r n) (hB : GlueBack M r n) (hI : GlueInj M r n) :
    Glue M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hyp
  have fw := hF V H hn t₁ f₂ f₂' φ φ' hyp
  have bk := hB V H hn t₁ f₂ f₂' φ φ' hyp
  have inj := hI V H hn t₁ f₂ f₂' φ φ' hyp
  let toθ : {Λ₂ : Submodule M.L.O V // H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ ∧
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ'} →
      {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ //
        IsUnit (H.Dl f₂ f₂' (r + 1)) ∧ MMInt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ ∧
          IsomD H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ θ} :=
    fun x => ⟨(fw x.1 x.2.1 x.2.2).choose, x.2.1.1.2.2.2.1, mmInt_of_generic H x.1 f₂ f₂' t₁.T t₁.T' x.2.1,
      (fw x.1 x.2.1 x.2.2).choose_spec.1⟩
  have toθ_spec : ∀ x m₁ m₂, (toθ x).1 (ddMk H t₁ m₁) = ddMk H _ m₂ ↔
      GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ x.1 φ φ' m₁ m₂ :=
    fun x => (fw x.1 x.2.1 x.2.2).choose_spec.2
  have hinj : Function.Injective toθ := by
    intro x y hxy
    apply Subtype.ext
    refine inj x.1 y.1 x.2.1 x.2.2 y.2.1 y.2.2 fun m₁ m₂ => ?_
    rw [← toθ_spec x, ← toθ_spec y, hxy]
  have hsurj : Function.Surjective toθ := by
    intro θ
    obtain ⟨Λ₂, hg, hth, hrel⟩ := bk θ.2.1 θ.2.2.1 θ.1 θ.2.2.2
    refine ⟨⟨Λ₂, hg, hth⟩, Subtype.ext (dd_ext H _ _ fun m₁ m₂ => ?_)⟩
    rw [toθ_spec, hrel]
  exact ⟨Equiv.ofBijective toθ ⟨hinj, hsurj⟩, toθ_spec⟩

end G3

end Formalism.L2.SG.LsDatumA
