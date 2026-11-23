import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv

noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.MultiIrr ValuativeRel Matrix
open scoped TensorProduct

namespace UpperTheory.Lit.Mix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

variable (k) in

def TwoAt : Prop :=
  ∀ (r t : ℕ) (V W : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W),
    IsSmooth π₁ → π₁.IsIrreducible → IsUnitarisable π₁ → IsSmooth π₂ → π₂.IsIrreducible → IsUnitarisable π₂ →
    (prod₂ π₁ π₂).IsIrreducible

theorem ind₂_at (H : TwoAt k) (e : a ⊕ b ≃ n)
    {π₁ : Representation ℂ (GL a k) V} {π₂ : Representation ℂ (GL b k) W}
    (s₁ : IsSmooth π₁) (i₁ : π₁.IsIrreducible) (u₁ : IsUnitarisable π₁)
    (s₂ : IsSmooth π₂) (i₂ : π₂.IsIrreducible) (u₂ : IsUnitarisable π₂) :
    (ind₂ e (extTensor π₁ π₂)).IsIrreducible := by
  classical
  let ea := Fintype.equivFin a
  let eb := Fintype.equivFin b
  let f₁ : GL (Fin (Fintype.card a)) k →* GL a k := (relabel k ea).symm.toMonoidHom
  let f₂ : GL (Fin (Fintype.card b)) k →* GL b k := (relabel k eb).symm.toMonoidHom
  have c₁ : Continuous f₁ := continuous_relabel ea.symm
  have c₂ : Continuous f₂ := continuous_relabel eb.symm
  have i₁' : Representation.IsIrreducible (π₁.comp f₁ : Representation ℂ _ V) := by
    refine (isIrreducible_iff_of_linearEquiv (ρ := π₁) (σ := π₁.comp f₁) (relabel k ea)
      (relabel k ea).surjective (LinearEquiv.refl ℂ V) ?_).mp i₁
    intro g v
    simp [f₁]
  have i₂' : Representation.IsIrreducible (π₂.comp f₂ : Representation ℂ _ W) := by
    refine (isIrreducible_iff_of_linearEquiv (ρ := π₂) (σ := π₂.comp f₂) (relabel k eb)
      (relabel k eb).surjective (LinearEquiv.refl ℂ W) ?_).mp i₂
    intro g v
    simp [f₂]
  have h := H _ _ V W (π₁.comp f₁) (π₂.comp f₂) (isSmooth_comp s₁ f₁ c₁) i₁'
    (UnitInd.isUnitarisable_comp u₁ f₁) (isSmooth_comp s₂ f₂ c₂) i₂' (UnitInd.isUnitarisable_comp u₂ f₂)
  unfold prod₂ at h
  refine (isIrreducible_ind₂_iff e _ ea eb (LinearEquiv.refl ℂ _) ?_).mpr h
  intro g v
  simp [extTensor, f₁, f₂]

theorem multiProd_at (H : TwoAt k) {s : ℕ} :
    ∀ {m : Fin s → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {n : Type} [Fintype n] [DecidableEq n]
    (e : (Σ i, m i) ≃ n) {X : Fin s → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    {σ : ∀ i, Representation ℂ (GL (m i) k) (X i)}, (∀ i, IsSmooth (σ i)) → (∀ i, (σ i).IsIrreducible) →
    (∀ i, IsUnitarisable (σ i)) → (multiProd e σ).IsIrreducible := by
  induction s with
  | zero => exact fun e _ _ _ σ _ _ _ => isIrreducible_multiProd_zero e σ
  | succ s ih =>
    intro m _ _ n _ _ e X _ _ σ hs hi hu
    obtain ⟨E⟩ := multiProd_succ_equiv e σ
    exact (isIrreducible_iff_of_equiv E).1 (ind₂_at H _ (hs 0) (hi 0) (hu 0) (isSmooth_parInd _ _)
      (ih _ (fun i => hs i.succ) (fun i => hi i.succ) fun i => hu i.succ)
      (UnitInd.isUnitarisable_multiProd _ fun i => hu i.succ))

end UpperTheory.Lit.Mix

end
