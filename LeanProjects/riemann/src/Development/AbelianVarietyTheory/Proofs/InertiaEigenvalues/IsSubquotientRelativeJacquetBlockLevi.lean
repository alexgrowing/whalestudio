import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSubquotientOfEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacStages GlobalTheory.InertSupp

namespace GlobalTheory.JacStagesExact

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {s : ℕ} {d : Fin s → ℕ} {t : Fin s → ℕ} {d' : ∀ a, Fin (t a) → ℕ}
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def relJacMap (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    {σ : Representation ℂ (Levi k fun a => Fin (d a)) V}
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) W} (f : σ.IntertwiningMap τ) :
    (relJacD e' σ).IntertwiningMap (relJacD e' τ) :=
  twistMap (jacquetMap f _ _ _) _

theorem relJacMap_surjective (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    {σ : Representation ℂ (Levi k fun a => Fin (d a)) V}
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) W} (f : σ.IntertwiningMap τ)
    (hf : Function.Surjective f) : Function.Surjective (relJacMap e' f) := fun y => by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨v, rfl⟩ := hf w
  exact ⟨Submodule.Quotient.mk v, rfl⟩

theorem relJacMap_injective (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    {σ : Representation ℂ (Levi k fun a => Fin (d a)) V}
    {τ : Representation ℂ (Levi k fun a => Fin (d a)) W} (hτ : IsSmooth τ) (f : σ.IntertwiningMap τ)
    (hf : Function.Injective f) : Function.Injective (relJacMap e' f) := by
  classical
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have h1 : f v ∈ twKer τ (relUnipD k e') 1 := (Submodule.Quotient.mk_eq_zero _).1 hx
  obtain ⟨S, hS, h2⟩ := GlobalTheory.JacquetExact.exists_finset_of_mem_twKer h1
  have hH : ∀ a, ∃ H : Subgroup (GL (Fin (d a)) k), H ≤ unipRad k (e' a) ∧
      IsCompact (H : Set (GL (Fin (d a)) k)) ∧ ∀ u ∈ S, u a ∈ H := by
    intro a
    have hN : unipRad k (e' a) = unipOf k fun i => ((blk (e' a) i).val : ℤ) :=
      unipRad_eq_unipOf k fun i j => by simp
    obtain ⟨H, hle, hc, hSH⟩ := GlobalTheory.UnipCompact.exists_compact_subgroup k (Fin (d a)) _
      (S.image fun u => u a) (by
        intro u hu
        obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hu
        have hm : u' a ∈ unipRad k (e' a) := hS u' hu' a (Set.mem_univ a)
        exact hN ▸ hm)
    exact ⟨H, hle.trans hN.ge, hc, fun u hu => hSH _ (Finset.mem_image_of_mem _ hu)⟩
  choose H hle hc hSH using hH
  let H' : Subgroup (Levi k fun a => Fin (d a)) := Subgroup.pi Set.univ H
  have hc' : IsCompact (H' : Set (Levi k fun a => Fin (d a))) := by
    have : (H' : Set (Levi k fun a => Fin (d a))) = Set.pi Set.univ fun a => (H a : Set _) := rfl
    rw [this]
    exact isCompact_univ_pi hc
  have hle' : H' ≤ relUnipD k e' := fun u hu a _ => hle a (hu a (Set.mem_univ a))
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  exact GlobalTheory.IwahoriInj.twKer_mono hle'
    (GlobalTheory.JacquetExact.mem_twKer_of_compact hτ f hf hc' (h2 H' fun u hu a _ => hSH a u hu))

theorem isSubquotient_relJacD : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s : ℕ) (d : Fin s → ℕ) (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (V W : Type) [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (Levi k fun a => Fin (d a)) V)
    (τ : Representation ℂ (Levi k fun a => Fin (d a)) W),
    IsSmooth τ → IsSubquotient σ τ → IsSubquotient (relJacD e' σ) (relJacD e' τ) := by
  intro k _ _ _ _ s d t d' e' V W _ _ _ _ σ τ hτ h
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap τ := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  exact (IsSubquotient.of_surjective _ (relJacMap_surjective e' f hf)).trans
    (.of_injective _ (relJacMap_injective e' hτ ι Subtype.val_injective))

end GlobalTheory.JacStagesExact
