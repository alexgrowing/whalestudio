import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NontrivialOfNeBot
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology

namespace GlobalTheory.FrameAut.VecForms

theorem isAutRepU_span_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S), Submodule.span ℂ (Set.range ρ) = ⊤ → ∀ M : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)), M ≠ ⊥ → (∀ f ∈ M, (∀ v, IsAutFormU (f v)) ∧ ∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) → (∀ k ∈ finU E n, ∀ f ∈ M, (RU E n k) ∘ₗ f ∈ M) → (∀ N ≤ M, (∀ k ∈ finU E n, ∀ f ∈ N, (RU E n k) ∘ₗ f ∈ N) → N = ⊥ ∨ N = M) → IsAutRepU (Submodule.span ℂ {φ | ∃ f ∈ M, ∃ v, f v = φ}) := by
  intro E _ _ _ n S _ _ _ ρ hsp M hM0 hf hk hirr
  let j : M →ₗ[ℂ] S →ₗ[ℂ] (UA E n → ℂ) := M.subtype
  have himg : Submodule.span ℂ {φ | ∃ f ∈ M, ∃ v, f v = φ} = GlobalTheory.DefU.Pairs.img j := by
    unfold GlobalTheory.DefU.Pairs.img
    congr 1
    ext φ
    constructor
    · rintro ⟨f, hf, v, rfl⟩
      exact ⟨⟨f, hf⟩, v, rfl⟩
    · rintro ⟨p, v, rfl⟩
      exact ⟨p.1, p.2, v, rfl⟩
  rw [himg]
  have hj : ∀ (p : M) (x : infU E n) (v : S), j p (ρ x v) = RU E n x.1 (j p v) := fun p x v => (hf p.1 p.2).2 x v
  have hstab : ∀ x, ∀ φ ∈ GlobalTheory.DefU.Pairs.img j, RU E n x φ ∈ GlobalTheory.DefU.Pairs.img j := by
    intro x φ hφ
    refine GlobalTheory.DefU.Pairs.stable_of (fun a => ?_) (fun k => ?_) x φ hφ
    · have h1 : GlobalTheory.DefU.Pairs.img j ≤ (GlobalTheory.DefU.Pairs.img j).comap (RU E n a.1) := Submodule.span_le.2 (by
        rintro _ ⟨p, v, rfl⟩
        change RU E n a.1 _ ∈ GlobalTheory.DefU.Pairs.img j
        rw [← hj]
        exact GlobalTheory.DefU.Pairs.apply_mem_img _ _ _)
      exact fun φ hφ => h1 hφ
    · have h1 : GlobalTheory.DefU.Pairs.img j ≤ (GlobalTheory.DefU.Pairs.img j).comap (RU E n k.1) := Submodule.span_le.2 (by
        rintro _ ⟨p, v, rfl⟩
        exact GlobalTheory.DefU.Pairs.apply_mem_img j ⟨(RU E n k.1) ∘ₗ p.1, hk k k.2 p.1 p.2⟩ v)
      exact fun φ hφ => h1 hφ
  have hne : GlobalTheory.DefU.Pairs.img j ≠ ⊥ := by
    obtain ⟨f, hfM, h0⟩ := (Submodule.ne_bot_iff _).1 hM0
    obtain ⟨v, hv⟩ := DFunLike.ne_iff.1 h0
    intro e
    have := GlobalTheory.DefU.Pairs.apply_mem_img j ⟨f, hfM⟩ v
    rw [e, Submodule.mem_bot] at this
    exact hv this
  let Q : finU E n → Module.End ℂ M := fun k =>
    ((LinearMap.llcomp ℂ S (UA E n → ℂ) (UA E n → ℂ) (RU E n k.1)) ∘ₗ M.subtype).codRestrict M
      (fun p => hk k k.2 p.1 p.2)
  have hP : ∀ N : Submodule ℂ M, (∀ k, ∀ p ∈ N, Q k p ∈ N) → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    have hst : ∀ k ∈ finU E n, ∀ f ∈ N.map M.subtype, (RU E n k) ∘ₗ f ∈ N.map M.subtype := by
      rintro k hkk _ ⟨p, hp, rfl⟩
      exact ⟨Q ⟨k, hkk⟩ p, hN ⟨k, hkk⟩ p hp, rfl⟩
    have hc : N = (N.map M.subtype).comap M.subtype :=
      (Submodule.comap_map_eq_of_injective M.injective_subtype N).symm
    rcases hirr _ (Submodule.map_subtype_le M N) hst with h | h
    · left
      rw [hc, h, Submodule.comap_bot, Submodule.ker_subtype]
    · right
      rw [hc, h, Submodule.comap_subtype_self]
  refine ⟨fun φ hφ => ?_, hstab, hne, fun U hle hU => ?_⟩
  · have h1 : GlobalTheory.DefU.Pairs.img j ≤ autU E n := Submodule.span_le.2 (by
      rintro _ ⟨p, v, rfl⟩
      exact (hf p.1 p.2).1 v)
    exact h1 hφ
  · exact GlobalTheory.DefU.Pairs.eq_bot_or_eq_img hsp (R := fun x => RU E n x.1) hj
      (Q := Q) (T := fun k => RU E n k.1) (fun _ _ _ => rfl) hP hle
      (fun x => hU x.1) (fun k => hU k.1)

end GlobalTheory.FrameAut.VecForms
