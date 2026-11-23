import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterEigenspaceIsComplPrincipalSeriesTwistedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EigEqZeroOfMemAugOfNotIntertwineStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsEigTranslateOfSubMemAugStatement

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem map_mem_aug_of_conj {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    (A B : Set G) (z : G) (h : ∀ y ∈ B, z * y * z⁻¹ ∈ A) (u : V) (hu : u ∈ aug π B (fun _ => 1)) :
    π z u ∈ aug π A (fun _ => 1) := by
  have hle : aug π B (fun _ => 1) ≤ (aug π A (fun _ => 1)).comap (π z) := by
    unfold aug
    refine Submodule.span_le.2 ?_
    rintro x ⟨y, hy, w, rfl⟩
    refine Submodule.subset_span ⟨z * y * z⁻¹, h y hy, π z w, ?_⟩
    have e : π (z * y * z⁻¹) (π z w) = π z (π y w) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      simp
    rw [e, map_sub, map_smul]
  exact hle hu

theorem aug_mono_set {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)
    {A B : Set G} (θ : G → ℂ) (h : A ⊆ B) : aug π A θ ≤ aug π B θ := by
  unfold aug
  refine Submodule.span_mono ?_
  rintro x ⟨y, hy, w, rfl⟩
  exact ⟨y, h hy, w, rfl⟩

theorem eig_eq_zero_of_mem_aug_chain : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (J : Set G) (N : ℕ → Set G) (θ : G → ℂ) (z : G), Datum J θ → (∀ m, Datum (N m) (fun _ => 1)) → Monotone N → (∀ y ∈ N 0, y ∈ J ∧ θ y = 1) → (∀ m y, y ∈ N (m + 1) ↔ z * y * z⁻¹ ∈ N m) → (∀ y ∈ N 1, (y ∈ J ∧ θ y = 1) ∨ ∃ j ∈ J, y * j * y⁻¹ ∈ J ∧ θ j ≠ θ (y * j * y⁻¹)) → (∀ j ∈ J, ∃ y ∈ N 0, z⁻¹ * (y⁻¹ * j) * z ∈ J ∧ θ (z⁻¹ * (y⁻¹ * j) * z) = θ j) → ∀ (m : ℕ) (u : V), u ∈ aug π (N m) (fun _ => 1) → IsEig π J θ u → u = 0 := by
  intro G V _ _ _ _ _ π hπ J N θ z hJ hN hmono h0 hconj h1 hz m
  induction m with
  | zero =>
    intro u hu heig
    refine (GlobalTheory.T.characterEigenspace_isCompl_principalSeriesTwistedSpan G V π hπ (N 0) (fun _ => 1) (hN 0)).1 u hu ?_
    intro y hy
    rw [heig y (h0 y hy).1, (h0 y hy).2]
  | succ m ih =>
    intro u hu heig
    obtain ⟨u', hu'eig, hsub⟩ := (GlobalTheory.T.characterEigenspace_isCompl_principalSeriesTwistedSpan G V π hπ (N 1) (fun _ => 1) (hN 1)).2 u
    have hsub' : u - u' ∈ aug π (N (m + 1)) (fun _ => 1) :=
      aug_mono_set π _ (hmono (Nat.succ_le_succ (Nat.zero_le m))) hsub
    have hu' : u' ∈ aug π (N (m + 1)) (fun _ => 1) := by
      have := Submodule.sub_mem _ hu hsub'
      simpa using this
    have hzu : π z u' ∈ aug π (N m) (fun _ => 1) :=
      map_mem_aug_of_conj π (N m) (N (m + 1)) z (fun y hy => (hconj m y).1 hy) u' hu'
    have hzeig : IsEig π J θ (π z u') :=
      GlobalTheory.T.isEig_apply_of_sub_mem_aug G V π hπ J (N 0) (N 1) θ z hJ (hN 0) h0 (hconj 0) hz u u' heig hu'eig hsub
    have hz0 : π z u' = 0 := ih _ hzu hzeig
    have hu0 : u' = 0 := by
      have e : π z⁻¹ (π z u') = u' := by
        rw [← Module.End.mul_apply, ← map_mul]
        simp
      rw [← e, hz0, map_zero]
    rw [hu0, sub_zero] at hsub
    exact GlobalTheory.T.eq_zero_of_mem_aug_of_isEig_of_not_intertwine G V π hπ J (N 1) θ hJ (hN 1) h1 u hsub heig

end GlobalTheory.PsType
