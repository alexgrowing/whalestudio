import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor

open Formalism.BasicNotions.TH

namespace GlobalTheory.ExistsHW

open GlobalTheory.TensorHW

section General

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

lemma inf_eig_ne_bot_iff (f : Module.End ℂ V) (N : Submodule ℂ V) (hf : ∀ x ∈ N, f x ∈ N) (t : ℂ) :
    N ⊓ f.eigenspace t ≠ ⊥ ↔ Module.End.HasEigenvalue (f.restrict hf) t := by
  rw [Module.End.hasEigenvalue_iff, Submodule.ne_bot_iff, Submodule.ne_bot_iff]
  constructor
  · rintro ⟨x, ⟨hx1, hx2⟩, hx0⟩
    refine ⟨⟨x, hx1⟩, ?_, fun h => hx0 (congrArg Subtype.val h)⟩
    rw [Module.End.mem_eigenspace_iff]
    exact Subtype.ext (Module.End.mem_eigenspace_iff.1 hx2)
  · rintro ⟨x, hx, hx0⟩
    refine ⟨x, ⟨x.2, ?_⟩, fun h => hx0 (Subtype.ext h)⟩
    rw [Module.End.mem_eigenspace_iff] at hx
    exact Module.End.mem_eigenspace_iff.2 (congrArg Subtype.val hx)

lemma exists_eig (f : Module.End ℂ V) (N : Submodule ℂ V) [FiniteDimensional ℂ N] (hN : N ≠ ⊥)
    (hf : ∀ x ∈ N, f x ∈ N) : ∃ t, N ⊓ f.eigenspace t ≠ ⊥ := by
  haveI : Nontrivial N := Submodule.nontrivial_iff_ne_bot.2 hN
  obtain ⟨t, ht⟩ := Module.End.exists_eigenvalue (f.restrict hf)
  exact ⟨t, (inf_eig_ne_bot_iff f N hf t).2 ht⟩

lemma finite_eig (f : Module.End ℂ V) (N : Submodule ℂ V) [FiniteDimensional ℂ N]
    (hf : ∀ x ∈ N, f x ∈ N) : {t | N ⊓ f.eigenspace t ≠ ⊥}.Finite := by
  simp only [inf_eig_ne_bot_iff f N hf]
  exact Module.End.finite_hasEigenvalue _

lemma exists_common {ι : Type*} (E : ι → Module.End ℂ V) (hE : ∀ a b x, E a (E b x) = E b (E a x))
    (N : Submodule ℂ V) [FiniteDimensional ℂ N] (hN : N ≠ ⊥) (hst : ∀ a, ∀ x ∈ N, E a x ∈ N)
    (s : Finset ι) : ∃ N' : Submodule ℂ V, N' ≤ N ∧ N' ≠ ⊥ ∧ (∀ a, ∀ x ∈ N', E a x ∈ N') ∧
      ∀ a ∈ s, ∃ t, N' ≤ (E a).eigenspace t := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨N, le_rfl, hN, hst, by simp⟩
  | insert b s _ ih =>
    obtain ⟨N', h1, h2, h3, h4⟩ := ih
    haveI : FiniteDimensional ℂ N' := Submodule.finiteDimensional_of_le h1
    obtain ⟨t, ht⟩ := exists_eig (E b) N' h2 (h3 b)
    refine ⟨N' ⊓ (E b).eigenspace t, inf_le_left.trans h1, ht, ?_, ?_⟩
    · rintro a x ⟨hx1, hx2⟩
      refine ⟨h3 a x hx1, Module.End.mem_eigenspace_iff.2 ?_⟩
      rw [hE, Module.End.mem_eigenspace_iff.1 hx2, map_smul]
    · intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact ⟨t, inf_le_right⟩
      · obtain ⟨u, hu⟩ := h4 a ha
        exact ⟨u, inf_le_left.trans hu⟩

end General

lemma eig_rat {p q : ℕ} (M : GKMod p q) (a : Ix p q) {t : ℂ} {v : M.V} (hv0 : v ≠ 0)
    (hv : v ∈ (M.act (Eab a a)).eigenspace t) : ∃ r : ℚ, (r : ℂ) = t := by
  by_contra hr
  have hd := Module.End.eigenspaces_iSupIndep (M.act (Eab a a)) t
  have hle : (⨆ μ : Ix p q → ℚ, wtSub M.act μ) ≤
      ⨆ (j : ℂ) (_ : j ≠ t), (M.act (Eab a a)).eigenspace j := by
    refine iSup_le fun μ => le_iSup₂_of_le ((μ a : ℚ) : ℂ) (fun h => hr ⟨μ a, h⟩) fun x hx => ?_
    exact Module.End.mem_eigenspace_iff.2 (mem_wt.1 hx a)
  exact hv0 (Submodule.disjoint_def.1 hd v hv (hle (M.wts v)))

theorem exists_highestWeight (p q : ℕ) (M : GKMod p q) (W : Submodule ℂ M.V)
    (hfd : FiniteDimensional ℂ W) (hW : KStable M.act W) (h0 : W ≠ ⊥) :
    ∃ (μ : Ix p q → ℚ) (v : M.V), v ∈ W ∧ IsHW M.act μ v := by
  have hL : Formalism.MainNotions.SchurIrreducible.IsKLieAct M.act := fun X Y _ _ => M.lie X Y
  set c : Ix p q → ℂ := fun a => (grad p q a : ℂ) with hc
  set H : Module.End ℂ M.V := M.act (Matrix.diagonal c) with hH
  have hHW : ∀ x ∈ W, H x ∈ W := hW _ (isKC_diag c)
  obtain ⟨t, ht, hmax⟩ := Set.exists_max_image _ Complex.re (finite_eig H W hHW)
    (exists_eig H W h0 hHW)
  set N := W ⊓ H.eigenspace t with hN
  haveI : FiniteDimensional ℂ N := Submodule.finiteDimensional_of_le inf_le_left
  have hkill : ∀ a b, posC a b → ∀ x ∈ N, M.act (Eab a b) x = 0 := by
    intro a b hab x hx
    by_contra hne
    have := hmax (t + (c a - c b)) ((Submodule.ne_bot_iff _).2 ⟨_,
      ⟨hW _ (isKC_Eab (same_of_pos hab)) x hx.1, eig_shift hL c (same_of_pos hab) hx.2⟩, hne⟩)
    simp only [hc, Complex.add_re, Complex.sub_re, Complex.ofReal_re] at this
    linarith [grad_lt hab]
  have hst : ∀ a, ∀ x ∈ N, M.act (Eab a a) x ∈ N := by
    intro a x hx
    refine ⟨hW _ (isKC_Eab (same_refl a)) x hx.1, ?_⟩
    have := eig_shift hL c (same_refl a) hx.2
    rwa [sub_self, add_zero] at this
  have hcomm : ∀ a b x, M.act (Eab a a) (M.act (Eab b b) x) = M.act (Eab b b) (M.act (Eab a a) x) := by
    intro a b x
    rw [lie_apply hL (isKC_Eab (same_refl a)) (isKC_Eab (same_refl b))]
    have : (Eab a a * Eab b b - Eab b b * Eab a a : Mat p q) = 0 := by
      by_cases hab : a = b
      · rw [hab, sub_self]
      · rw [Eab, Eab, Matrix.single_mul_single_of_ne _ _ _ _ hab,
          Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm hab), sub_self]
    rw [this, map_zero, LinearMap.zero_apply, add_zero]
  obtain ⟨N', h1, h2, -, h4⟩ := exists_common (fun a => M.act (Eab a a)) hcomm N ht hst Finset.univ
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 h2
  have : ∀ a, ∃ r : ℚ, M.act (Eab a a) v = (r : ℂ) • v := by
    intro a
    obtain ⟨u, hu⟩ := h4 a (Finset.mem_univ a)
    obtain ⟨r, rfl⟩ := eig_rat M a hv0 (hu hv)
    exact ⟨r, Module.End.mem_eigenspace_iff.1 (hu hv)⟩
  choose μ hμ using this
  exact ⟨μ, v, (h1 hv).1, hv0, mem_hw.2 ⟨hμ, fun a b hab => hkill a b hab v (h1 hv)⟩⟩

end GlobalTheory.ExistsHW
