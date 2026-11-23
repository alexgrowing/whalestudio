import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

theorem exists_family_adapted_filtration :
    ∀ (E W : Type) [Field E] [AddCommGroup W] [Module E W] (D : Submodule E W) (F : ℤ → Submodule E W) (d : ℕ), Module.Finite E ↥D → Module.finrank E ↥D = d → (∀ a, F (a + 1) ≤ F a) → (∀ x, ∃ a, x ∈ F a) → (∀ x, (∀ a, x ∈ F a) → x = 0) → ∃ (x : Fin d → W) (u : Fin d → ℤ), (∀ k, x k ∈ D ∧ x k ∈ F (u k)) ∧ ∀ (a : ℤ) (c : Fin d → E), (∀ k, u k ≠ a → c k = 0) → ∑ k, c k • x k ∈ F (a + 1) → ∀ k, c k = 0 := by
  intro E W _ _ _ D F d hfin hd hF hex hsep
  have anti : Antitone F := antitone_int_of_succ_le hF
  induction d generalizing D with
  | zero => exact ⟨Fin.elim0, Fin.elim0, fun k => k.elim0, fun _ _ _ _ k => k.elim0⟩
  | succ d ih =>
    have hne : D ≠ ⊥ := by
      rintro rfl
      simp at hd
    have hinh : ∃ z, D ≤ F z := by
      obtain ⟨s, hs⟩ : D.FG := Module.Finite.iff_fg.mp hfin
      choose g hg using hex
      obtain ⟨m, hm⟩ := (s.image g).bddBelow
      refine ⟨m, ?_⟩
      rw [← hs, Submodule.span_le]
      intro y hy
      exact anti (hm (by simpa using ⟨y, hy, rfl⟩)) (hg y)
    have hbdd : ∃ b : ℤ, ∀ z, D ≤ F z → z ≤ b := by
      obtain ⟨y, hyD, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have : ∃ b, y ∉ F b := by
        by_contra h
        push Not at h
        exact hy0 (hsep y h)
      obtain ⟨b, hb⟩ := this
      refine ⟨b, fun z hz => ?_⟩
      by_contra h
      exact hb (anti (not_le.mp h).le (hz hyD))
    obtain ⟨lo, hlo, hmax⟩ := Int.exists_greatest_of_bdd hbdd hinh
    have hnot : ¬ D ≤ F (lo + 1) := fun h => by have := hmax _ h; omega
    obtain ⟨x0, hx0D, hx0F⟩ := SetLike.not_le_iff_exists.mp hnot
    obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_notMem hx0F
    have hx0 : x0 ∉ D ⊓ LinearMap.ker f := fun h => hf0 h.2
    have hfin' : Module.Finite E ↥(D ⊓ LinearMap.ker f) :=
      Submodule.finiteDimensional_of_le (inf_le_left : D ⊓ LinearMap.ker f ≤ D)
    have hsup : (D ⊓ LinearMap.ker f) ⊔ Submodule.span E {x0} = D := by
      apply le_antisymm
      · exact sup_le inf_le_left ((Submodule.span_singleton_le_iff_mem _ _).mpr hx0D)
      · intro y hy
        have h1 : y - (f y / f x0) • x0 ∈ D ⊓ LinearMap.ker f := by
          refine ⟨D.sub_mem hy (D.smul_mem _ hx0D), ?_⟩
          simp [LinearMap.mem_ker, div_mul_cancel₀ _ hf0]
        have h2 : (f y / f x0) • x0 ∈ Submodule.span E {x0} :=
          Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
        simpa using Submodule.add_mem_sup h1 h2
    have hd' : Module.finrank E ↥(D ⊓ LinearMap.ker f) = d := by
      have hne0 : x0 ≠ 0 := fun h => hf0 (by simp [h])
      have := Submodule.finrank_sup_add_finrank_inf_eq (D ⊓ LinearMap.ker f) (Submodule.span E {x0})
      rw [hsup, hd, ((Submodule.disjoint_span_singleton' hne0).mpr hx0).eq_bot, finrank_bot,
        finrank_span_singleton hne0] at this
      omega
    obtain ⟨x, u, h1, h2⟩ := ih _ hfin' hd'
    refine ⟨Fin.cons x0 x, Fin.cons lo u, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun j => ?_) k
      · exact ⟨hx0D, hlo hx0D⟩
      · exact ⟨(h1 j).1.1, (h1 j).2⟩
    · intro a c hc hs
      rw [Fin.sum_univ_succ] at hs
      simp only [Fin.cons_zero, Fin.cons_succ] at hs
      have hc0 : c 0 = 0 := by
        by_cases ha : lo = a
        · subst ha
          have h3 := hf hs
          rw [LinearMap.mem_ker, map_add, map_sum, map_smul] at h3
          have h4 : ∑ j : Fin d, f (c j.succ • x j) = 0 :=
            Finset.sum_eq_zero fun j _ => by
              rw [map_smul, (LinearMap.mem_ker.mp (h1 j).1.2), smul_zero]
          rw [h4, add_zero, smul_eq_mul] at h3
          exact (mul_eq_zero.mp h3).resolve_right hf0
        · exact hc 0 ha
      rw [hc0, zero_smul, zero_add] at hs
      have h5 := h2 a (fun j => c j.succ) (fun j hj => hc j.succ hj) hs
      intro k
      exact Fin.cases hc0 h5 k

end GlobalTheory
