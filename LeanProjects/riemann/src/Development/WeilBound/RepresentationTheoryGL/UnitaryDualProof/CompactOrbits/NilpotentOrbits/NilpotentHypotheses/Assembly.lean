import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.NilpotentHypotheses.ContinuousLin

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Asm

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]

theorem nilpB_of (fourP : FourP (k := k)) (orbP : OrbP (k := k)) (locQ : LocQ (k := k)) (baseP : BaseP (k := k)) :
    NilpB (k := k) := by
  unfold NilpB
  intro n Z hCR hH
  by_cases hd : dB0 Z = 0
  · exact baseP n Z hCR hd
  refine locQ n Z hCR fun y ξ hξ hinv => ?_
  have hmono : ∀ η : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp η (Fib Z y) → Supp η (Bz Z ×ˢ Set.univ) := by
    intro η hη f hf hvan
    refine hη f hf fun p hp => hvan p ?_
    have hp' : p ∈ (Bz Z ∩ qZ Z ⁻¹' {y}) ×ˢ (Set.univ : Set (Fin n → k)) := hp
    exact ⟨hp'.1.1, hp'.2⟩
  obtain ⟨t, ht0, ht1⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator k
  obtain ⟨𝓕, hF1, hF2, hF3, hF4, hF5, hF6⟩ := fourP n Z hCR
  obtain ⟨a, ha, hP⟩ := orbP n Z hCR (Nat.pos_of_ne_zero hd) t ht1 y
  have hξB := hmono ξ hξ
  have hFξ := hP (𝓕 ξ) (hF2 ξ y hξ) (hF3 ξ hξB hinv) (hH (𝓕 ξ) (hF1 ξ hξB) (hF3 ξ hξB hinv))
  have hξK := hP ξ hξ hinv (hH ξ hξB hinv)
  have hc : 1 < (nabs k t)⁻¹ := one_lt_inv_iff₀.2 ⟨ht0, ht1⟩
  have key : ξ ∈ (supportedIn (UU : Set (Sp k n))).dualAnnihilator := by
    refine bez _ (pull Z t) (pull Z t⁻¹) (pull_inv Z hCR t).1 (pull_inv Z hCR t).2 ?_
      ((nabs k t)⁻¹) hc (dB0 Z) a ha ξ ?_ ?_
    · intro m hm
      rw [Submodule.mem_dualAnnihilator] at hm ⊢
      exact pull_kills Z hCR t m hm
    · rw [Submodule.mem_dualAnnihilator]
      exact hξK
    · rw [Submodule.mem_dualAnnihilator]
      refine (hF4 _ (prod_supp Z hCR t _ a ξ hξB)).2 ?_
      intro f hf
      have hfu : f ∈ supportedIn (Set.univ : Set (Sp k n)) :=
        (show f ∈ supportedIn (Set.univ : Set (Sp k n)) ↔
            (IsLocallyConstant f ∧ HasCompactSupport f) ∧ Function.support f ⊆ Set.univ from Iff.rfl).2
          ⟨((show f ∈ supportedIn (UU : Set (Sp k n)) ↔
            (IsLocallyConstant f ∧ HasCompactSupport f) ∧ Function.support f ⊆ UU from Iff.rfl).1 hf).1,
            Set.subset_univ _⟩
      rw [four_prod Z hCR 𝓕 hF1 hF5 hF6 t a ξ hξB f hfu]
      exact hFξ f hf
  exact (Submodule.mem_dualAnnihilator ξ).1 key

end PositivityTheory.RgUd.T.Nil.Asm
