import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.L2.Host PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.HeckeEigenspaces

theorem exists_closed_common_ker {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] (𝒯 : Set (X →L[ℂ] X)) :
    ∃ Y : Submodule ℂ X, IsClosed (Y : Set X) ∧ ∀ φ, φ ∈ Y ↔ ∀ T ∈ 𝒯, T φ = 0 := by
  refine ⟨{ carrier := {φ | ∀ T ∈ 𝒯, T φ = 0}
            add_mem' := fun {x y} hx hy T hT => by rw [map_add, hx T hT, hy T hT, add_zero]
            zero_mem' := fun T _ => map_zero T
            smul_mem' := fun c x hx T hT => by rw [map_smul, hx T hT, smul_zero] }, ?_, fun _ => Iff.rfl⟩
  have e : ({φ | ∀ T ∈ 𝒯, T φ = 0} : Set X) = ⋂ T ∈ 𝒯, T ⁻¹' {0} := by
    ext φ; simp
  change IsClosed ({φ | ∀ T ∈ 𝒯, T φ = 0} : Set X)
  rw [e]
  exact isClosed_biInter fun T _ => isClosed_singleton.preimage T.continuous

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem exists_heckeOp (w : Pl E) {h : GL (Fin a) (w.adicCompletion E) → ℂ} (hh : h ∈ Hecke ℂ (KGL w a)) :
    ∃ T : XB E a →L[ℂ] XB E a, (∀ x, heckeVec (repW a w) (KGL w a) h x = T x) ∧
      ∀ A : XB E a →L[ℂ] XB E a, (∀ u, Commute A (Rt E a (fl a w u))) → Commute A T := by
  classical
  have hs := Formalism.UG.P.finite_support_cosets (Final.GLintComm E w a) hh.2
  refine ⟨∑ c ∈ hs.toFinset, h c.out • Rt E a (fl a w c.out), fun x => ?_, fun A hA => ?_⟩
  · rw [heckeVec, finsum_eq_sum_of_support_subset (s := hs.toFinset)]
    · simp
    · intro c hc
      refine Finset.mem_coe.2 (hs.mem_toFinset.2 fun h0 => hc (by simp [h0]))
  · exact Commute.sum_right _ _ _ fun c _ => (hA c.out).smul_right _

theorem hecke_eigenfunctions_closed : G0 → G2c := by
  intro h0 E _ _ _ a w B hB
  have hcomm : ∀ g : GA E a, cLoc w g = 1 → ∀ u, Commute (Rt E a g) (Rt E a (fl a w u)) := fun g hg u => by
    have e := (h0 E a).2.2.2.2.2.2.2.1 w g hg u
    change Rt E a g * Rt E a (fl a w u) = Rt E a (fl a w u) * Rt E a g
    rw [← map_mul, ← map_mul, e]
  choose T hT hC using fun (p : {ϖ // IsUnifV E w ϖ}) (j : ℕ) =>
    exists_heckeOp (a := a) w (Tj_mem_hecke (n := a) p.2 j)
  obtain ⟨Y, hcl, hY⟩ := exists_closed_common_ker
    ({R | (∃ k ∈ KGL w a, R = Rt E a (fl a w k) - 1) ∨
      ∃ (p : {ϖ // IsUnifV E w ϖ}) (j : ℕ), j ≤ a ∧ R = T p j - satEig (qV E w) a B j • 1} :
      Set (XB E a →L[ℂ] XB E a))
  refine ⟨Y, hcl, fun g hg φ hφ => ?_, fun φ => ?_⟩
  · rw [hY] at hφ ⊢
    intro R hR
    have hRc : Commute (Rt E a g) R := by
      rcases hR with ⟨k, -, rfl⟩ | ⟨p, j, -, rfl⟩
      · exact (hcomm g hg k).sub_right (Commute.one_right _)
      · exact (hC p j _ (hcomm g hg)).sub_right ((Commute.one_right _).smul_right _)
    have e : R (Rt E a g φ) = Rt E a g (R φ) := (DFunLike.congr_fun hRc.eq φ).symm
    rw [e, hφ R hR, map_zero]
  · rw [hY]
    constructor
    · intro h
      by_cases hφ : φ = 0
      · exact Or.inl hφ
      · refine Or.inr ⟨hφ, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, hB, fun ϖ hϖ j hj => ?_⟩
        · have := h _ (Or.inl ⟨k, hk, rfl⟩)
          simpa [sub_eq_zero] using this
        · have := h _ (Or.inr ⟨⟨ϖ, hϖ⟩, j, hj, rfl⟩)
          rw [hT ⟨ϖ, hϖ⟩ j]
          simpa [sub_eq_zero] using this
    · rintro (rfl | ⟨-, hfix, -, heig⟩) R hR
      · exact map_zero R
      · rcases hR with ⟨k, hk, rfl⟩ | ⟨p, j, hj, rfl⟩
        · have := GlobalTheory.LGrp.mem_fixed.1 hfix k hk
          simpa [sub_eq_zero] using this
        · have := heig p.1 p.2 j hj
          rw [hT p j] at this
          simpa [sub_eq_zero] using this

end GlobalTheory.CompanionTheory.HeckeEigenspaces
