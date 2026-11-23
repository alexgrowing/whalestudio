import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonEigenvalue

private theorem common_eigenvector_commuting_family {T D : Type}
    [AddCommGroup D] [_root_.Module ℂ D] [FiniteDimensional ℂ D] (φ : T → _root_.Module.End ℂ D)
    (hc : ∀ (s t : T), Commute (φ s) (φ t)) :
    ∀ (n : ℕ) (W : Submodule ℂ D), _root_.Module.finrank ℂ W = n → W ≠ ⊥ →
      (∀ (t : T), ∀ x ∈ W, φ t x ∈ W) →
      ∃ (l : D) (a : T → ℂ), l ≠ (0 : D) ∧ ∀ (t : T), (φ t : D → D) l = a t • l := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W hn hW hinv
    by_cases hs : ∀ t, ∃ c : ℂ, ∀ x ∈ W, φ t x = c • x
    · choose a ha using hs
      obtain ⟨l, hlW, hl⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
      exact ⟨l, a, hl, fun t => ha t l hlW⟩
    · push Not at hs
      obtain ⟨t, ht⟩ := hs
      haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW
      obtain ⟨c, hcv⟩ := _root_.Module.End.exists_eigenvalue ((φ t).restrict (hinv t))
      obtain ⟨v, hv⟩ := hcv.exists_hasEigenvector
      have hv0 : (v : D) ≠ 0 := fun h => hv.2 (Subtype.ext h)
      have hv1 : φ t (v : D) = c • (v : D) := by
        have := congrArg Subtype.val hv.apply_eq_smul
        simpa using this
      let E : Submodule ℂ D := W ⊓ _root_.Module.End.eigenspace (φ t) c
      have hE : ∀ y, y ∈ E ↔ y ∈ W ∧ φ t y = c • y := by
        intro y
        simp [E, Submodule.mem_inf, _root_.Module.End.mem_eigenspace_iff]
      have hEbot : E ≠ ⊥ := by
        intro h
        have : (v : D) ∈ E := (hE _).2 ⟨v.2, hv1⟩
        rw [h] at this
        exact hv0 (by simpa using this)
      have hlt : E < W := by
        refine lt_of_le_of_ne inf_le_left ?_
        intro h
        obtain ⟨x, hxW, hx⟩ := ht c
        exact hx ((hE x).1 (h ▸ hxW)).2
      have hfr : _root_.Module.finrank ℂ E < n := hn ▸ Submodule.finrank_lt_finrank_of_lt hlt
      refine ih _ hfr E rfl hEbot ?_
      intro s y hy
      obtain ⟨hyW, hyc⟩ := (hE y).1 hy
      refine (hE _).2 ⟨hinv s y hyW, ?_⟩
      have h1 : φ t (φ s y) = φ s (φ t y) := by
        have := (hc t s).eq
        exact congrArg (fun f : _root_.Module.End ℂ D => f y) this
      rw [h1, hyc, map_smul]

theorem UpperTheory.Reformulated.B.CommonEigenvectorExistence.common_eigenvector :
    ∀ {T D : Type}
    [inst : AddCommGroup D] [inst_1 : _root_.Module ℂ D] [FiniteDimensional ℂ D] [Nontrivial D] (φ : T → Module.End ℂ D),
    (∀ (s t : T), Commute (φ s) (φ t)) → ∃ (l : D) (a : T → ℂ), l ≠ (0 : D) ∧ ∀ (t : T), (φ t : D → D) l = a t • l := by
  intro T D _ _ _ _ φ hc
  exact common_eigenvector_commuting_family φ hc _ ⊤ rfl top_ne_bot (fun _ _ _ => Submodule.mem_top)
