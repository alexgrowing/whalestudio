import Mathlib

noncomputable section

open MeasureTheory

namespace GlobalTheory.Pc3.RS

theorem exists_finset_sep {X : Type*} (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W] :
    ∀ (m : ℕ) (K : Submodule ℂ W), Module.finrank ℂ K = m →
      ∃ S : Finset X, ∀ w ∈ K, (∀ s ∈ S, (w : X → ℂ) s = 0) → w = 0 := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro K hK
    by_cases h0 : K = ⊥
    · exact ⟨∅, fun w hw _ => by rw [h0] at hw; exact (Submodule.mem_bot ℂ).1 hw⟩
    · obtain ⟨w0, hw0K, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
      have : ∃ x0, (w0 : X → ℂ) x0 ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hw0 (Subtype.ext (funext hc))
      obtain ⟨x0, hx0⟩ := this
      let e : W →ₗ[ℂ] ℂ := (LinearMap.proj x0).comp W.subtype
      let K' : Submodule ℂ W := K ⊓ LinearMap.ker e
      have hlt : K' < K := by
        refine lt_of_le_of_ne inf_le_left fun heq => ?_
        have : w0 ∈ K' := heq ▸ hw0K
        exact hx0 (LinearMap.mem_ker.1 (Submodule.mem_inf.1 this).2)
      have hr : Module.finrank ℂ K' < m := hK ▸ Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨S, hS⟩ := ih _ hr K' rfl
      refine ⟨insert x0 S, fun w hw hv => hS w (Submodule.mem_inf.2 ⟨hw, ?_⟩) fun s hs => hv s (Finset.mem_insert_of_mem hs)⟩
      exact LinearMap.mem_ker.2 (hv x0 (Finset.mem_insert_self _ _))

theorem integral_mem {X Y : Type} [MeasurableSpace Y] (μ : Measure Y) (W : Submodule ℂ (X → ℂ))
    [FiniteDimensional ℂ W] (G : Y → X → ℂ) (hG : ∀ y, G y ∈ W) (hi : ∀ x, Integrable (fun y => G y x) μ) :
    (fun x => ∫ y, G y x ∂μ) ∈ W := by
  classical
  obtain ⟨S, hS⟩ := exists_finset_sep W _ ⊤ rfl
  let r : W →ₗ[ℂ] (S → ℂ) :=
    { toFun := fun w s => (w : X → ℂ) s
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : LinearMap.ker r = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    exact hS w Submodule.mem_top fun s hs => congrFun hw ⟨s, hs⟩
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective r hinj
  have key : ∀ (w : W) (x : X), (w : X → ℂ) x = ∑ s : S, (w : X → ℂ) s * ((L (Pi.single s 1) : W) : X → ℂ) x := by
    intro w x
    have h1 : L (r w) = w := by simpa using LinearMap.congr_fun hL w
    have h2 : r w = ∑ s : S, (w : X → ℂ) s • (Pi.single s 1 : S → ℂ) := by
      ext t
      simp [r, Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [← h1, h2]
    simp [map_sum, map_smul, Finset.sum_apply]
  have hfun : (fun x => ∫ y, G y x ∂μ) =
      ((∑ s : S, (∫ y, G y s ∂μ) • L (Pi.single s 1) : W) : X → ℂ) := by
    funext x
    have e : ∀ y, G y x = ∑ s : S, G y s * ((L (Pi.single s 1) : W) : X → ℂ) x :=
      fun y => key ⟨G y, hG y⟩ x
    simp_rw [e]
    rw [integral_finsetSum (Finset.univ : Finset S) fun (s : S) _ =>
      (hi (s : X)).mul_const (((L (Pi.single s 1) : W) : X → ℂ) x)]
    simp only [integral_mul_const, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun]
  exact Submodule.coe_mem _

end GlobalTheory.Pc3.RS
