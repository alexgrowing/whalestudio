import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions GlobalTheory.TrueGeo

set_option autoImplicit false

namespace GlobalTheory.ArchLowerBound

theorem exists_pos_le_pn :
    ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (D : Y.Dv) (σ : F →+* ℂ)
    (m : C.Met Y σ D), C.mSmooth Y σ D m → ∀ (k N : ℕ) (s : Fin N → Y.Fn), (∀ i, s i ∈ Y.H0 (k • D)) →
    (∀ x : Y.X, ∃ i, (k • D).GeneratesAt x (s i)) →
    ∃ c : ℝ, 0 < c ∧ ∀ z : Pts Y σ, ∃ j, c ≤ C.pn Y σ _ (C.mPow Y σ D k m) (C.cx Y σ (s j)) z := by
  intro F _ _ C Y D σ m hm k N s hs hgen
  obtain rfl := C.eq_std
  change Var.mSmooth Y σ D m at hm
  change ∃ c : ℝ, 0 < c ∧ ∀ z : Pts Y σ, ∃ j, c ≤ Var.pn Y σ _ (Var.mPow Y σ D k m) (Var.cx Y σ (s j)) z
  have hP : (Var.mPow Y σ D k m).SmoothOn Set.univ := Var.Met.SmoothOn.mPow isOpen_univ hm k
  set g : Fin N → Pts Y σ → ℝ := fun j z => Var.pn Y σ _ (Var.mPow Y σ D k m) (Var.cx Y σ (s j)) z with hg
  have hcont : ∀ j, Continuous (g j) := fun j =>
    continuousOn_univ.1 (hP.continuousOn_pn isOpen_univ fun y _ => Var.secReg_cx_of_mem (hs j) y)
  have hnn : ∀ j z, 0 ≤ g j z := fun j z => Var.pn_nonneg
  have hpos : ∀ z : Pts Y σ, ∃ i, 0 < g i z := by
    intro z
    obtain ⟨i, hi⟩ := hgen (under z)
    refine ⟨i, lt_of_le_of_ne (hnn i z) fun h0 => ?_⟩
    have h1 := (Var.pn_eq_zero_iff (hP.1 (Set.mem_univ z)) (Var.secReg_cx_of_mem (hs i) z)).1 h0.symm
    rw [Var.secZero_cx_iff, CartierDiv.vanishesAt_iff] at h1
    exact h1.2 hi
  set S : Pts Y σ → ℝ := fun z => ∑ j, g j z with hS
  have hSc : Continuous S := continuous_finset_sum _ fun j _ => hcont j
  obtain ⟨z₀⟩ : Nonempty (Pts Y σ) := inferInstance
  obtain ⟨z₁, -, hmin⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty) hSc.continuousOn
  have hS0 : 0 < S z₁ := by
    obtain ⟨i, hi⟩ := hpos z₁
    exact lt_of_lt_of_le hi (Finset.single_le_sum (fun j _ => hnn j z₁) (Finset.mem_univ i))
  refine ⟨S z₁ / (N + 1), div_pos hS0 (by positivity), fun z => ?_⟩
  by_contra hcon
  push_neg at hcon
  have h1 : S z ≤ N * (S z₁ / (N + 1)) := by
    calc S z = ∑ j, g j z := rfl
      _ ≤ ∑ _j : Fin N, S z₁ / (N + 1) := Finset.sum_le_sum fun j _ => (hcon j).le
      _ = N * (S z₁ / (N + 1)) := by simp
  have h2 : S z₁ ≤ S z := hmin (Set.mem_univ z)
  have h3 : (N : ℝ) * (S z₁ / (N + 1)) < S z₁ := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

end GlobalTheory.ArchLowerBound
