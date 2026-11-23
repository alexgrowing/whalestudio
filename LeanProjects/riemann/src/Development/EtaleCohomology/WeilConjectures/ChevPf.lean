import Development.EtaleCohomology.WeilConjectures.ContinCut
import Mathlib.NumberTheory.Padics.ProperSpace

namespace LateralTheory.EWeil.ChevPf

open Topology

theorem Chev_of : LateralTheory.EWeil.ContinCut.Chev := by
  intro l _ M _ _ _ K hK h0 N
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' ℤ_[l] M
  let V : ℕ → Set (Fin r → ℤ_[l]) := fun k => ((K k).comap π : Set (Fin r → ℤ_[l]))
  have hc : ∀ k, IsCompact (V k) := by
    intro k
    obtain ⟨s, g, hg⟩ := Module.Finite.exists_fin' ℤ_[l] ((K k).comap π)
    have : V k = Set.range (((K k).comap π).subtype.comp g) := by
      ext z
      constructor
      · intro hz
        obtain ⟨a, ha⟩ := hg ⟨z, hz⟩
        exact ⟨a, by simp [ha]⟩
      · rintro ⟨a, rfl⟩
        exact (g a).2
    rw [this]
    exact isCompact_range (LinearMap.continuous_on_pi _)
  have hdir : Directed (· ⊇ ·) V := by
    intro a b
    refine ⟨max a b, ?_, ?_⟩
    · intro z hz; exact hK (le_max_left a b) hz
    · intro z hz; exact hK (le_max_right a b) hz
  let ε : ℝ := (l : ℝ) ^ (-(N : ℤ))
  have hε : 0 < ε := by
    have : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    positivity
  let U : Set (Fin r → ℤ_[l]) :=
    {z | ∃ c w, π c = 0 ∧ (∀ i, ‖w i‖ ≤ ε) ∧ z = c + w}
  have hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x := by
    intro x hx
    have hx0 : π x = 0 := h0 _ (fun k => Set.mem_iInter.1 hx k)
    refine Filter.mem_of_superset (Metric.ball_mem_nhds x hε) ?_
    intro z hz
    refine ⟨x, z - x, hx0, fun i => ?_, by abel⟩
    have h1 : dist (z i) (x i) ≤ dist z x := dist_le_pi_dist z x i
    rw [Metric.mem_ball] at hz
    rw [Pi.sub_apply, ← dist_eq_norm]
    linarith
  obtain ⟨k, hk⟩ := exists_subset_nhds_of_isCompact hdir hc hU
  refine ⟨k, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := hπ y
  obtain ⟨c, w, hc0, hw, rfl⟩ := hk (show x ∈ V k from hy)
  have hu : ∀ i, ∃ u : ℤ_[l], w i = (l : ℤ_[l]) ^ N * u := by
    intro i
    have := (PadicInt.norm_le_pow_iff_mem_span_pow (w i) N).1 (hw i)
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨u, by rw [← hu, mul_comm]⟩
  choose u hu using hu
  refine ⟨π u, ?_⟩
  have : w = (l : ℤ_[l]) ^ N • u := funext fun i => by simp [hu i]
  rw [map_add, hc0, zero_add, this, map_smul]

end LateralTheory.EWeil.ChevPf
