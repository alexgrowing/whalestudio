import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact

namespace GlobalTheory.Doubling

theorem translate_eq_sum_of_isKFinite {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K : Subgroup G} {f : G → ℂ} (hf : Continuous f) (hK : IsKFinite K f) :
    ∃ (m : ℕ) (kk : Fin m → G) (c : Fin m → G → ℂ), (∀ j, kk j ∈ K) ∧ (∀ j, Continuous (c j)) ∧
      ∀ g, ∀ k ∈ K, f (g * k) = ∑ j, c j k * f (g * kk j) := by
  classical
  set S : Set (G → ℂ) := {Ψ | ∃ k ∈ K, Ψ = fun g => f (g * k)} with hS
  haveI : Module.Finite ℂ (Submodule.span ℂ S) := hK
  obtain ⟨b, hbS, hspan, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq ℂ S
  choose kk hkk hb using hbS
  set V := Submodule.span ℂ (Set.range b) with hV
  let B := Module.Basis.span hli
  haveI : FiniteDimensional ℂ V := Module.Finite.of_basis B
  let ev : G → Module.Dual ℂ V := fun g => (LinearMap.proj g).comp V.subtype
  have hev : Submodule.span ℂ (Set.range ev) = ⊤ := by
    have h0 : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      rw [Submodule.mem_bot]
      ext g
      exact hv (ev g) (Submodule.subset_span ⟨g, rfl⟩)
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), h0,
      Submodule.dualAnnihilator_bot]
  have ha : ∀ j, ∃ a : G →₀ ℂ, (a.sum fun g x => x • ev g) = B.coord j := fun j =>
    (Finsupp.mem_span_range_iff_exists_finsupp).1 (hev ▸ Submodule.mem_top)
  choose a ha using ha
  refine ⟨_, kk, fun j k => (a j).sum fun i x => x * f (i * k), hkk, fun j => ?_, fun g k hk => ?_⟩
  · simp only [Finsupp.sum]
    exact continuous_finset_sum _ fun i _ => continuous_const.mul (hf.comp (continuous_mul_left i))
  · have hw : (fun g => f (g * k)) ∈ V := by
      have h := Submodule.subset_span (R := ℂ) (s := S) ⟨k, hk, rfl⟩
      rw [← hspan] at h
      exact h
    set w : V := ⟨_, hw⟩ with hwdef
    have e := congrArg (fun v : V => (v : G → ℂ) g) (B.sum_repr w)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, B,
      Module.Basis.span_apply, hwdef] at e
    have hc : ∀ j, B.repr w j = (a j).sum fun i x => x * f (i * k) := fun j => by
      rw [← Module.Basis.coord_apply, ← ha j]
      simp [Finsupp.sum, LinearMap.sum_apply, ev, hwdef]
    rw [← e]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hb j]
    exact congrArg (fun x => x * f (g * kk j)) (hc j)

end GlobalTheory.Doubling
