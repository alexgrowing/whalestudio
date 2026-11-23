import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertPrimeTeichmuller.UltrametricPairEstimate

open NumberField Filter Topology

noncomputable section

namespace PI.OkpW

theorem okpInert_main : PI.OkpInert := by
  intro K _ _ c p _ τ hK hc hp2 hP
  show closure (Set.range fun a : 𝓞 K => (τ (a : K), τ (c (a : K)))) =
    closure (Subring.closure (gens p) : Set (ℂ_[p] × ℂ_[p]))
  have hqn : ∀ (a : 𝓞 K) (n : ℕ), (p : 𝓞 K) ∣ a ^ ((p ^ 2) ^ n) - a := fun a n =>
    pow_q_sub hK hP a n
  have hq : ∀ b : 𝓞 K, (p : 𝓞 K) ∣ b ^ (p ^ 2) - b := fun b => by simpa using hqn b 1
  set cO : 𝓞 K →+* 𝓞 K := RingOfIntegers.mapRingHom c with hcO
  have hfrob : ∀ a : 𝓞 K, (p : 𝓞 K) ∣ cO a - a ^ p := fun a => c_frob hK c hc hp2 hP a
  have hcoe : ∀ a : 𝓞 K, ((cO a : 𝓞 K) : K) = c (a : K) := fun a => rfl
  set ψ : 𝓞 K →+* ℂ_[p] × ℂ_[p] :=
    RingHom.prod (τ.comp (algebraMap (𝓞 K) K)) (τ.comp ((algebraMap (𝓞 K) K).comp cO)) with hψ
  have hR : Set.range (fun a : 𝓞 K => (τ (a : K), τ (c (a : K)))) =
      (ψ.range : Set (ℂ_[p] × ℂ_[p])) := by
    rw [RingHom.coe_range]
    rfl
  apply Set.Subset.antisymm
  · apply closure_minimal _ isClosed_closure
    rintro _ ⟨a, rfl⟩
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hp1 : (p : ℝ)⁻¹ < 1 :=
      inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hp1
    obtain ⟨r, hr, h1, h2⟩ := approx τ cO hqn hfrob n a
    refine ⟨r, hr, ?_⟩
    rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm]
    rw [hcoe] at h2
    exact max_lt (lt_of_le_of_lt h1 hn) (lt_of_le_of_lt h2 hn)
  · have hsub : gens p ⊆ (ψ.range.topologicalClosure : Set (ℂ_[p] × ℂ_[p])) := by
      rintro x ⟨ζ, hζ, rfl⟩
      obtain ⟨a, ha⟩ := teich_surj hq hK τ hP hζ
      have hb : teich τ (cO a) = teich τ a ^ p := teich_c τ hq a (cO a) (hfrob a)
      show (_ : ℂ_[p] × ℂ_[p]) ∈ closure (ψ.range : Set (ℂ_[p] × ℂ_[p]))
      have hlim : Tendsto (fun k => (tseq τ a k, tseq τ (cO a) k)) atTop (𝓝 (ζ, ζ ^ p)) := by
        rw [← ha, ← hb]
        exact (teich_spec τ hq a).1.prodMk_nhds (teich_spec τ hq (cO a)).1
      apply mem_closure_of_tendsto hlim
      refine Filter.Eventually.of_forall fun k => ?_
      refine RingHom.mem_range.mpr ⟨a ^ ((p ^ 2) ^ k), ?_⟩
      simp [hψ, tseq]
    rw [hR]
    exact closure_minimal (SetLike.coe_subset_coe.mpr (Subring.closure_le.mpr hsub))
      isClosed_closure

end PI.OkpW
