import Mathlib
import CompanionTheory.AutomorphicTheory.BesselOrbitBounds.BesselMapUniqueness.BesselMapUniqGap
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.SmoothCyc
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.SmoothCyclicVectors.PhMeas
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.IwaCore

open CompanionTheory.Bmu CompanionTheory.D.Upq.Sm Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.CompanionTheory.BmuFactor

theorem exists_factor {S E V : Type*} [AddCommGroup S] [Module ℂ S] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (J : S →ₗ[ℂ] E) (B : S →ₗ[ℂ] V) (C : ℝ)
    (hb : ∀ v, ‖B v‖ ≤ C * ‖J v‖) : ∃ T : E →L[ℂ] V, ∀ v, B v = T (J v) := by
  have hker : LinearMap.ker J ≤ LinearMap.ker B := fun v hv => by
    have := hb v
    rw [LinearMap.mem_ker.1 hv, norm_zero, mul_zero] at this
    exact norm_le_zero_iff.1 this
  let g : LinearMap.range J →ₗ[ℂ] V := ((LinearMap.ker J).liftQ B hker).comp J.quotKerEquivRange.symm.toLinearMap
  have hg : ∀ v : S, g ⟨J v, LinearMap.mem_range_self J v⟩ = B v := fun v => by
    show (LinearMap.ker J).liftQ B hker (J.quotKerEquivRange.symm ⟨J v, _⟩) = _
    rw [LinearMap.quotKerEquivRange_symm_apply_image]; rfl
  have hgb : ∀ y : LinearMap.range J, ‖g y‖ ≤ C * ‖y‖ := by
    rintro ⟨_, v, rfl⟩
    exact (congrArg norm (hg v)).le.trans (hb v)
  obtain ⟨T, hT⟩ := ContinuousLinearMap.exist_extension_of_finiteDimensional_range (g.mkContinuous _ hgb)
  refine ⟨T, fun v => ?_⟩
  have := congrArg (fun f => f ⟨J v, LinearMap.mem_range_self J _⟩) hT
  exact (hg v).symm.trans this

theorem factor : Factor := by
  intro n Hm H _ _ _ σ hσ V _ _ _ B hB
  obtain ⟨C, Ws, hW, hC⟩ := hB.bd
  have h := hσ.rep
  have hI : ∀ i : Fin Ws.length, LieWd Hm (Ws.get i) := fun i => hW _ (List.get_mem Ws i)
  have hL : ∀ i : Fin Ws.length, LieW (UH Hm) (Ws.get i) := fun i X hX t => ex_mem_of_lie (hI i X hX) t
  let S : Submodule ℂ H :=
    { carrier := {v | IsSm (UH Hm) σ v}
      add_mem' := fun ha hb => IsSm.add ha hb
      zero_mem' := IsSm.zero
      smul_mem' := fun c _ ha => IsSm.smul ha c }
  let J : S →ₗ[ℂ] (Fin Ws.length → H) :=
    { toFun := fun v i => dsW σ (Ws.get i) v
      map_add' := fun a b => funext fun i => dsW_add h a.2 b.2 (hL i)
      map_smul' := fun c a => funext fun i => dsW_smul h a.2 c (hL i) }
  let B' : S →ₗ[ℂ] V :=
    { toFun := fun v => B v
      map_add' := fun a b => hB.add _ a.2 _ b.2
      map_smul' := fun c a => hB.smul c _ a.2 }
  have hb : ∀ v : S, ‖B' v‖ ≤ (|C| * Ws.length) * ‖J v‖ := fun v => by
    have h1 : (Ws.map fun w => ‖dsW σ w (v : H)‖).sum ≤ Ws.length * ‖J v‖ := by
      have := List.sum_le_card_nsmul (Ws.map fun w => ‖dsW σ w (v : H)‖) ‖J v‖ (by
        intro x hx
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
        obtain ⟨i, rfl⟩ := List.get_of_mem hw
        exact norm_le_pi_norm (J v) i)
      rwa [List.length_map, nsmul_eq_mul] at this
    have h0 : 0 ≤ (Ws.map fun w => ‖dsW σ w (v : H)‖).sum :=
      List.sum_nonneg fun x hx => by obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx; exact norm_nonneg _
    calc ‖B' v‖ ≤ C * _ := hC _ v.2
      _ ≤ |C| * (Ws.length * ‖J v‖) := mul_le_mul (le_abs_self C) h1 h0 (abs_nonneg C)
      _ = _ := by ring
  obtain ⟨T, hT⟩ := exists_factor J B' _ hb
  refine ⟨Ws.length, Ws.get, fun i => T.comp (ContinuousLinearMap.single ℂ (fun _ => H) i), hI, fun v hv => ?_⟩
  have h2 : B v = T (J ⟨v, hv⟩) := hT ⟨v, hv⟩
  rw [h2, ← Finset.univ_sum_single (J ⟨v, hv⟩), map_sum]
  rfl

end GlobalTheory.CompanionTheory.BmuFactor

end
