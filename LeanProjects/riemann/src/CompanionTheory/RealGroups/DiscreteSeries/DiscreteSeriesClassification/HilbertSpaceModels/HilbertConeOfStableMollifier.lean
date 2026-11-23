import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.HilbertSpaceModels.StepSqInt

noncomputable section

open Finset

namespace CompanionTheory.RgDs.Hilb

open ReciprocityTheory.ChartRestriction.DS

theorem hilbert_cone_of_stable_mollifier : StepStable → StepMoll → StepWtSpan → StepCone := by
  intro hSt hMo hWt n ε lam T Ψ _hHC hPsi hKey η S hSH hSK
  have : FiniteDimensional ℂ S := hSK.1
  have hcl : IsClosed ((Hlam ε Ψ T.w : Submodule ℂ (L2 ε)) : Set (L2 ε)) := by
    unfold Hlam closGen
    exact Submodule.isClosed_topologicalClosure _
  obtain ⟨A, hAK, hAinj, hAsm, hAW⟩ :=
    hMo n ε (Hlam ε Ψ T.w) S hcl (hSt n ε lam T Ψ hPsi) inferInstance hSH hSK.2.1
  set S₂ : Submodule ℂ (L2 ε) := S.map A with hS₂
  have hfin : FiniteDimensional ℂ S₂ := Module.Finite.map S A
  have hK₂ : Formalism.MainNotions.S.IsKStableOn ε (rreg ε) S₂ := by
    rintro g hg _ ⟨w, hw, rfl⟩
    exact ⟨rreg ε g w, hSK.2.1 g hg w hw, hAK g hg w⟩
  have hne : S₂ ≠ ⊥ := by
    obtain ⟨v, hv, hv0, -⟩ := hSK.2.2.2.1
    intro h
    have hmem : A v ∈ S₂ := ⟨v, hv, rfl⟩
    rw [h] at hmem
    exact hv0 (hAinj v hv ((Submodule.mem_bot ℂ).1 hmem))
  obtain ⟨N, _i1, _i2, e, φ, h1, h2, -⟩ := hKey S₂ hfin (hAW.trans le_rfl) hK₂
  obtain ⟨x₀, -, hx₀⟩ := h1 S₂ le_rfl hK₂ hne
  have he : e ≠ 0 := by
    intro h
    apply hx₀
    rw [h, LinearMap.zero_apply]
  obtain ⟨ν, x, hxw, hex⟩ := hWt n ε S₂ hfin hAsm hK₂ N e he
  have hνc : InCone (lowK ε lam) ν := h2 ν x hxw hex
  have hx0 : (x : L2 ε) ≠ 0 := by
    intro h
    apply hex
    have : x = 0 := Subtype.ext h
    rw [this, map_zero]
  obtain ⟨y, hy, hyx⟩ := x.2
  have hy0 : y ≠ 0 := by
    intro h
    apply hx0
    rw [← hyx, h, map_zero]
  have hyw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (rreg ε) ν y := by
    intro θ hθ
    have h1' : A (rreg ε (Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) y -
        Complex.exp (((∑ a, ν a * θ a : ℝ) : ℂ) * Complex.I) • y) = 0 := by
      rw [map_sub, map_smul, hAK _ hθ, hyx, hxw θ hθ, sub_self]
    have h2' := hAinj _ (Submodule.sub_mem _ (hSK.2.1 _ hθ y hy) (Submodule.smul_mem _ _ hy)) h1'
    exact sub_eq_zero.1 h2'
  obtain ⟨c', hc', hd⟩ := hSK.2.2.2.2 ν y hy hy0 hyw
  obtain ⟨c, hc, hν⟩ := hνc
  refine ⟨fun a b => c a b + c' a b, ?_, ?_⟩
  · intro a b hab
    have hab' : c a b + c' a b ≠ 0 := hab
    by_cases h : c a b = 0
    · rw [h, zero_add] at hab'
      exact (hc' a b hab').1
    · exact hc a b h
  · have hη : η = ν + (η - ν) := by abel
    rw [hη, hd, hν]
    simp only [Nat.cast_add, add_smul, Finset.sum_add_distrib]
    abel

end CompanionTheory.RgDs.Hilb
