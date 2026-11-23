import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.WeightVectorTensorEqDual
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.K1V

noncomputable section

open ComplexConjugate
open ReciprocityTheory.ChartRestriction.DS.Mult1.ConjugateHilbertSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.LemK

open ReciprocityTheory.ChartRestriction.DS DualRepresentationReversal

theorem dualKType_of_standardKType (n : ℕ) (hK : LowestKTypeEulerTensorStandard n) : LowestKTypeEulerTensorDual n := by
  intro ε lam h H _ _ _ σ D E V hσ hD hV hc hVK hint hanti hgl hp hq f hf
  have hint' : ∀ a, ∃ m : ℤ, lamd lam a - ((n : ℝ) - 1) / 2 = (m : ℝ) := fun a => by
    obtain ⟨m, hm⟩ := hint (Fin.rev a)
    exact ⟨-m - ((n : ℤ) - 1), by push_cast; simp only [lamd]; linarith⟩
  have hc' : ∀ v ∈ cjV V, casimir (Edd ε E) v = (casVal (lamd lam) : ℂ) • v := fun v hv => by
    rw [← ofD_toD v, casimir_Edd, hc _ ((mem_cjV v).1 hv), casVal_rev, ofD_smul, Complex.conj_ofReal]
  have hVK' : ∀ k ∈ Kset (ε ∘ Fin.rev), ∀ v ∈ cjV V, ∃ w ∈ cjV V, (w : Cj H) = sdd σ k v :=
    fun k hk v hv => by
      obtain ⟨w, hw, hweq⟩ := hVK (sub k) (K_sub hk) (toD v) ((mem_cjV v).1 hv)
      exact ⟨ofD w, (mem_cjV _).2 hw, hweq⟩
  have hgl' := gapLap_rev hgl
  have key := hK (ε ∘ Fin.rev) (lamd lam) h (Cj H) (sdd σ) (cjSub D) (Edd ε E) (cjV V) (urep_sdd hσ)
    (derived_sdd hD) (kirr_cjV hV) hc' hVK' hint' hgl'.1 hgl' (by rwa [pOf_rev]) (by rwa [qOf_rev])
    (Tf ε f) (fun c => mem_genSub_Edd ε E V (Submodule.smul_mem _ _ (hf _)))
  have hθ : thV (lamd lam) = fun t => thVd lam (Fin.rev t) := by
    funext t; simp only [thV, thVd, lamd]
  rw [hθ, prodShift_rev] at key
  have hl := list_inter (Tfh ε) (Tf_smul ε) (eeV (Edd ε E)) (eeVd E) (fun g => (weightVector_tensor_eq_dual ε E g).symm)
    (List.ofFn (thVd lam)) f
  rw [← prodShift_eq, ← prodShift_eq] at hl
  have h2 : Tfh ε (prodShift (eeVd E) (thVd lam) f) = 0 := by rw [hl]; exact key
  exact Tf_inj ε h2

theorem k1Vd (n : ℕ) : LowestKTypeEulerTensorDual n :=
  dualKType_of_standardKType n (k1V n)

end ReciprocityTheory.ChartRestriction.DS.Lap.LemK
