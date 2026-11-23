import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGoodEmptyIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalRankinSelbergLogarithmFormulaStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG

namespace GlobalTheory.RSNonvan

theorem units_coe_multiset (A : Multiset ℂˣ) :
    (do let a ← A; pure (a : ℂ) : Multiset ℂ) = A.map (fun α : ℂˣ => (α : ℂ)) := by
  show A.bind (fun a => {(a : ℂ)}) = _
  exact Multiset.bind_singleton A _

theorem powSum_conj (B : Multiset ℂ) (r : ℕ) :
    (B.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum = starRingEnd ℂ ((B.map fun β => β ^ (r + 1)).sum) := by
  rw [map_multiset_sum, Multiset.map_map]
  simp [Function.comp_def, map_pow]

theorem natCast_cpow_eq_exp (q : ℕ) (hq : 1 < q) (r : ℕ) (x : ℝ) :
    (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) = Complex.exp (-((((r : ℝ) + 1) * Real.log q : ℝ) : ℂ) * (x : ℂ)) := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  rw [Complex.cpow_def_of_ne_zero hq0, ← Complex.natCast_log]
  congr 1
  push_cast
  ring

theorem four_terms (A B : Multiset ℂ) (q : ℕ) (hq : 1 < q) (r : ℕ) (x : ℝ) :
    (A.map fun α => α ^ (r + 1)).sum * (A.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum *
        (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1) +
      (B.map fun α => α ^ (r + 1)).sum * (B.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum *
        (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1) +
      (A.map fun α => α ^ (r + 1)).sum * (B.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum *
        (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1) +
      (B.map fun α => α ^ (r + 1)).sum * (A.map fun β => (starRingEnd ℂ β) ^ (r + 1)).sum *
        (q : ℂ) ^ (-(((r : ℂ) + 1) * (x : ℂ))) / ((r : ℂ) + 1) =
    ((‖((A + B).map (· ^ (r + 1))).sum‖ ^ 2 / ((r : ℝ) + 1) : ℝ) : ℂ) *
      Complex.exp (-((((r : ℝ) + 1) * Real.log q : ℝ) : ℂ) * (x : ℂ)) := by
  rw [powSum_conj A, powSum_conj B, natCast_cpow_eq_exp q hq, Multiset.map_add, Multiset.sum_add]
  set PA := (A.map fun α => α ^ (r + 1)).sum
  set PB := (B.map fun α => α ^ (r + 1)).sum
  have hn : ((‖PA + PB‖ ^ 2 : ℝ) : ℂ) = (PA + PB) * starRingEnd ℂ (PA + PB) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rw [← Complex.ofReal_pow, hn, map_add]
  ring

theorem fourProd_eq_exp (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a b : ℕ) (σ : CG E a)
    (σ' : CG E b) (hσ : σ.IsUnitary) (hσ' : σ'.IsUnitary) (T : Finset (HeightOneSpectrum (𝓞 E)))
    (hT : UnrOutside T σ) (hT' : UnrOutside T σ') (x : ℝ) (hx : 1 < x) :
    ∃ g : ℂ, HasSum (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} × ℕ =>
        ((dcoef σ σ' p.1.1 p.2 : ℝ) : ℂ) * Complex.exp (-((dexp p.1.1 p.2 : ℝ) : ℂ) * (x : ℂ))) g ∧
      (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ (x : ℂ) w.1) *
        (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ' (x : ℂ) w.1) *
        (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ σ' (x : ℂ) w.1) *
        (∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, lfac σ' σ (x : ℂ) w.1) = Complex.exp g := by
  have L := GlobalTheory.T.localRankinSelberg_logarithm_formula.2 E
  obtain ⟨s1, p1⟩ := L a a σ σ hσ hσ T hT hT x hx
  obtain ⟨s2, p2⟩ := L b b σ' σ' hσ' hσ' T hT' hT' x hx
  obtain ⟨s3, p3⟩ := L a b σ σ' hσ hσ' T hT hT' x hx
  obtain ⟨s4, p4⟩ := L b a σ' σ hσ' hσ T hT' hT x hx
  have h := (((s1.of_norm.hasSum.add s2.of_norm.hasSum).add s3.of_norm.hasSum).add s4.of_norm.hasSum)
  refine ⟨?g, ?hs, ?hp⟩
  case hp =>
    simp only [lfac]
    rw [p1.tprod_eq, p2.tprod_eq, p3.tprod_eq, p4.tprod_eq, ← Complex.exp_add, ← Complex.exp_add,
      ← Complex.exp_add]
  case hs =>
    refine (congrArg (fun f => HasSum f _) (funext fun p => ?_)).mpr h
    simp only [Pi.add_apply, units_coe_multiset]
    rw [four_terms _ _ _ (NumberField.HeightOneSpectrum.one_lt_absNorm p.1.1)]
    rfl

end GlobalTheory.RSNonvan
