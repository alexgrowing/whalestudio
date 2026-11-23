import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcChart
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PDualStackedExcCycle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace StackedExceptionalReduced

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F' : HermLattice K i} {T : Type} [Fintype T]

theorem mul_mem_of_mem_base [DecidableEq T] (b' : Module.Basis T ℤ (dualLattice F')) (a : T → ℤ) (u : T) :
    ∀ x ∈ stackedBase b' a,
      graphSecond u * x ∈ stackedGraph b' a ⊔ Ideal.span {C (a u) * graphFirst u} := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  rw [mul_add]
  refine Ideal.add_mem _ (Ideal.mem_sup_left ((stackedGraph b' a).mul_mem_left _ hy)) ?_
  clear hx
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    rw [mul_comm (graphSecond u)]
    exact StackedExceptionalCycle.mul_mem_first b' a s u
  | zero => rw [mul_zero]; exact Ideal.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Ideal.add_mem _ hx hy
  | smul r x _ hx => rw [smul_eq_mul, mul_left_comm]; exact Ideal.mul_mem_left _ r hx

theorem graphFirst_not_mem {k : Type} [Field k] {n : ℕ} {α : T → k} {M : T → Fin n → k} {t : T}
    (h : α t ≠ 0) : graphFirst t ∉ linPrime α M := by
  rw [linPrime, RingHom.mem_ker, LinPrimeExample.linPointMap_first]
  exact mul_ne_zero (by rwa [Ne, C_eq_zero]) (X_ne_zero _)

theorem graphSecond_not_mem {k : Type} [Field k] {m : ℕ} {α : T → k} {M : T → Fin (m + 1) → k} {t : T}
    (h : M t 0 ≠ 0) : graphSecond t ∉ linPrime α M := by
  rw [linPrime, RingHom.mem_ker, LinPrimeExample.linPointMap_second]
  intro h0
  apply h
  have h1 := congrArg (MvPolynomial.eval fun o : Option (Fin (m + 1)) =>
    o.elim (0 : k) fun j => if j = 0 then 1 else 0) h0
  simpa [Finset.sum_ite_eq'] using h1

end StackedExceptionalReduced

open StackedExceptionalCycle StackedGraphHorizontal StackedExceptionalReduced in

theorem DualStackedExcReduced.proof (hC : DualStackedExcCoords.Statement) (hB : DualStackedExcBase.Statement)
    (hX : DualStackedExcChart.Statement) : DualStackedExcReduced.Statement := by
  intro K _ _ i F F' T _ _ b b' a hi hlt hcov hab
  obtain ⟨k, _, ρ, π, y₀, m, g, α, M, hd⟩ := hC K i F F' T b b' a hi hlt hcov hab
  have hbase := hB K i F F' T b b' a hi hlt hcov hab k ρ π y₀ m g α M hd
  have hchart := hX K i F F' T b b' a hi hlt hcov hab k ρ π y₀ m g α M hd
  obtain ⟨-, -, -, -, -, -, -, ⟨v, hv⟩, ⟨u, hu⟩, -⟩ := hd
  have hEp : (linPrime α M).IsPrime := RingHom.ker_isPrime _
  have hXv : graphFirst v ∉ linPrime α M := graphFirst_not_mem hv
  have hYu : graphSecond u ∉ linPrime α M := graphSecond_not_mem hu
  have hrel : IsRelevant (linPrime α M) := by
    rintro (⟨⟩ | ⟨⟩)
    · exact ⟨v, hXv⟩
    · exact ⟨u, hYu⟩
  have hsub : ∀ w : T, stackedGraph b' a ⊔ Ideal.span {C (a w) * graphFirst w} ≤ stackedBase b' a :=
    fun w => sup_le le_sup_left ((Ideal.span_singleton_le_iff_mem _).mpr (first_mem_base b' a w))

  have hkey : ∀ W : Ideal (MRing (stackedBlocks T)), W.IsPrime → IsRelevant W → stackedBase b' a ≤ W →
      linPrime α M ≤ W := by
    intro W hW hWr hBW e he
    obtain ⟨v', hv'⟩ : ∃ v' : T, graphFirst v' ∉ W := hWr (Sum.inl ())
    obtain ⟨u', hu'⟩ : ∃ u' : T, graphSecond u' ∉ W := hWr (Sum.inr ())
    obtain ⟨N, hN⟩ := hchart v' u'
    have h1 : (graphFirst v' * graphSecond u') ^ N * e ∈ W := hBW (hsub u' (hN e he))
    refine (hW.mem_or_mem h1).resolve_left fun h2 => ?_
    rcases hW.mem_or_mem (hW.mem_of_pow_mem N h2) with h3 | h3
    · exact hv' h3
    · exact hu' h3
  have hmin : linPrime α M ∈ (stackedBase b' a).minimalPrimes := by
    refine ⟨⟨hEp, hbase⟩, fun Q hQ hQE => hkey Q hQ.1 (fun κ => ?_) hQ.2⟩
    obtain ⟨j, hj⟩ := hrel κ
    exact ⟨j, fun h => hj (hQE h)⟩
  refine ⟨linPrime α M, ⟨hmin, hrel⟩, fun W hW => ?_, ?_⟩
  · have hEW := hkey W hW.1.1.1 hW.2 hW.1.1.2
    exact le_antisymm (hW.1.2 ⟨hEp, hbase⟩ hEW) hEW
  · obtain ⟨N, hN⟩ := hchart v u
    have hs : (graphFirst v * graphSecond u) ^ N ∉ linPrime α M := fun h =>
      (hEp.mem_or_mem (hEp.mem_of_pow_mem N h)).elim hXv hYu
    rw [← multAt_eq_of_mul_mem (hsub u) hYu (mul_mem_of_mem_base b' a u),
      multAt_eq_of_mul_mem ((hsub u).trans hbase) hs hN]
    have := hEp
    exact ReciprocityTheory.ChartRestriction.G.AI.I1.inh_multAt_self _

end

end GroundTheory.Heights₂.Heights
