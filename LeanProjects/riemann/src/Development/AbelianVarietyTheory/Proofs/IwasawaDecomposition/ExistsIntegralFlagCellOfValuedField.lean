import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralPivotDecomposition
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb

theorem exists_integral_cell : ∀ (T : Type) (m : T → ℕ) (K : Type) [Field K] (A : ValuationSubring K) (M : ℕ)
    (c u : Let m → Fin (M + 1) → K), InBlock c u → (∀ τ, LinearIndependent K fun j : Fin (m τ) => u ⟨τ, j⟩) →
    ∃ (w : Pm m) (x : CellVar m → K) (d : Let m → K), (∀ v, x v ∈ A) ∧ (∀ z, d z ≠ 0) ∧
      Tri (cellVec c w x) u d := by
  intro T m K _ A M c u hin hli
  have hg : ∀ z : Let m, ∃ a : Fin (m z.1) → K, ∑ i, a i • c ⟨z.1, i⟩ = u z := fun z =>
    (Submodule.mem_span_range_iff_exists_fun K).1 (hin z)
  choose a ha using hg
  let g : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) K := fun τ i j => a ⟨τ, j⟩ i
  have hu : ∀ τ j, u ⟨τ, j⟩ = ∑ i, g τ i j • c ⟨τ, i⟩ := fun τ j => (ha ⟨τ, j⟩).symm
  have hgli : ∀ τ, LinearIndependent K (g τ).transpose := by
    intro τ
    refine Fintype.linearIndependent_iff.2 fun s hs => ?_
    have hs' : ∀ i, ∑ j, s j * g τ i j = 0 := fun i => by
      have := congrFun hs i
      simpa [Finset.sum_apply, Matrix.transpose_apply] using this
    have h0 : ∑ j, s j • u ⟨τ, j⟩ = 0 := by
      simp_rw [hu, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul]
      simp [hs']
    exact Fintype.linearIndependent_iff.1 (hli τ) s h0
  have hdec := fun τ => GlobalTheory.exists_integral_pivot_decomposition K A _ _ (g τ) (hgli τ)
  choose ι u0 b huA hu0 hu1 hbt hbd hgub using hdec
  have hbij : ∀ τ, Function.Bijective (ι τ) := fun τ => Finite.injective_iff_bijective.1 (ι τ).injective
  let w : Pm m := fun τ => Equiv.ofBijective _ (hbij τ)
  let x : CellVar m → K := fun v => u0 v.1 (ι v.1 v.2.1.1) v.2.1.2
  refine ⟨w, x, fun z => b z.1 z.2 z.2, fun v => huA _ _ _, fun z => hbd _ _, ?_⟩
  have hcell : ∀ τ i j, cell x τ i j = u0 τ (ι τ i) j := by
    intro τ i j
    unfold cell
    split_ifs with h1 h2
    · rfl
    · subst h2; exact (hu1 τ i).symm
    · have : i < j := lt_of_le_of_ne (not_lt.1 h1) h2
      exact (hu0 τ i j this).symm
  have hv : ∀ τ j, cellVec c w x ⟨τ, j⟩ = ∑ k, u0 τ k j • c ⟨τ, k⟩ := by
    intro τ j
    simp only [cellVec, hcell]
    exact Equiv.sum_comp (w τ) (fun k => u0 τ k j • c ⟨τ, k⟩)
  have hexp : ∀ τ j, u ⟨τ, j⟩ = ∑ l, b τ l j • cellVec c w x ⟨τ, l⟩ := by
    intro τ j
    rw [hu]
    simp_rw [hv, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    rw [show g τ i j = (u0 τ * b τ) i j from by rw [← hgub τ], Matrix.mul_apply]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rintro ⟨τ, j⟩
  show u ⟨τ, j⟩ - b τ j j • cellVec c w x ⟨τ, j⟩ ∈ _
  rw [hexp, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), add_sub_cancel_left]
  refine Submodule.sum_mem _ fun l hl => ?_
  rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hl) with h | h
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, h, rfl⟩)
  · rw [hbt τ h, zero_smul]
    exact Submodule.zero_mem _

end GlobalTheory.FlagEmb
