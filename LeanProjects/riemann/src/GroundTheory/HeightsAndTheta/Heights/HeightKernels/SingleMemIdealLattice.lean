import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.LatticeBundleObjects
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ImportsMore
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ImportsTer
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.ImportsBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding Matrix GroundTheory.Heights₂.Heights TensorProduct
open scoped nonZeroDivisors

noncomputable section

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in

theorem mem_coordLine {n : ℕ} {a : Fin n → FractionalIdeal (𝓞 K)⁰ K} {x : Fin n}
    {w : idealLattice a} : w ∈ coordLine a x ↔ ∀ y, y ≠ x → (w : Fin n → K) y = 0 := by
  simp only [coordLine, satSub, Submodule.mem_comap, Submodule.subtype_apply,
    Submodule.restrictScalars_mem, Set.range_const, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, ht⟩ y hy
    rw [← ht]
    simp [hy]
  · intro h
    refine ⟨(w : Fin n → K) x, funext fun y => ?_⟩
    by_cases hy : y = x
    · subst hy; simp
    · simp [hy, h y hy]

omit [NumberField K] in

theorem single_mem_idealLattice {n : ℕ} {a : Fin n → FractionalIdeal (𝓞 K)⁰ K} (v : idealLattice a)
    (x : Fin n) : (Pi.single x ((v : Fin n → K) x) : Fin n → K) ∈ idealLattice a := by
  have hv := v.2
  unfold idealLattice at hv ⊢
  rw [Submodule.mem_pi] at hv ⊢
  intro y _
  by_cases hy : y = x
  · subst hy; simpa using hv y (Set.mem_univ _)
  · simp [Pi.single_apply, hy]

theorem coordLine_isInternal {n : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) :
    DirectSum.IsInternal (coordLine a) := by
  classical
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_def]
    intro x
    rw [Submodule.disjoint_def]
    intro w hw hw'
    have hle : (⨆ j, ⨆ (_ : j ≠ x), coordLine a j) ≤
        LinearMap.ker ((LinearMap.proj (R := 𝓞 K) (φ := fun _ : Fin n => K) x) ∘ₗ
          (idealLattice a).subtype) :=
      iSup₂_le fun j hj v hv => by
        simp [mem_coordLine.mp hv x (Ne.symm hj)]
    have h0 : (w : Fin n → K) x = 0 := by simpa using hle hw'
    ext y
    by_cases hy : y = x
    · subst hy; simpa using h0
    · simpa using mem_coordLine.mp hw y hy
  · refine eq_top_iff.mpr fun w _ => ?_
    have hw : w = ∑ x, (⟨_, single_mem_idealLattice w x⟩ : idealLattice a) := by
      ext y
      simp [Submodule.coe_sum, Finset.sum_apply, Pi.single_apply]
    rw [hw]
    refine Submodule.sum_mem _ fun x _ => Submodule.mem_iSup_of_mem x (mem_coordLine.mpr ?_)
    intro y hy
    simp [Pi.single_apply, hy]

theorem coordLine_orthogonal {n : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K)
    (d : (K →+* ℂ) → Fin n → ℝ) (hd : ∀ σ x, 0 < d σ x) (hc : ∀ σ x, d (conjugate σ) x = d σ x) :
    IsOrthogonalFamily (latticeBundle a d hd hc) (coordLine a) := by
  intro σ x y hxy l hl l' hl'
  refine (matrixMetric_inner_one_tmul (idealLattice a) (diagMetric d) (diagMetric_posDef hd)
    (diagMetric_conj hc) σ l l').trans ?_
  simp only [diagMetric, mulVec_diagonal, dotProduct, embVec, Pi.star_apply]
  refine Finset.sum_eq_zero fun z _ => ?_
  by_cases hz : z = x
  · subst hz
    simp [mem_coordLine.mp hl' z hxy]
  · simp [mem_coordLine.mp hl z hz]

theorem S6.LatticeAsBundle.proof (hS : S6.MatrixSubDegree.Statement)
    (hE : S6.QuotExtension.Statement) (hQ : S6.QuotDegree.Statement) :
    S6.LatticeAsBundle.Statement := by
  intro K _ _ n a d ha hd hc
  have hspan := (LinesIdealLatticeFG.full K n a ha).2
  have hline : ∀ x : Fin n, LinearIndependent K (fun _ : Fin 1 => (Pi.single x 1 : Fin n → K)) :=
    fun x => linearIndependent_unique_iff.mpr (by simp)
  refine ⟨latticeBundle a d hd hc, coordLine a, coordLine_isInternal a, fun x => ?_,
    coordLine_orthogonal a d hd hc, fun x => ?_, ?_⟩
  · exact (hS K n (idealLattice a) (diagMetric d) (diagMetric_posDef hd) (diagMetric_conj hc)
      hspan 1 _ (hline x)).1
  · have h := (hS K n (idealLattice a) (diagMetric d) (diagMetric_posDef hd) (diagMetric_conj hc)
      hspan 1 _ (hline x)).2
    unfold HermitianBundle.normDegree normalise
    exact congrArg (· / (Module.finrank ℚ K : ℝ)) h
  · intro m k b c hli hmk
    obtain ⟨X, -, -⟩ := hE K n a d hd hc ha m k b c hli hmk
    obtain ⟨hspan'', hdeg⟩ := hQ K n a d ha hd m k b c hli hmk
    have hstd : (fun j : Fin k => (Pi.single j 1 : Fin k → K)) = ⇑(Pi.basisFun K (Fin k)) :=
      funext fun j => (Pi.basisFun_apply K (Fin k) j).symm
    have htop : satSub (quotLattice a b c hli hmk) (fun j : Fin k => (Pi.single j 1 : Fin k → K)) =
        ⊤ := by
      refine eq_top_iff.mpr fun w _ => ?_
      simp only [satSub, Submodule.mem_comap, Submodule.restrictScalars_mem, hstd,
        (Pi.basisFun K (Fin k)).span_eq, Submodule.mem_top]
    obtain ⟨hr, hdg⟩ := hS K k (quotLattice a b c hli hmk) (schurMetric d b c)
      (schurMetric_posDef hd hli) (schurMetric_conj hc b c) hspan'' k _
      (hstd ▸ (Pi.basisFun K (Fin k)).linearIndependent)
    rw [htop] at hr hdg
    refine ⟨subBundle a d hd hc b, quotBundle a d hd hc b c hli hmk, ⟨X⟩, hr, ?_⟩
    unfold HermitianBundle.normDegree normalise
    exact congrArg (· / (Module.finrank ℚ K : ℝ)) (hdg.trans hdeg)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
