import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactAnnihilatorFiniteAdelesStdChar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartEqSumTraceTraceDualBasis
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.MatAnnih

theorem trace_mul_smul_single (D : D7) {m n : ℕ} (y : Mx D n m) (r : AF D.host.F) (i : Fin n) (j : Fin m)
    (a : D.host.E) :
    Algebra.trace (AF D.host.F) (AE D) (y ⬝ (r • Matrix.single j i (incA D a) : Mx D m n)).trace =
      r * Algebra.trace (AF D.host.F) (AE D) (incA D a * y i j) := by
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_mul_single, map_smul, smul_eq_mul, op_smul_eq_mul, mul_comm (y i j)]

theorem finPart_sum_tmul (D : D7) {d : ℕ} (x : Fin d → Af D.host.F) (e : Fin d → D.host.E) :
    finPart D (∑ l, pairA D.host.F 0 (x l) ⊗ₜ[D.host.F] e l) = ∑ l, x l ⊗ₜ[D.host.F] e l := by
  unfold finPart
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum]
  rfl

theorem annih_mem_box : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (m n : ℕ), ∀ V ∈ nhds (0 : Mx D m n), ∃ K : Set (Mx D n m), IsCompact K ∧ ∀ y : Mx D n m, (∀ ξ ∈ V, ξ.map (infPart D) = 0 → ψ (Algebra.trace (AF D.host.F) (AE D) (y ⬝ ξ).trace) = 1) → InBox K y := by
  intro D ψ hψ m n V hV
  obtain ⟨d, c, e, hce⟩ := GlobalTheory.TwistCoords.finPart_eq_sum_trace D
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _

  let M : (Fin n × Fin m × Fin d) → Mx D m n := fun p => Matrix.single p.2.1 p.1 (incA D (c p.2.2))
  let φ : (Fin n × Fin m × Fin d) → Af D.host.F → Mx D m n := fun p t => (pairA D.host.F 0 t) • M p
  have hpair : Continuous fun t : Af D.host.F => pairA D.host.F 0 t := continuous_const.prodMk continuous_id
  have hφ : ∀ p, Continuous (φ p) := fun p =>
    Continuous.smul (f := fun t : Af D.host.F => pairA D.host.F 0 t) (g := fun _ => M p) hpair continuous_const
  have hφ0 : ∀ p, φ p 0 = 0 := fun p => by
    have : pairA D.host.F 0 (0 : Af D.host.F) = 0 := rfl
    simp only [φ, this, zero_smul]
  have hO : (⋂ p, φ p ⁻¹' V) ∈ nhds (0 : Af D.host.F) :=
    Filter.iInter_mem.2 fun p => (hφ p).continuousAt.preimage_mem_nhds (by rw [hφ0]; exact hV)
  obtain ⟨K₀, hK₀, hmem⟩ := GlobalTheory.ScalarAnnih.exists_compact_of_annih D ψ hψ _ hO
  let g : (Fin n × Fin m × Fin d → Af D.host.F) → Mx D n m :=
    fun z => Matrix.of fun i j => ∑ l, pairA D.host.F 0 (z (i, j, l)) ⊗ₜ[D.host.F] e l
  have hg : Continuous g := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun z : Fin n × Fin m × Fin d → Af D.host.F => ∑ l, pairA D.host.F 0 (z (i, j, l)) ⊗ₜ[D.host.F] e l
    refine continuous_finset_sum _ fun l _ => ?_
    have : (fun z : Fin n × Fin m × Fin d → Af D.host.F => (pairA D.host.F 0 (z (i, j, l)) ⊗ₜ[D.host.F] e l : AE D)) =
        fun z => pairA D.host.F 0 (z (i, j, l)) • ((1 : AF D.host.F) ⊗ₜ[D.host.F] e l : AE D) := by
      funext z; rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact (hpair.comp (continuous_apply (A := fun _ : Fin n × Fin m × Fin d => Af D.host.F) (i, j, l))).smul
      (continuous_const (y := ((1 : AF D.host.F) ⊗ₜ[D.host.F] e l : AE D)))
  refine ⟨g '' Set.pi Set.univ (fun _ => K₀), (isCompact_univ_pi fun _ => hK₀).image hg, fun y hy => ?_⟩
  let z : Fin n × Fin m × Fin d → Af D.host.F :=
    fun p => sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) (incA D (c p.2.2) * y p.1 p.2.1))
  refine ⟨g z, ⟨z, fun p _ => hmem _ fun t ht => ?_, rfl⟩, ?_⟩
  · have hu : (pairA D.host.F 0 t • Matrix.single p.2.1 p.1 (incA D (c p.2.2)) : Mx D m n) ∈ V :=
      Set.mem_iInter.1 ht p
    have hinf : (pairA D.host.F 0 t • Matrix.single p.2.1 p.1 (incA D (c p.2.2)) : Mx D m n).map (infPart D) = 0 := by
      ext k l
      simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply, Matrix.single_apply]
      split_ifs
      · change infPart D (pairA D.host.F 0 t • ((1 : AF D.host.F) ⊗ₜ[D.host.F] c p.2.2)) = 0
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        change (fstA D.host.F (pairA D.host.F 0 t)) ⊗ₜ[D.host.F] (c p.2.2) = 0
        exact TensorProduct.zero_tmul _ _
      · rw [smul_zero, map_zero]
    have h1 := hy _ hu hinf
    have e2 := trace_mul_smul_single D y (pairA D.host.F 0 t) p.1 p.2.1 (c p.2.2)
    have e1 : pairA D.host.F 0 (t * z p) = pairA D.host.F 0 t *
        Algebra.trace (AF D.host.F) (AE D) (incA D (c p.2.2) * y p.1 p.2.1) :=
      Prod.ext (zero_mul _).symm rfl
    exact (congrArg ψ (e1.trans e2.symm)).trans h1
  · refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply, Matrix.sub_apply, Matrix.zero_apply, (finPart D).map_sub, sub_eq_zero, hce]
    exact (finPart_sum_tmul D (fun l => z (i, j, l)) e).symm

end GlobalTheory.MatAnnih
