import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactAnnihilatorFiniteAdelesStdCharStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartEqSumTraceTraceDualBasisStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalTestMatrixIsolatesEntryStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMeanAnnih

theorem finPart_mem_compact : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ K : Set (Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K ∧ ∀ y : Mx D a b, (∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO V W (GlobalTheory.IsoMean.emb V W P Q y) u) = 1) → y.map (finPart D) ∈ K := by
  intro D V W a b P Q hP hQ ψ hψ U hU
  obtain ⟨d, c, e, hce⟩ := GlobalTheory.T.finitePart_eq_sum_trace_traceDualBasis D
  have hm : ∀ p : Fin a × Fin b × Fin d, ∃ m : Matrix (Fin W.rank) (Fin V.rank) D.host.E,
      ∀ (y : Mx D a b) (r : AF D.host.F), symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (r • m.map (incA D)) =
        r * Algebra.trace (AF D.host.F) (AE D) (incA D (c p.2.2) * y p.1 p.2.1) :=
    fun p => GlobalTheory.T.exists_rational_test_matrix_isolates_entry D V W a b P Q hP hQ p.1 p.2.1 (c p.2.2)
  choose m hm using hm
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  let φ : (Fin a × Fin b × Fin d) → Af D.host.F → WO V W :=
    fun p t => (pairA D.host.F 0 t) • (m p).map (incA D)
  have hpair : Continuous fun t : Af D.host.F => pairA D.host.F 0 t := continuous_const.prodMk continuous_id
  have hφ : ∀ p, Continuous (φ p) := fun p =>
    Continuous.smul (f := fun t : Af D.host.F => pairA D.host.F 0 t) (g := fun _ => (m p).map (incA D)) hpair continuous_const
  have hφ0 : ∀ p, φ p 0 = 0 := fun p => by
    have : pairA D.host.F 0 (0 : Af D.host.F) = 0 := rfl
    simp only [φ, this, zero_smul]
  have hO : (⋂ p, φ p ⁻¹' (U : Set (WO V W))) ∈ nhds (0 : Af D.host.F) :=
    Filter.iInter_mem.2 fun p => (hφ p).continuousAt.preimage_mem_nhds
      (hU.mem_nhds (by rw [hφ0]; exact U.zero_mem))
  obtain ⟨K₀, hK₀, hmem⟩ := GlobalTheory.T.exists_compact_annihilator_finiteAdeles_stdChar D ψ hψ _ hO
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : ContinuousSMul (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.toContinuousSMul _ _
  haveI : ContinuousAdd (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.toContinuousAdd (Af D.host.F) _
  let g : (Fin a × Fin b × Fin d → Af D.host.F) → Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E) :=
    fun z => Matrix.of fun i j => ∑ l, z (i, j, l) ⊗ₜ[D.host.F] e l
  have hg : Continuous g := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun z : Fin a × Fin b × Fin d → Af D.host.F => ∑ l, z (i, j, l) ⊗ₜ[D.host.F] e l
    refine continuous_finset_sum _ fun l _ => ?_
    have : (fun z : Fin a × Fin b × Fin d → Af D.host.F => z (i, j, l) ⊗ₜ[D.host.F] e l) =
        fun z => z (i, j, l) • ((1 : Af D.host.F) ⊗ₜ[D.host.F] e l) := by
      funext z; rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Continuous.smul (continuous_apply (A := fun _ : Fin a × Fin b × Fin d => Af D.host.F) (i, j, l))
      (continuous_const (y := ((1 : Af D.host.F) ⊗ₜ[D.host.F] e l)))
  refine ⟨g '' Set.pi Set.univ (fun _ => K₀), (isCompact_univ_pi fun _ => hK₀).image hg, fun y hy =>
    ⟨fun p => sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) (incA D (c p.2.2) * y p.1 p.2.1)),
      fun p _ => hmem _ fun t ht => ?_, ?_⟩⟩
  · have hu : φ p t ∈ U := Set.mem_iInter.1 ht p
    have hinf : (φ p t).map (infPart D) = 0 := by
      ext k l
      simp only [φ, Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply]
      change infPart D (pairA D.host.F 0 t • ((1 : AF D.host.F) ⊗ₜ[D.host.F] m p k l)) = 0
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      change (fstA D.host.F (pairA D.host.F 0 t)) ⊗ₜ[D.host.F] (m p k l) = 0
      exact TensorProduct.zero_tmul _ _
    have h1 := hy _ hu hinf
    simp only [φ] at h1
    rw [hm] at h1
    convert h1 using 2
    exact Prod.ext (zero_mul _).symm rfl
  · ext i j
    simp only [g, Matrix.of_apply, Matrix.map_apply]
    rw [hce]

end GlobalTheory.IsoMeanAnnih
