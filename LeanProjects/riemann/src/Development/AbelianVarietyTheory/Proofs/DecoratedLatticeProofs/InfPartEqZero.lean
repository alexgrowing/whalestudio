import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceModeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartMemCompactOfIsotropicAnnihilator
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.MixHalf

variable {D : D7}

theorem infPart_eq_zero {e : AE D} (he : IsSplitIdem D e) {z : AE D} (hz : cA D e * z = z) : infPart D z = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨β, rfl, -⟩, h3⟩ := he
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) = 0 := TensorProduct.zero_tmul _ _
  have he' : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  have h4 : (e + cA D e) * cA D e = cA D e := by rw [add_mul, h2, he', zero_add]
  rw [← hz, ← h4, h3, map_mul, map_mul, h0, zero_mul, zero_mul]

theorem map_infPart_mul {l m n : ℕ} {x : Mx D l m} (hx : x.map (infPart D) = 0) (y : Mx D m n) :
    (x ⬝ y).map (infPart D) = 0 := by
  rw [Matrix.map_mul, hx, Matrix.zero_mul]

theorem symplO_extX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x : Mx D T.rank ρ) (w : WO S T) :
    symplO S T (d.extX T x) w = symplO S T (d.extX T x) (d.extY T (w ⬝ d.jY)) := by
  unfold symplO
  rw [d.hO_coordS, d.hO_coordS]
  simp only [HypDec.extX_apply, HypDec.extY_apply, Matrix.mul_assoc, HypDec.pX_jX, HypDec.pX_j0, HypDec.pX_jY,
    HypDec.pY_jX, HypDec.pY_j0, HypDec.pY_jY, Matrix.mul_one, Matrix.mul_zero, pairS, hO_eq_trace S₀, trace_zero]

theorem rank_qX {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) : d.qX.rank = ρ := by
  refine le_antisymm (by simpa using Matrix.rank_le_height d.qX) ?_
  have h : d.qX * d.e = 1 := d.e'e
  have := Matrix.rank_mul_le_left d.qX d.e
  rwa [h, Matrix.rank_one, Fintype.card_fin] at this

theorem mixS_half : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ e, IsSplitIdem D e → ∀ f, IsThetaFunO ψ S T f → (∃ U : AddSubgroup (Mx D T.rank ρ), IsOpen (U : Set (Mx D T.rank ρ)) ∧ ∀ u ∈ U, (∀ i j, cA D e * u i j = u i j) → ∀ x, d.mixS T ψ μ 𝓕 f (x + u) = d.mixS T ψ μ 𝓕 f x) ∧ ∃ K : Set (Mx D T.rank ρ), IsCompact K ∧ ∀ x : Mx D T.rank ρ, (∀ i j, cA D e * x i j = x i j) → d.mixS T ψ μ 𝓕 f x ≠ 0 → x ∈ K := by
  intro D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he f hf
  obtain ⟨hX, hY, -⟩ := GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ S S₀ T ρ d ⟨μ, 𝓕, hμ⟩ f hf
  obtain ⟨U, hU, hl⟩ := hf.level
  have hhalf : ∀ x : Mx D T.rank ρ, (∀ i j, cA D e * x i j = x i j) → x.map (infPart D) = 0 := fun x hx => by
    ext i j; exact infPart_eq_zero he (hx i j)
  have cX : Continuous (d.extX T) := continuous_id.matrix_mul continuous_const
  have cY : Continuous (d.extY T) := continuous_id.matrix_mul continuous_const
  refine ⟨⟨U.comap (d.extX T), hU.preimage cX, fun u hu hu' x => ?_⟩, ?_⟩
  · have := hX x u
    rw [hl _ hu (map_infPart_mul (hhalf u hu') _)] at this
    exact this.symm
  · let r : WO S T →+ Mx D T.rank ρ :=
      { toFun := fun w => w ⬝ d.jY, map_zero' := Matrix.zero_mul _, map_add' := fun _ _ => Matrix.add_mul _ _ _ }
    have cr : Continuous r := continuous_id.matrix_mul continuous_const
    obtain ⟨K, hK, hmem⟩ := GlobalTheory.IsoMeanAnnih.finPart_mem_compact D S T T.rank ρ 1 d.qX
      (by rw [Matrix.rank_one, Fintype.card_fin]) (rank_qX d) ψ hψ (U.comap ((d.extY T).comp r))
      (hU.preimage (cY.comp cr))
    obtain ⟨g, hg, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
    have hs : Continuous fun b : Af D.host.F ⊗[D.host.F] D.host.E => (g.symm (0, b) : AE D) :=
      hc.comp (continuous_const.prodMk continuous_id)
    refine ⟨(fun y => y.map fun b => (g.symm (0, b) : AE D)) '' K, hK.image (continuous_id.matrix_map hs),
      fun x hx h0 => ⟨x.map (finPart D), hmem x fun u hu hu' => ?_, ?_⟩⟩
    · have h1 := hY x (u ⬝ d.jY)
      rw [hl (d.extY T (u ⬝ d.jY)) hu (map_infPart_mul (map_infPart_mul hu' _) _)] at h1
      have h2 : GlobalTheory.IsoMean.emb S T 1 d.qX x = d.extX T x := by
        change (rat (1 : Matrix (Fin T.rank) (Fin T.rank) D.host.E) ⬝ x : Mx D T.rank ρ) ⬝ d.pX = x ⬝ d.pX
        rw [rat_one, Matrix.one_mul]
      rw [h2, symplO_extX]
      have h3 : (ψ (symplO S T (d.extX T x) (d.extY T (u ⬝ d.jY))) - 1) • d.mixS T ψ μ 𝓕 f x = 0 := by
        rw [sub_smul, one_smul]; exact sub_eq_zero.2 h1.symm
      exact sub_eq_zero.1 ((smul_eq_zero.1 h3).resolve_right h0)
    · ext i j
      simp only [Matrix.map_apply]
      rw [RingEquiv.symm_apply_eq]
      exact Prod.ext ((infPart_eq_zero he (hx i j)).symm.trans (hg _).1.symm) (hg _).2.symm

end GlobalTheory.MixHalf
