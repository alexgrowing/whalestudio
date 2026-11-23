import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittSourceMixedCoordHeisenbergRestriction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InfPartEqZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittDecompositionMixedCoordsRankZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaRestrictionDownWittTowerSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierUniquenessOfOpenSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenSubgroupHalfCharactersSeparate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfSymplZeroRight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.HalfNonvan

open GlobalTheory.HalfAverage

variable {D : D7}

theorem symplO_extX_extY {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x a : Mx D T.rank ρ) :
    symplO S T (d.extX T x) (d.extY T a) = halfSympl T a x := by
  have h := d.hO_ext T x 0 0 a 0 0
  simp only [map_zero, add_zero, zero_add] at h
  have h0 : hO S₀ T (0 : WO S₀ T) 0 = 0 := by simp [hO]
  have hp : pairS T (0 : Mx D T.rank ρ) 0 = 0 := by simp [pairS, adj]
  rw [h0, hp, add_zero, add_zero] at h
  unfold symplO halfSympl
  rw [h]
  congr 2
  simp only [pairS, halfPair, Matrix.trace, Matrix.diag, Matrix.mul_apply, adj, gA, Matrix.transpose_apply,
    Matrix.map_apply, Finset.mul_sum, mul_assoc, rat]
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_comm

theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, symplO, hO]

theorem exists_mixS_zero {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S S₀ T : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) {μ : Measure (Mx D T.rank ρ)} {𝓕 : Set (Mx D T.rank ρ)}
    (hμ : IsCovolOne (ratMx D T.rank ρ) μ 𝓕) {f₀ : WO S₀ T → ℂ} (hf₀ : IsThetaFunO ψ S₀ T f₀) :
    ∃ f, IsThetaFunO ψ S T f ∧ d.mixS T ψ μ 𝓕 f 0 = f₀ := by
  rcases Nat.eq_zero_or_pos ρ with rfl | hρ
  · obtain ⟨-, hb, hth, -⟩ := GlobalTheory.WeilSrc.om0_ext0_eq_om_emb0_of_isWeilDatumO D ψ S S₀ T d hψ
    have hc : (fun w => (f₀ ∘ (Equiv.ofBijective _ hb).symm) (d.ext0 T w)) = f₀ := by
      funext w
      exact congrArg f₀ ((Equiv.ofBijective _ hb).symm_apply_apply w)
    refine ⟨f₀ ∘ (Equiv.ofBijective _ hb).symm, (hth _).1 (by rw [hc]; exact hf₀), ?_⟩
    rw [(GlobalTheory.Unf.mixRankZero D ψ).1 S S₀ T d μ 𝓕 hμ, hc]
  · obtain ⟨h1, h2, -, -, -, h6, -⟩ := GlobalTheory.Bridge.heis_bridge D ψ S S₀ T ρ d
    obtain ⟨f, hf, hff⟩ := GlobalTheory.TowerSurj.res_surjective D S S₀ T ρ d.e d.i₀ (h1 hρ) ψ hψ μ 𝓕 (h2 ▸ hμ) f₀ hf₀
    refine ⟨f, hf, ?_⟩
    rw [h6, map_zero, heisO_zero', hff]

set_option maxHeartbeats 1000000 in

theorem avg_mixS_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ e, IsSplitIdem D e → ∀ ℓ₀ : (WO S₀ T → ℂ) →ₗ[ℂ] ℂ, (∃ f, IsThetaFunO ψ S₀ T f ∧ ℓ₀ f ≠ 0) → ∀ H : AddSubgroup (Mx D T.rank ρ), (∀ x, x ∈ H ↔ ∀ i j, cA D e * x i j = x i j) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsAddHaarMeasure], ∃ f, IsThetaFunO ψ S T f ∧ ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 f x.1) ∂ν ≠ 0 := by
  intro D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ ⟨f₀, hf₀, hℓ⟩ H hH mH bH ν hν
  obtain rfl : H = halfMx (cA D e) T.rank ρ := AddSubgroup.ext fun x => hH x
  obtain ⟨f, hf, hmix⟩ := exists_mixS_zero hψ d hμ hf₀
  by_contra hall
  push_neg at hall
  obtain ⟨-, hY, -⟩ := GlobalTheory.HeisMixSource.heis_mixS D ψ hψ S S₀ T ρ d ⟨μ, 𝓕, hμ⟩ f hf
  obtain ⟨⟨U, hU, hUinv⟩, K, hK, hKs⟩ := GlobalTheory.MixHalf.mixS_half D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he f hf
  obtain ⟨L, hL, hLU, hsep⟩ := GlobalTheory.HalfSeparate.exists_open_separated D ψ hψ T ρ e he
    (U.comap (halfMx (cA D e) T.rank ρ).subtype) (hU.preimage continuous_subtype_val)
  have hφ := @GlobalTheory.fourier_uniqueness_of_openSubgroup (halfMx (cA D e) T.rank ρ) (halfMx e T.rank ρ) _ _ _ mH bH ν hν _
    (fun a t => ψ (halfSympl T (a : Mx D T.rank ρ) (t : Mx D T.rank ρ)))
    (fun a s t => by simp only [AddSubgroup.coe_add, halfSympl_add_right, AddChar.map_add_eq_mul])
    (fun a => by simp only [ZeroMemClass.coe_zero, halfSympl_zero_right, AddChar.map_zero_eq_one])
    (fun t => by simp only [ZeroMemClass.coe_zero, halfSympl_zero_left, AddChar.map_zero_eq_one])
    (fun a b t => by simp only [AddSubgroup.coe_add, halfSympl_add_left, AddChar.map_add_eq_mul])
    L hL hsep (fun t => ℓ₀ (d.mixS T ψ μ 𝓕 f t.1))
    (Subtype.val ⁻¹' K) ((isClosed_halfMx _ _ _).isClosedEmbedding_subtypeVal.isCompact_preimage hK)
    (fun t ht => by
      have : d.mixS T ψ μ 𝓕 f t.1 = 0 := by
        by_contra h
        exact ht (hKs t.1 t.2 h)
      simp only [this, map_zero])
    (fun t l hl => by
      simp only [AddSubgroup.coe_add]
      rw [hUinv l.1 (hLU hl) l.2])
    (fun a _ => by
      rw [← hall _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf (d.extY T a.1))]
      refine congrArg (fun g => @integral _ ℂ _ _ mH ν g) (funext fun t => ?_)
      have := hY t.1 a.1
      simp only at this
      rw [this, map_smul, smul_eq_mul, symplO_extX_extY])
  apply hℓ
  have := congrFun hφ 0
  simpa [hmix] using this

end GlobalTheory.HalfNonvan
