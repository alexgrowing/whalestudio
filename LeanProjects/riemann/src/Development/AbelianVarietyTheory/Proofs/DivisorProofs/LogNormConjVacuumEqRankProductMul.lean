import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyStandardLatticesEqBaseVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConstantExponentsFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumNormConjCmPointsAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyEqTensorPowerVacuumStatement

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.ConjVacuumPower

theorem even_rank (R : Ranks) (l : ℕ) : Even (R.N l) := by
  unfold Ranks.N
  exact R.k_even.add ((R.t_odd.add_one).mul_left l)

theorem logThAt_eq_mul : ∀ (D : D7) (dl : ℂ) (B : Base D D.host.ccK dl) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (K : Type) [Field K] (σ₀ : K →+* ℂ) (R : Ranks) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M], TaylorLogMetric.adm1 D → GL3Theta.InducedCMType D → TaylorLogMetric.IsCurveIdeal D D.host.ccK → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D D.host.ccK dl → TaylorLogMetric.IsChi D χ → B.VecP χ → ThetaFieldData B cD σ₀ R M → ∀ ρ : M →ₐ[ℚ] ℂ, ∃ lt : ℝ, ∀ i < R.m, logThAt B M ρ (R.N i) (R.N (i + 1)) = (R.N i : ℝ) * (R.N (i + 1) : ℝ) * lt := by
  intro D dl B χ cD K _ σ₀ R M _ hadm hpsi hcur hdel hχ hV hH ρ
  have hc : StandardLatticesGL3.Crv D D.host.ccK dl := ⟨hcur, hdel⟩
  have hY := GlobalTheory.ExponentsFinite.yFinite D B.γ₀ B.kc
  have hT := GlobalTheory.T.normalisedFamily_eq_tensorPower_vacuum D _ dl B χ hadm hpsi hcur hdel hχ hY
  have hD : TaylorLogMetric.DataIn D (TaylorLogMetric.tor0 D D.host.ccK dl) M := hH.2.1
  obtain ⟨t', ht'⟩ := (GlobalTheory.TwoTorsionPt.exists_point D _ dl hc).2 M ρ hD.2.1 hD.2.2
  refine ⟨(TaylorLogMetric.fF D : ℝ) * Real.log (StandardLatticesGL3.nrm1Sq (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D D.host.ccK dl))
    (GL3Theta.th0 (TaylorLogMetric.lamConj M ρ (TaylorLogMetric.lamOf D D.host.ccK dl)) t')), fun i hi => ?_⟩
  obtain ⟨hAdm, hbase⟩ := GlobalTheory.NatAtStd.eNat_std D _ dl B χ hχ hV _ _ (even_rank R i) (even_rank R (i + 1))
  have hE := hT _ B.t0 _ _ _ _ hAdm
  rw [hbase] at hE
  have hs : ∀ n, StandardLatticesGL3.SD D (StandardLatticesGL3.stdL D n) := fun n => by
    letI := D.host.cmStar
    exact GlobalTheory.NatAtStd.isSD_pi _ n
  have h := (GlobalTheory.ConjNorm.useNorm_all D _ dl hc _ B.t0 _ _ _ _ (hs _) (hs _) ((even_rank R i).mul_right _) _ hE M ρ hD
    (hH.2.2.2 i hi) t' ht').1
  unfold logThAt
  erw [h]
  rw [Real.log_pow]
  push_cast
  ring

end GlobalTheory.ConjVacuumPower
