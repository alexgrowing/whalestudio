import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRightOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqFinClSumAvg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenSubgroupFixesVacuumDefiniteBottom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixTranslates
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

open scoped Topology

noncomputable section

namespace GlobalTheory.VacFixNeg

open GlobalTheory.Grid (neg)

set_option maxHeartbeats 1000000 in

theorem exists_open_fix_vac_neg : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D A), IsOpen (U : Set (GA D A)) ∧ GinfC A ≤ U ∧
      ∀ k ∈ U, k ∈ GfC A → X.ω t (k, 1) X.vac = X.vac := by
  intro D T L sc G W i j A A' WW X hX t
  set om' := (X.ω t).toSgn true with hom'
  have hW : IsWeilDatumO W.ψ (neg A) WW _ _ om' := hX.is.weil t
  have hvac : IsVacO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.Λ X.rW.Λ X.vac := hX.is.isVac
  have hθ : IsInfFam W.θ := hvac.2.inf
  have hsdS : IsSelfDualC (neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hX.is.rigA.1
  have hsdT : IsSelfDualC WW X.rW.Λ := hX.is.rigW.1
  have hcS : ∀ τ, IsCartanInv (gramAt D (neg A) τ) (-X.rA.s τ) := fun τ =>
    GlobalTheory.Grid.isCartanInv_sgn true A τ (hX.is.rigA.2.2 τ).1
  have hcT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hX.is.rigW.2.2 τ).1
  obtain ⟨n₀, hn₀⟩ := GlobalTheory.VacTranslate.exists_finCong_mod (neg A) WW X.rA.Λ X.rW.Λ hsdS hsdT 1 one_pos
  set N₁ := n₀.factorial with hN₁def
  have hN₁ : 0 < N₁ := n₀.factorial_pos
  have hscal : ∀ k ∈ GfC (neg A), GlobalTheory.Member.FinCong (neg A) N₁ k →
      ∃ c : ℂ, ‖c‖ = 1 ∧ om' (k, 1) X.vac = c • X.vac := by
    intro k hk hc
    have hΛ := GlobalTheory.VacTranslate.lat_iff_of_mod hn₀
      (show k ∈ GlobalTheory.Member.PrincLevel.levelGroup (neg A) N₁ from ⟨hk, hc⟩)
    have hvac' := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ (neg A) WW _ _ om' hW hθ
      (fun τ => -X.rA.s τ) (fun τ => -X.rA.s τ) X.rW.s X.rW.s _ _ _ _ k 1
      (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ (neg A) hk τ, Matrix.one_mul, Matrix.mul_one])
      (fun τ => GlobalTheory.SmoothVac.comm_compAt_one WW W.θ τ (X.rW.s τ)) hΛ X.vac hvac
    exact GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ hvac.1 hθ (Formalism.L2.Fam.ThC.fixSig (neg A)) (Formalism.L2.Fam.ThC.fixSig WW)
      (fun τ => -X.rA.s τ) X.rW.s (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _) hcS hcT X.rA.Λ X.rW.Λ
      hsdS hsdT X.vac _ (GlobalTheory.VacFixTarget.isVacO_fixSig hvac) (GlobalTheory.VacFixTarget.isVacO_fixSig hvac')
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hvac
  have hcont : Continuous fun k : GA D (neg A) => om' (k, 1) X.vac w₀ :=
    (hW.om_cont _ hvac.2.theta w₀).comp (continuous_id.prodMk continuous_const)
  have key : ∃ n : ℕ, ∀ k ∈ GfC (neg A), GlobalTheory.Member.FinCong (neg A) (N₁ * n.factorial) k →
      om' (k, 1) X.vac = X.vac := by
    by_contra hne
    push_neg at hne
    choose k hk hkc hkne using hne
    have hpow : ∀ n, ∃ m : ℕ, ∃ c : ℂ, om' (k n ^ m, 1) X.vac = c • X.vac ∧ ¬ ‖c - 1‖ ≤ 1 / 2 := by
      intro n
      obtain ⟨c, -, hc⟩ := hscal (k n) (hk n) (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc n))
      have hc1 : c ≠ 1 := by
        rintro rfl
        exact hkne n (by rw [hc, one_smul])
      by_contra h
      push_neg at h
      exact hc1 (GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le (A := ℂ) fun m =>
        h m (c ^ m) (GlobalTheory.VacFixSource.om_pow_eq_fst _ (k n) _ c hc m))
    choose m c hmc hc using hpow
    have hmem : ∀ n, k n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup (neg A) (N₁ * n.factorial) :=
      fun n => pow_mem (show k n ∈ GlobalTheory.Member.PrincLevel.levelGroup (neg A) (N₁ * n.factorial) from ⟨hk n, hkc n⟩) _
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k n ^ m n) (fun n => (hmem n).1)
      (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem n).2)
    have h2 := (hcont.tendsto 1).comp ht
    have e1 : om' ((1 : GA D (neg A)), (1 : GA D WW)) X.vac w₀ = X.vac w₀ := by
      show om' 1 X.vac w₀ = _
      rw [map_one]
      rfl
    rw [Function.comp_def, e1] at h2
    have hpos : 0 < ‖X.vac w₀‖ / 2 := half_pos (norm_pos_iff.2 hw₀)
    obtain ⟨n, hn⟩ := (h2.eventually (Metric.ball_mem_nhds _ hpos)).exists
    rw [hmc n, Pi.smul_apply, smul_eq_mul, dist_eq_norm, ← sub_one_mul, norm_mul] at hn
    have := hc n
    push_neg at this
    nlinarith [norm_nonneg (X.vac w₀)]
  obtain ⟨n, hn⟩ := key
  have hNpos : 0 < N₁ * n.factorial := Nat.mul_pos hN₁ n.factorial_pos
  refine ⟨(GlobalTheory.VacFixTarget.congGroup (neg A) (N₁ * n.factorial)).comap (GlobalTheory.Grid.ofSgn true A).symm.toMonoidHom,
    (GlobalTheory.Grid.continuous_ofSgn_symm true A).isOpen_preimage _ (GlobalTheory.VacFixTarget.isOpen_congGroup (neg A) hNpos),
    fun k hk => ?_, fun k hU hk => ?_⟩
  · show GlobalTheory.Member.FinCong (neg A) (N₁ * n.factorial) ((GlobalTheory.Grid.ofSgn true A).symm k)
    have h1 : finHom (neg A) ((GlobalTheory.Grid.ofSgn true A).symm k) = 1 := hk
    intro z hz
    refine ⟨0, by first | exact zero_mem _ | exact Submodule.zero_mem _ | exact AddSubgroup.zero_mem _ | simp [Formalism.L2.Pj.latHat], ?_⟩
    rw [h1, Units.val_one, Matrix.one_mulVec, sub_self]
    exact (nsmul_zero _).symm
  · have h1 := hn ((GlobalTheory.Grid.ofSgn true A).symm k) hk hU
    have e : om' ((GlobalTheory.Grid.ofSgn true A).symm k, 1) = X.ω t (k, 1) := by
      simp [hom', GlobalTheory.Grid.WRep.toSgn]
    rw [e] at h1
    exact h1

end GlobalTheory.VacFixNeg
