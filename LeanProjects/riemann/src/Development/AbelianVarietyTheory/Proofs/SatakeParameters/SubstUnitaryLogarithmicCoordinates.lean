import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.FacShapeZero
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OfClosedInt
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.KappaIntegralOfCalculation

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd

theorem flin_pad {K : Type} [Field K] {σ n m : Type} [Fintype n] [Fintype m] {l linv : PowerSeries K}
    (hl : PowerSeries.constantCoeff l = 0) (c : n ⊕ m → K) (u : m → MvPowerSeries σ K) :
    Formalism.L2.Th1.C.flin l linv c (Sum.elim (fun _ => (0 : MvPowerSeries σ K)) u) =
      Formalism.L2.Th1.C.flin l linv (fun j => c (Sum.inr j)) u := by
  unfold Formalism.L2.Th1.C.flin
  congr 1
  rw [Fintype.sum_sum_type]
  simp [hl]

open Formalism.L2.Th1.C in

theorem unitaryInv_rect {K : Type} [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K)
    (hFr : Frame R l linv ph) (O : Type) [CommRing O] [StarRing O] (τ : O →+* K)
    (hE : ∀ α, EndInt R l linv (τ α)) (hB : ∀ z : O, star z = z → IsBinomScalar R (τ z))
    (hF1 : Formalism.L2.Th1.C.F1 R l linv ph)
    (hN : ∀ α : O, PhNormAt R l linv ph (τ α) (τ (star α)))
    (hA : ∀ α : O, AdjAt R l linv ph (τ α) (τ (star α)))
    {n m : Type} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] (γ : Matrix n m O)
    (hγ : γ.conjTranspose * γ = 1) {σ : Type} (u : m → MvPowerSeries σ K) (hu : ∀ j, IsPt R (u j)) :
    Cong R (∑ i, PowerSeries.subst (flin l linv (fun j => τ (γ i j)) u) ph) (∑ j, PowerSeries.subst (u j) ph) := by
  set P : Matrix n n O := 1 - γ * γ.conjTranspose with hP
  have hPh : P.conjTranspose = P := by
    rw [hP, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hPγ : P * γ = 0 := by
    rw [hP, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hγ, Matrix.mul_one, sub_self]
  have hγP : γ.conjTranspose * P = 0 := by
    rw [hP, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hγ, Matrix.one_mul, sub_self]
  have hPP : P * P = P := by
    conv_lhs => rw [show P * P = P * (1 - γ * γ.conjTranspose) from rfl]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPγ, Matrix.zero_mul, sub_zero]
  have hΔ : (Matrix.fromBlocks P γ γ.conjTranspose 0).conjTranspose * Matrix.fromBlocks P γ γ.conjTranspose 0 = 1 := by
    rw [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_conjTranspose, hPh, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, hPP, hPγ, hγP, hγ, ← Matrix.fromBlocks_one]
    congr 1
    · rw [hP]; abel
    · simp
    · simp
    · simp
  have hu' : ∀ c : n ⊕ m, IsPt R (Sum.elim (fun _ : n => (0 : MvPowerSeries σ K)) u c) := by
    rintro (c | c)
    · exact ⟨by simp, fun k => by simp⟩
    · exact hu c
  have key := unitaryInv K R l linv ph hFr O τ hE hB hF1 hN hA (n ⊕ m)
    (Matrix.fromBlocks P γ γ.conjTranspose 0) hΔ σ (Sum.elim (fun _ : n => 0) u) hu'
  have hph : PowerSeries.constantCoeff ph = 0 := hFr.2.2
  have hl : PowerSeries.constantCoeff l = 0 := hFr.1.1
  have hli : PowerSeries.constantCoeff linv = 0 := hFr.1.2.2.1
  simp only [Fintype.sum_sum_type, flin_pad hl, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂,
    Sum.elim_inl, Sum.elim_inr, Matrix.zero_apply, map_zero] at key
  have h0 : PowerSeries.subst (flin l linv (fun _ : m => (0 : K)) u) ph = 0 := by
    unfold flin
    simp [hli, hph]
  simpa [hph, h0] using key

theorem HostLog.subst_unitary : ∀ (p : ℕ) [Fact p.Prime] (g2 g3 s2 ε : MaximalUnramifiedExtension p) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (F : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension p)), CurveData p g2 g3 s2 ε σ F → ∀ (n m : Type) [Fintype n] [Fintype m] [DecidableEq m] (γ : n → m → MaximalUnramifiedExtension p), (∀ i j, ‖γ i j‖ ≤ 1 ∧ σ (σ (γ i j)) = γ i j) → (∀ j j', ∑ i, σ (γ i j) * γ i j' = if j = j' then 1 else 0) → ∀ Θ : MvPowerSeries n ℂ_[p], HostLog p g2 g3 s2 ε Θ → HostLog p g2 g3 s2 ε (MvPowerSeries.subst (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries m ℂ_[p])) Θ) := by
  intro p _ g2 g3 s2 ε σ F hD n m _ _ _ γ hγ hγo Θ hΘ
  classical
  obtain ⟨h5, hg2, hg3, hε, hθ, hU, hF, hN⟩ := hD
  obtain ⟨hFr, hF1, hall, hbin⟩ := Formalism.L2.Th1.Top.CalcC_proof p h5 g2 g3 ε s2 hg2 hg3 hε hθ σ hU F hF hN
  have hσ : ∀ a : MaximalUnramifiedExtension p, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1 := (Formalism.L2.Th1.D.frobSq (MaximalUnramifiedExtension p) p σ hU).2
  let _ : StarRing (Formalism.L2.Th1.D.BrC.Osub σ) := Formalism.L2.Th1.D.BrC.starO hσ
  let τ : Formalism.L2.Th1.D.BrC.Osub σ →+* ℂ_[p] := (MaximalUnramifiedExtension p).subtype.comp (Formalism.L2.Th1.D.BrC.Osub σ).subtype
  let γO : Matrix n m (Formalism.L2.Th1.D.BrC.Osub σ) :=
    Matrix.of fun i j => ⟨γ i j, Formalism.L2.Th1.D.BrC.mem_Osub.2 (hγ i j)⟩
  have hun : γO.conjTranspose * γO = 1 := by
    ext a b
    rw [Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum, Matrix.one_apply]
    have h := hγo a b
    have e : ((if a = b then (1 : Formalism.L2.Th1.D.BrC.Osub σ) else 0 : Formalism.L2.Th1.D.BrC.Osub σ) : MaximalUnramifiedExtension p) =
        if a = b then 1 else 0 := by split_ifs <;> rfl
    rw [e, ← h]
    rfl
  set l := Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p with hl_def
  set linv := Formalism.L2.Th1.D.expF ℂ_[p] p with hlinv_def
  set ph := PowerSeries.map (MaximalUnramifiedExtension p).subtype (phFF p g2 g3 s2 ε) with hph_def
  let t : n → MvPowerSeries m ℂ_[p] := fun i =>
    Formalism.L2.Th1.C.flin l linv (fun j => τ (γO i j)) MvPowerSeries.X
  have hpt : ∀ i, Formalism.L2.Th1.C.IsPt (Formalism.G.unitBall ℂ_[p]) (t i) := fun i =>
    Formalism.L2.Th1.C.Pts.isPt_flin hFr.1 hFr.2.1 (fun j => (hall _ (hγ i j).1 (hγ i j).2).1)
      (fun j => Formalism.L2.Th1.E.CompatibleChartOperations.isPt_X j)
  have hcc : ∀ i, MvPowerSeries.constantCoeff (t i) = 0 := fun i => (hpt i).1
  have hcong := unitaryInv_rect (Formalism.G.unitBall ℂ_[p]) l linv ph hFr (Formalism.L2.Th1.D.BrC.Osub σ) τ
    (fun α => (hall α.1 α.2.1 α.2.2).1) (fun z hz => hbin z.1 z.2.1 (congrArg Subtype.val hz)) hF1
    (fun α => (hall α.1 α.2.1 α.2.2).2.1) (fun α => (hall α.1 α.2.1 α.2.2).2.2) γO hun
    (MvPowerSeries.X) (fun j => Formalism.L2.Th1.E.CompatibleChartOperations.isPt_X j)
  have hph0 : PowerSeries.constantCoeff ph = 0 := hFr.2.2
  have hPh0 : MvPowerSeries.constantCoeff (Formalism.L2.Th1.E.phSum ph : MvPowerSeries n ℂ_[p]) = 0 :=
    Formalism.L2.Th1.E.CompatibleChartOperations.cc_phSum hph0
  have hb0 : ∀ (k : Type) (i : k), MvPowerSeries.constantCoeff (Formalism.InvariantFactorPaths.G7.at1 i l : MvPowerSeries k ℂ_[p]) = 0 :=
    fun k i => Formalism.L2.Th1.C.Pts.constantCoeff_subst_l hFr.1 (MvPowerSeries.constantCoeff_X i)
  set Θt : MvPowerSeries n ℂ_[p] := MvPowerSeries.subst (fun i : n => (Formalism.InvariantFactorPaths.G7.at1 i l : MvPowerSeries n ℂ_[p])) Θ with hΘt
  have hΘ' : Formalism.DworkPowerSeriesWeights.Integral (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries n ℂ_[p]) * Θt) := hΘ
  have hΘe : Formalism.DworkPowerSeriesWeights.mvExp (-(Formalism.L2.Th1.E.phSum ph : MvPowerSeries n ℂ_[p])) *
      (Formalism.DworkPowerSeriesWeights.mvExp (Formalism.L2.Th1.E.phSum ph : MvPowerSeries n ℂ_[p]) * Θt) = Θt := by
    rw [← mul_assoc]
    have := Formalism.L2.Th1.C.mvExp_neg hPh0
    rw [← Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq, ← Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq] at this
    rw [this, one_mul]
  obtain ⟨h3, h4, h5'⟩ := Formalism.L2.Th1.E.substExpInt ℂ_[p] n m t hcc (fun i k => (hpt i).2 k)
    (Formalism.L2.Th1.E.phSum ph) _ hPh0 hΘ'
  rw [hΘe, Formalism.L2.Th1.E.CompatibleChartOperations.subst_phSum _ hcc] at h3
  rw [Formalism.L2.Th1.E.CompatibleChartOperations.subst_phSum _ hcc] at h5'
  have hid : MvPowerSeries.subst (fun j : m => (Formalism.InvariantFactorPaths.G7.at1 j l : MvPowerSeries m ℂ_[p]))
      (MvPowerSeries.subst (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries m ℂ_[p])) Θ) =
      MvPowerSeries.subst t Θt := by
    have hb : MvPowerSeries.HasSubst (fun j : m => (Formalism.InvariantFactorPaths.G7.at1 j l : MvPowerSeries m ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (hb0 m)
    have hb' : MvPowerSeries.HasSubst (fun i : n => (Formalism.InvariantFactorPaths.G7.at1 i l : MvPowerSeries n ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (hb0 n)
    have hlin : MvPowerSeries.HasSubst
        (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries m ℂ_[p])) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => by simp
    have ht : MvPowerSeries.HasSubst t := MvPowerSeries.hasSubst_of_constantCoeff_zero hcc
    rw [MvPowerSeries.subst_comp_subst_apply hlin hb, hΘt, MvPowerSeries.subst_comp_subst_apply hb' ht]
    congr 1
    funext i
    rw [Formalism.InvariantFactorPaths.G7.at1, Formalism.L2.Th1.C.Pts.substMv_subst (MvPowerSeries.constantCoeff_X i) hcc,
      MvPowerSeries.subst_X ht]
    simp only [t, Formalism.L2.Th1.C.flin]
    rw [Formalism.L2.Th1.C.Pts.subst_l_linv hFr.1 (by
      rw [map_sum]
      exact Finset.sum_eq_zero fun j _ => by
        rw [map_mul, show PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries m ℂ_[p]) l = Formalism.InvariantFactorPaths.G7.at1 j l from rfl,
          hb0, mul_zero])]
    rw [← MvPowerSeries.coe_substAlgHom hb, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, MvPowerSeries.coe_substAlgHom hb, MvPowerSeries.subst_X hb]
    rw [MvPowerSeries.subst_C]
    rfl
  unfold HostLog
  rw [hid, h3, ← mul_assoc]
  refine Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' ?_ h4
  obtain ⟨hc0, hcI⟩ := Formalism.L2.Th1.C.Calc.cong_symm hcong
  have hA0 : MvPowerSeries.constantCoeff (∑ i : m, Formalism.InvariantFactorPaths.G7.at1 i ph : MvPowerSeries m ℂ_[p]) = 0 :=
    Formalism.L2.Th1.E.CompatibleChartOperations.cc_phSum hph0
  have hB0 : MvPowerSeries.constantCoeff (-(∑ i, PowerSeries.subst (t i) ph) : MvPowerSeries m ℂ_[p]) = 0 := by
    rw [map_neg, h5', neg_zero]
  rw [Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq, Formalism.L2.Th1.E.CompatibleChartOperations.mvExp_eq, ← Formalism.L2.Th1.C.mvExp_add hA0 hB0,
    ← sub_eq_add_neg]
  exact fun k => hcI k

end GlobalTheory.KerStd
