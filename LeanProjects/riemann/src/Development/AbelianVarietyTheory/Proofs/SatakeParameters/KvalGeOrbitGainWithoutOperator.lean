import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.TransportFirstLevel
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KurComplete
import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.OneLetterJetKernel
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FinalS
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralOrbitSeriesStatement

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob alG capG lsG deLoss dSet lgN DivAB)
open Formalism.GrowthSums (excessGain)
open Formalism.MainNotions.DIV.Bridge.DworkPowerSeriesWeights (young_second_row_length_count yd_size yd_one_le_colLen yd_colLen_le)
open Formalism.MainNotions.DIV.Bridge.OneLetterJetKernel (tieFrame)

namespace GlobalTheory.KerGaussA

theorem card_height_one (μ : YoungDiagram) :
    (Finset.univ.filter (fun c : Fin (μ.rowLen 0) => μ.colLen c = 1)).card = μ.rowLen 0 - μ.rowLen 1 := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (μ.rowLen 0))))
    (fun c => 2 ≤ μ.colLen c)
  rw [young_second_row_length_count, Finset.card_univ, Fintype.card_fin] at h
  have e : (Finset.univ.filter (fun c : Fin (μ.rowLen 0) => μ.colLen c = 1)) =
      Finset.univ.filter (fun c : Fin (μ.rowLen 0) => ¬ 2 ≤ μ.colLen c) := by
    ext c
    have := yd_one_le_colLen μ c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [e]; omega

theorem mem_dSet {ν : ℕ} [NeZero ν] (TT : Finset (ZMod (2 * ν))) (s : ZMod (2 * ν)) (e : ℕ) :
    2 * e + 1 ∈ dSet TT s ↔ (2 * e + 1 < 2 * ν ∧ s + ((2 * e + 1 : ℕ) : ZMod (2 * ν)) ∈ TT) := by
  have hν : 0 < ν := Nat.pos_of_ne_zero (NeZero.ne ν)
  have : NeZero (2 * ν) := ⟨by omega⟩
  unfold dSet
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨s', ⟨h1, -⟩, h3⟩
    refine ⟨h3 ▸ ZMod.val_lt _, ?_⟩
    rw [← h3, ZMod.natCast_zmod_val]
    simpa using h1
  · rintro ⟨h1, h2⟩
    refine ⟨_, ⟨h2, ?_⟩, ?_⟩
    · rw [ZMod.val_add, ZMod.val_cast_of_lt h1, Nat.mod_mod_of_dvd _ (Dvd.intro ν rfl)]
      omega
    · rw [add_sub_cancel_left, ZMod.val_cast_of_lt h1]

theorem tsum_odd (f : ℕ → ℝ) (hf : ∀ e, ¬ Odd e → f e = 0) : ∑' e : ℕ, f (2 * e + 1) = ∑' e : ℕ, f e := by
  refine Function.Injective.tsum_eq (g := fun e : ℕ => 2 * e + 1) (fun a b h => by simpa using h) ?_
  intro e he
  have ho : Odd e := by
    by_contra h
    exact he (hf e h)
  obtain ⟨k, hk⟩ := ho
  exact ⟨k, hk.symm⟩

theorem constantCoeff_sumE {K ι : Type} [Field K] [Fintype ι] {N0 N1 : ℕ} (be : MvPowerSeries (Fin 2) K)
    (h : MvPowerSeries.constantCoeff be = 0) :
    MvPowerSeries.constantCoeff (sumE (ι := ι) (N0 := N0) (N1 := N1) be) = 0 := by
  unfold sumE
  rw [map_sum]
  refine Finset.sum_eq_zero fun e _ => ?_
  refine MvPowerSeries.constantCoeff_subst_eq_zero ?_ ?_ h
  · exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun a => by simp)
  · intro a; simp

theorem exists_root_sq (l : ℕ) [hl : Fact l.Prime] : ∃ ζ : MaximalUnramifiedExtension l, IsPrimitiveRoot ζ (l ^ 2 - 1) := by
  have h1 : 1 < l ^ 2 := by have := hl.out.two_le; nlinarith
  refine Formalism.L2.Th1.D.kurRoots l (l ^ 2 - 1) (by omega) fun hd => ?_
  have h2 : l ∣ l ^ 2 := dvd_pow_self l two_ne_zero
  have h3 : l ∣ 1 := by
    have := (Nat.dvd_sub h2 hd)
    rwa [Nat.sub_sub_self h1.le] at this
  exact hl.out.one_lt.ne' (Nat.dvd_one.1 h3)

theorem exists_pi (l : ℕ) [hl : Fact l.Prime] : ∃ ϖ : ℂ_[l], ϖ ^ (l ^ 2 - 1) = (l : ℂ_[l]) := by
  have h1 : 1 < l ^ 2 := by have := hl.out.two_le; nlinarith
  exact IsAlgClosed.exists_pow_nat_eq _ (by omega)

theorem kernel_bound (l : ℕ) [Fact l.Prime] (ν m N0 N1 : ℕ) [NeZero ν] (hm : m = ν) (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l)
    (F be0 : MvPowerSeries (Fin 2) (MaximalUnramifiedExtension l)) (om oms : Fin m → MaximalUnramifiedExtension l)
    (hσ : UnrOK (MaximalUnramifiedExtension l) l σ) (hF : IsLawOfLog l F) (h1 : F1 F be0) (h2 : F2 l σ be0)
    (hO : OwOK (2 * ν) σ om oms) (hT : TrDual (2 * ν) σ om oms)
    (U0 : MvPowerSeries (Bool × Fin m × Fin N0 × Fin N1) ℂ_[l]) (hU : Formalism.DworkPowerSeriesWeights.Integral U0)
    (TT : Finset (ZMod (2 * ν))) (colN : ZMod (2 * ν) → ℕ) (hts : ∀ s, Fin (colN s) → ℕ)
    (hp : ∀ s c, hts s c ≤ N0) (I : ∀ s c, Fin (hts s c) → Fin N1) (n : (ZMod (2 * ν) × Fin N0 × Fin N0) →₀ ℕ) :
    ‖MvPolynomial.coeff n (Formalism.DworkPowerSeriesWeights.frameJet colN hts hp I (thetaInZ (d := 2 * ν) l (MaximalUnramifiedExtension l).subtype σ om oms
        (Formalism.DworkPowerSeriesWeights.mvExp (-(sumE (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0))) * U0)))‖ ≤
      (l : ℝ) ^ (-(excessGain (l : ℝ) TT (dSet TT) (fun s => (alG TT colN hts s : ℝ))
        (fun s => (capG TT colN hts s : ℝ)) (deLoss l N0 N1 TT (alG TT colN hts) (lsG TT colN hts)))) := by
  subst hm
  have : CompleteSpace (MaximalUnramifiedExtension l) := Formalism.L2.Th1.D.kurComplete l
  have hb : MvPowerSeries.constantCoeff (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype be0) = 0 := by
    have h0 : MvPowerSeries.constantCoeff be0 = 0 := h1.1 0 (Or.inl rfl)
    rw [MvPowerSeries.constantCoeff_map, h0, map_zero]
  exact (Formalism.L2.Th1.D.kernelOfF l (MaximalUnramifiedExtension l) σ hσ (exists_root_sq l) F hF be0 h1 h2 ℂ_[l] (MaximalUnramifiedExtension l).subtype m N0 N1
    (fun _ => rfl) (exists_pi l) om oms hO hT U0 _ hU (constantCoeff_sumE _ hb)
    ((Formalism.InvariantFactorPaths.G7.equivalence_rules ℂ_[l] _).1 _) TT colN hts hp I n).1

theorem kvalGe_gainA : ∀ (Lc : product_zeroth_first_parts.Loc) (ep : ℂ_[Lc.l]) (be : MvPowerSeries (ZMod Lc.d) ℂ_[Lc.l]), ‖ep‖ = 1 → BeStd Lc.l Lc.d be → OrbitPlaces.OrbitThetaExpansion Lc ep (-1) be → product_zeroth_first_parts.KvalGe Lc.N0 Lc.N1 Lc.l Lc.nu Lc.Th (gainA Lc) := by
  rintro Lc ep be hep ⟨σ, F, be0, om, oms, ζ, hD, rfl⟩ hB
  obtain ⟨U0, hU, hTh⟩ := GlobalTheory.T.exists_integral_orbit_series Lc ep σ F be0 om oms ζ hD hB
  have hp : ∀ s (c : Fin ((Lc.nu s).rowLen 0)), (Lc.nu s).colLen c ≤ Lc.N0 :=
    fun s c => (yd_colLen_le _ _).trans (Lc.nu_rows s)
  refine tieFrame Lc.l Lc.d Lc.N0 Lc.N1 Lc.nu hp Lc.Th ep _ hep ?_
  intro I n
  rw [hTh]
  clear hTh hB
  obtain ⟨hσ, hF, h1, h2, hO, hT, -⟩ := hD
  obtain ⟨J, rank_lt_alt, nu, hnu, TT⟩ := Lc
  obtain @⟨l, hl, h5, d, hd, hev, h2d, N0, N1, Th⟩ := J
  obtain ⟨ν, hν⟩ : ∃ ν, d = 2 * ν := by
    obtain ⟨k, hk⟩ := hev
    exact ⟨k, by omega⟩
  subst hν
  have : NeZero ν := ⟨by omega⟩
  refine (kernel_bound l ν (2 * ν / 2) N0 N1 (by omega) σ F be0 om oms hσ hF h1 h2 hO hT U0 hU TT
    (fun s => (nu s).rowLen 0) (fun s c => (nu s).colLen c) hp I n).trans (le_of_eq ?_)
  set Lc : product_zeroth_first_parts.Loc := ⟨⟨l, h5, 2 * ν, hev, h2d, N0, N1, Th⟩, rank_lt_alt, nu, hnu, TT⟩ with hLc
  have hal : alG TT (fun s => (nu s).rowLen 0) (fun s c => (nu s).colLen c) = alLoc Lc := by
    funext s
    unfold alG alLoc
    by_cases hs : s ∈ TT
    · rw [if_pos hs, if_pos (show s ∈ Lc.TT from hs)]
      exact card_height_one _
    · rw [if_neg hs, if_neg (show s ∉ Lc.TT from hs)]
  have hcap : capG TT (fun s => (nu s).rowLen 0) (fun s c => (nu s).colLen c) = Lc.cap := by
    funext s
    unfold capG
    rw [hal]
    unfold alLoc product_zeroth_first_parts.Loc.cap
    have hle : (nu s).rowLen 1 ≤ (nu s).rowLen 0 := (nu s).rowLen_anti 0 1 (Nat.zero_le _)
    by_cases hs : s ∈ Lc.TT
    · rw [if_pos hs, if_pos hs]
      show (nu s).rowLen 0 - ((nu s).rowLen 0 - (nu s).rowLen 1) = (nu s).rowLen 1
      omega
    · rw [if_neg hs, if_neg hs]
      rfl
  have hls : lsG TT (fun s => (nu s).rowLen 0) (fun s c => (nu s).colLen c) = fun s => Lc.size s - alLoc Lc s := by
    funext s
    unfold lsG
    rw [hal, ← yd_size]
    rfl
  rw [hcap, hls, hal]
  congr 2
  unfold excessGain gainA deLoss
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← tsum_odd _ (fun e he => if_neg (fun h => he h.1))]
  refine tsum_congr fun e => ?_
  have ho : Odd (2 * e + 1) := ⟨e, rfl⟩
  by_cases h : 2 * e + 1 ∈ dSet TT s
  · rw [if_pos h, if_neg (fun h' => h'.2 ((mem_dSet TT s e).1 h))]
  · rw [if_neg h, if_pos ⟨ho, fun h' => h ((mem_dSet TT s e).2 h')⟩]

end GlobalTheory.KerGaussA
