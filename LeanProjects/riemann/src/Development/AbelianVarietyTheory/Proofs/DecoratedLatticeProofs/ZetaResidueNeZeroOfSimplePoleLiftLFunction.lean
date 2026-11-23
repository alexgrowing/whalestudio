import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialNormalizingFactorProductAnalyticNeZero
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SimplePoleTwistedLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.Exh

open Filter Topology

theorem residue_ne_zero_of_simplePole : GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.SimplePole → ∀ (D : D7) (S : Finset (FinPl D)) (r t : ℕ) (c par : GlobalTheory.LFun.Fam D.host.E) (χ : (AE D)ˣ →* Circle), GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.Hyp (S : Set (FinPl D)) r t c par (GlobalTheory.LFun.val (F := D.host.F) χ) (GlobalTheory.LFun.val (F := D.host.F) χ) → ∀ (a b : ℕ) (Z : ℂ → ℂ) (C z : ℂ), C ≠ 0 → EqRight Z (fun s => GlobalTheory.LFun.LSD D S par χ (s + 1 / 2) / GlobalTheory.LFun.dSfun D.host.E (S : Set (FinPl D)) a b s * C) → CoeffAt Z ((t : ℂ) / 2) (-1) z → z ≠ 0 := by
  intro hSP D S r t c par χ hH a b Z C z hC hZ hz
  obtain ⟨-, -, ⟨Z0, hZ0⟩, h4⟩ := hSP D.host.F D.host.E (S : Set (FinPl D)) r t c par
    (GlobalTheory.LFun.val (F := D.host.F) χ) (GlobalTheory.LFun.val (F := D.host.F) χ) hH
  obtain ⟨hmer, -, heq, -, -, ρ, hρ, hlim⟩ := h4 Z0 hZ0
  set R := GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift.rhs (S : Set (FinPl D)) c (GlobalTheory.LFun.val (F := D.host.F) χ) t Z0 with hR
  set d := GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E (S : Set (FinPl D)) a b with hd
  obtain ⟨hdan, hdne⟩ := dSfun_analytic_ne_zero D (S : Set (FinPl D)) a b
  have ht : (r : ℝ) + 5 ≤ t := by exact_mod_cast hH.2.1
  have hr0 : (0 : ℝ) ≤ (r : ℝ) / 2 := by positivity
  have htr : (r : ℝ) / 2 < ((t : ℂ) / 2).re := by
    have : ((t : ℂ) / 2).re = (t : ℝ) / 2 := by simp
    rw [this]; linarith
  have hext : IsExtAt (fun s => GlobalTheory.LFun.LSD D S par χ (s + 1 / 2) / d s * C) ((t : ℂ) / 2)
      (fun s => R (s + 1 / 2) / d s * C) := by
    refine ⟨rightOf ((r : ℝ) / 2), htr, isRightDomain_rightOf _, fun s hs => ?_, (t : ℝ) / 2, fun s hs => ?_⟩
    · have hs0 : (r : ℝ) / 2 < s.re := hs
      have hs' : ((r : ℝ) + 1) / 2 < (s + 1 / 2).re := by
        have : (s + 1 / 2).re = s.re + 1 / 2 := by simp
        rw [this]; linarith
      have h1 : MeromorphicAt (fun s => R (s + 1 / 2)) s :=
        MeromorphicAt.comp_analyticAt (g := (· + 1 / 2)) (hmer _ hs') (by fun_prop)
      have h2 : MeromorphicAt d s := (hdan s (show (0 : ℝ) < s.re by linarith)).meromorphicAt
      exact (h1.div h2).mul (MeromorphicAt.const C s)
    · have hs0 : (t : ℝ) / 2 < s.re := hs
      have hs' : ((t : ℝ) + 1) / 2 < (s + 1 / 2).re := by
        have : (s + 1 / 2).re = s.re + 1 / 2 := by simp
        rw [this]; linarith
      show R (s + 1 / 2) / d s * C = GlobalTheory.LFun.LSD D S par χ (s + 1 / 2) / d s * C
      rw [heq _ hs']
  have hext' : IsExtAt Z ((t : ℂ) / 2) (fun s => R (s + 1 / 2) / d s * C) := hext.congr hZ.symm
  have hpos : (0 : ℝ) < ((t : ℂ) / 2).re := lt_of_le_of_lt hr0 htr
  have hd0 : d ((t : ℂ) / 2) ≠ 0 := (hdne _ hpos).1
  have hshift : Tendsto (fun s : ℂ => s + 1 / 2) (𝓝[≠] ((t : ℂ) / 2)) (𝓝[≠] ((1 + (t : ℂ)) / 2)) := by
    have h := (Homeomorph.addRight (1 / 2 : ℂ)).map_punctured_nhds_eq ((t : ℂ) / 2)
    have e : (t : ℂ) / 2 + 1 / 2 = (1 + (t : ℂ)) / 2 := by ring
    have h' : map (fun x : ℂ => x + 1 / 2) (𝓝[≠] ((t : ℂ) / 2)) = 𝓝[≠] ((t : ℂ) / 2 + 1 / 2) := h
    rw [e] at h'
    exact h'.le
  have h2 : Tendsto d (𝓝[≠] ((t : ℂ) / 2)) (𝓝 (d ((t : ℂ) / 2))) :=
    (hdan _ hpos).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hlim' : Tendsto (fun s => (s - (t : ℂ) / 2) ^ (1 : ℕ) * (R (s + 1 / 2) / d s * C)) (𝓝[≠] ((t : ℂ) / 2))
      (𝓝 (ρ / d ((t : ℂ) / 2) * C)) := by
    refine (((hlim.comp hshift).div h2 hd0).mul_const C).congr fun s => ?_
    simp only [Pi.div_apply, Function.comp_apply, pow_one]
    ring
  have hc := hext'.coeffAt_of_tendsto hlim'
  have e := hz.unique (by simpa using hc)
  rw [e]
  exact mul_ne_zero (div_ne_zero hρ hd0) hC

end GlobalTheory.Core.Rk.Exh

end
