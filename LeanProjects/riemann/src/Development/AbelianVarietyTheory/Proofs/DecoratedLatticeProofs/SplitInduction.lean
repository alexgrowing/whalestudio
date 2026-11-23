import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairAlongChainStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNonzeroMoveConstantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveSplitSupportInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveCompactLevelInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecompositionStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.VacConst

theorem suppAt_one {D : D7} (e : Formalism.L2.Theta.AE D) (V : HSp D) : Formalism.L2.Theta.SuppAt e V 1 := by
  intro i j
  have h : mt V 1 - 1 = 0 := by rw [GlobalTheory.AdelicLatMove.mt_one, sub_self]
  rw [h, Matrix.zero_apply, mul_zero]

theorem split_induction {D : D7} (V : HSp D) (P : GA D V → Prop)
    (hP : ∀ g ∈ GfC V, P g → ∀ e, IsSplitIdem D e → ∀ s, Formalism.L2.Theta.SuppAt e V s → P (s * g))
    {s : GA D V} (hs : s ∈ splitPart V) : s ∈ GfC V ∧ ∀ g ∈ GfC V, P g → P (s * g) := by
  induction hs using Subgroup.closure_induction'' with
  | mem x hx =>
    obtain ⟨e, he, hx⟩ := hx
    exact ⟨GlobalTheory.SplitHecke.Stab.mem_GfC he hx, fun g hg h => hP g hg h e he x hx⟩
  | inv_mem x hx =>
    obtain ⟨e, he, hx⟩ := hx
    have hx' := GlobalTheory.SplitHecke.Stab.suppAt_inv hx
    exact ⟨GlobalTheory.SplitHecke.Stab.mem_GfC he hx', fun g hg h => hP g hg h e he _ hx'⟩
  | one => exact ⟨one_mem _, fun g _ h => by rwa [one_mul]⟩
  | mul x y _ _ ihx ihy =>
    refine ⟨mul_mem ihx.1 ihy.1, fun g hg h => ?_⟩
    rw [mul_assoc]
    exact ihx.2 _ (mul_mem ihy.1 hg) (ihy.2 g hg h)

theorem vacMove : GlobalTheory.Published.StrongApproxSU → ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z) (u : B.Word) (A : ColDat I l Z u (w.C.herm.base.Ch u)) ψ θ, A.Is (w.C.forms u) ψ θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m), A.VacMove θ i hi := by
  intro hSA B X I l Z w u A ψ θ hA i hi
  obtain ⟨c₀, hc, h1⟩ := GlobalTheory.T.exists_nonzero_move_constant I l Z w u A ψ θ hA i hi
  have hstd := (GlobalTheory.T.standard_pair_along_chain I l Z w u A ψ θ hA i hi).1
  refine ⟨c₀, hc, fun g hg h hh => ?_⟩
  obtain ⟨r, s, k, hr, hs, hk, hkL, rfl⟩ :=
    GlobalTheory.T.strong_approximation_decomposition hSA _ _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) hstd.gS g hg
  obtain ⟨r', s', k', hr', hs', hk', hkL', rfl⟩ :=
    GlobalTheory.T.strong_approximation_decomposition hSA _ _ _ (rankN (I.rec7 l Z) (i + 1) hi) hstd.gT h hh
  have h2 := GlobalTheory.T.move_compact_level_invariant I l Z w u A ψ θ hA i hi c₀ 1 1 (one_mem _) (one_mem _) h1 k hk k' hk' hkL hkL'
  rw [one_mul, one_mul] at h2
  have h3 := split_induction _ (fun g => A.MoveAt θ i hi c₀ g k') (fun g hg H e he t ht => by
    have := GlobalTheory.T.move_split_support_invariant I l Z w u A ψ θ hA i hi c₀ g k' hg hk' H e he t 1 ht (suppAt_one e _)
    rwa [one_mul] at this) hs
  have hsk := mul_mem h3.1 hk
  have h4 := split_induction _ (fun h => A.MoveAt θ i hi c₀ (s * k) h) (fun h hh H e he t ht => by
    have := GlobalTheory.T.move_split_support_invariant I l Z w u A ψ θ hA i hi c₀ (s * k) h hsk hh H e he 1 t (suppAt_one e _) ht
    rwa [one_mul] at this) hs'
  have h5 := GlobalTheory.T.move_rational_invariant I l Z w u A ψ θ hA i hi c₀ _ _ hsk (mul_mem h4.1 hk') (h4.2 k' hk' (h3.2 k hk h2)) r r' hr hr'
  rw [mul_assoc, mul_assoc]
  exact h5

end GlobalTheory.AdForm.VacConst
