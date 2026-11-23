import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneAtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeReductionEqOneOfLocalComponentOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LevChain

theorem mem_levS_iff_moves : ∀ (D : D7) (c : GlobalTheory.ChainOnto.Com D) (j : ℕ) (s : GlobalTheory.ChainOnto.PiLocalization₂ D), s.Is c j → ∀ v : GlobalTheory.FinPl.Pl D, v ∉ c.S → ∀ κ ∈ grpAt s.V (· = v), κ ∈ levS s.V s.β s.L ↔ Moves s.V κ s.Λ s.Λ (· = v) := by
  intro D c j s hs v hv κ hκ
  haveI : Submodule.IsLattice D.host.E s.Λ := hs.selfDual.1
  have hfg : s.Λ.FG := Submodule.IsLattice.fg (A := D.host.E)
  have hGf := (GlobalTheory.FinPl.KOpen.mem_grpAt_iff s.V (· = v) κ).1 hκ
  have hSt : Lev.finE s.V κ ∈ Formalism.L2.DIV.St s.β ↔ κ ∈ GlobalTheory.AdelicU.levelOpen D.sp.cm.sig s.V.gram s.Λ := by
    rw [GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_of_fg s.V s.β s.Λ hs.frame hfg κ]
    exact GlobalTheory.AdelicU.mem_levelOpen.symm
  constructor
  · intro h
    have h2 : Lev.finE s.V κ ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L := h.2
    exact GlobalTheory.FinPl.KOpen.moves_of_levelOpen s.V s.Λ hfg _ (hSt.1 (Formalism.L2.DIV.parLev_St h2.1))
  · intro hm
    have hS := hSt.2 (GlobalTheory.FinPl.KOpen.levelOpen_of_inK s.V s.Λ hfg _ ⟨hκ, hm⟩)
    obtain ⟨hr, ξ, hL⟩ := hs.lev
    refine ⟨hGf.1, ?_⟩
    refine GlobalTheory.LevSplit.mem_lev_of_red _ _ _ _ _ (GlobalTheory.LevSplit.finE_mem_UA _ _) hS fun PP hPP => ?_
    have hPg : PP ∈ c.Pg := by
      rw [hL] at hPP
      simpa [Lev.datY] using hPP
    refine GlobalTheory.ChainOnto.RedOne.redFn_eq_one D s.V s.β κ PP hS (hGf.2 _ ?_)
    intro he
    exact hv (Finset.mem_image.2 ⟨PP, hPg, he⟩)

end GlobalTheory.Core.Mi.LevChain

end
