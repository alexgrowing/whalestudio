import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CTFrameMatMulGram
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentOfIsWittFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.CuspOfFrame

theorem isIsoFrame_initCols {D : D7} {V : HSp D} {m : ℕ} {X Y : Matrix (Fin V.rank) (Fin m) D.host.E}
    (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (k : Fin m) : IsIsoFrame V (GlobalTheory.StdPar.initCols X k) := by
  have hf := GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm
  have hli := GlobalTheory.CompanionTheory.UnipCocompact.linearIndependent_of_isWittFrame (GlobalTheory.SiegelSet.sigma_sigma hf.1) (hf.2 V) hW
  refine ⟨Nat.succ_pos _, ?_, ?_⟩
  · exact hli.comp (Fin.castLE k.2) (Fin.castLE_injective k.2)
  · have h := hW.xx
    refine Matrix.ext fun a b => ?_
    have := congrFun (congrFun h (Fin.castLE k.2 a)) (Fin.castLE k.2 b)
    simpa [GlobalTheory.StdPar.initCols, Matrix.mul_apply, Formalism.UG.cT] using this

theorem isCuspFun_of_isConstAlong : ∀ (D : D7) (V : HSp D) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → (∀ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C → r ≤ m) → ∀ f : GA D V → ℂ, (∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) → (∀ k : Fin m, IsConstAlong D.sp.cm.sig V.gram X {k} f 0) → IsCuspFun V f := by
  intro D V m X Y hW hmax f hl hc
  have hl' : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) f := hl
  refine (GlobalTheory.Cusp.isCuspFun_iff hl').2 fun W hW' => ?_
  obtain ⟨r, C, hC, rfl⟩ := (GlobalTheory.AutFunCompare.isIsotropic_iff V W).1 hW'
  have hrm := hmax r C hC
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by have := hC.1; omega⟩
  let k : Fin m := ⟨r', by omega⟩
  have hC0 : IsIsoFrame V (GlobalTheory.StdPar.initCols X k) := isIsoFrame_initCols hW k
  have hcc : GlobalTheory.Cusp.Cocompact (GQ V) (GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC0)) := GlobalTheory.Cusp.cocompact_single _
  haveI : LocallyCompactSpace (GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC0)) := by
    rw [GlobalTheory.Cusp.NA_frameFlag hC0]
    exact (GlobalTheory.CuspDecay.Model.isClosed_NI V hC0).locallyCompactSpace
  have e : GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC0) = GlobalTheory.SiegelSet.unipRad D.sp.cm.sig V.gram (GlobalTheory.StdPar.initCols X k) :=
    GlobalTheory.Cusp.NA_frameFlag hC0
  have h1 : GlobalTheory.UAut.IsConstTermOn D.sp.cm.sig V.gram (GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC0)) f 0 := by
    rw [e]
    exact GlobalTheory.UAut.isConstTerm_iff.1 ((GlobalTheory.StdPar.isConstAlong_singleton hW k).1 (hc k))
  have h2 : GlobalTheory.UAut.IsConstTermOn D.sp.cm.sig V.gram (GlobalTheory.Cusp.NA (GlobalTheory.Cusp.frameFlag hC0)) f
      (GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag hC0) f) := fun μ 𝓕 b1 b2 b3 g => by
    rw [GlobalTheory.Cusp.constTerm_eq b2 hl' g, MeasureTheory.Measure.real, b3]
    simp
  have h0 : GlobalTheory.Cusp.constTerm (GlobalTheory.Cusp.frameFlag hC0) f = 0 := h2.unique hcc h1
  exact GlobalTheory.CompanionTheory.ConstTermConj.constTerm_eq_zero_of_frame D V (r' + 1) _ C hC0 hC f hl h0

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.CuspOfFrame

end
