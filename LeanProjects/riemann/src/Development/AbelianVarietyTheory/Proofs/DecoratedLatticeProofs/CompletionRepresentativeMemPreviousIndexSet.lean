import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NormalRepresentationLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingIntegralTwistPrimeEqDeepFiniteSumStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsGLExistsUnique
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge

namespace GlobalTheory.RepsAtTwist

theorem exists_rep_flat_ne : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ j c (h : j + 1 + c = s) (b : L.β (j + 1)) (g' : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k), IsGL ι (L.h (j + 1) b P) g' → ∃ (al : L.β j) (g : GL (XIx (Fin R.k) (Fin R.t) (j) ⊕ Fin (c + 1 + 1)) k), IsGL ι (L.h j al P) g ∧ flat W.ψ ν ((W.T s R).mu (j + 1)) ((W.T s R).Phi j (c + 1) (by omega)) g g' ≠ 0 := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s W _ _ ν hν hc hA L G hL hP j c h b g' hg'
  have hm := hL.hm
  have hs := hA.steps
  obtain ⟨al, A₀, B₀, hne⟩ := hL.nonvan j (by omega) b P
  obtain ⟨g, hg, -⟩ := GlobalTheory.TwBridge.Model.isGL_existsUnique (k := k) ι j (c + 1 + 1) (by unfold cOf; omega) (L.h j al P)
  have hSum := GlobalTheory.T.unfoldingIntegral_twistPrime_eq_deep_finite_sum X Pr R Ch sel S₀ mu cst σ₀ P k ι s W ν hν hc hA
  obtain ⟨A₁, B₁, hAB⟩ := hSum j c h (L.h j al P) (L.h (j + 1) b P) g g' hg hg'
    (hL.boundQ j al P hA.nmem) (hL.boundQ (j + 1) b P hA.nmem) (hL.depthQ' P hA.nmem)
  obtain ⟨e', he'⟩ : ∃ e : XIx (Fin R.k) (Fin R.t) j ≃ Fin (R.N j), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e :=
    GlobalTheory.AtTypeExists.exists_ord.1 R.k R.t j
  obtain ⟨e, he⟩ : ∃ e : XIx (Fin R.k) (Fin R.t) (j + 1) ≃ Fin (R.N (j + 1)), GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e :=
    GlobalTheory.AtTypeExists.exists_ord.1 R.k R.t (j + 1)
  obtain ⟨x, hx⟩ := Function.ne_iff.1 (hne (max A₀ A₁) (max B₀ B₁) (le_max_left _ _) (le_max_left _ _))
  have hF := hAB (max A₀ A₁) (max B₀ B₁) (le_max_right _ _) (le_max_right _ _) e' e he' he x
  have hsg : W.sg ≠ 0 := by
    intro h0
    have h2 := GlobalTheory.TwBridge.Model.sg_sq (h := hA) (hok := hc)
    rw [h0] at h2
    norm_num at h2
  refine ⟨al, g, hg, fun h0 => ?_⟩
  have h1 := congrFun h0 (GlobalTheory.SymBridge.toLoc ι e e' x)
  rw [hF, Pi.zero_apply] at h1
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ((map_ne_zero σ₀).2 hx) h1
  · unfold sgn; exact zpow_ne_zero _ hsg
  · unfold sgn; exact zpow_ne_zero _ hsg

end GlobalTheory.RepsAtTwist
