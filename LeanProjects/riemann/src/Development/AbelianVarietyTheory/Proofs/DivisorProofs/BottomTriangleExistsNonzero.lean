import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFundamentalDomainEqVolMulClassSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTripleThetaKernelLeftRationalInvarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleThetaEvalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTrianglePairCompare
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotFormula.ClassSumMonotone
open GlobalTheory.SqTop

theorem gbig_mono' {Q Q' : GP} (h : GBig Q) (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}
    (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ), Q G μ₀ C x b → Q' G μ₀ C x b) : GBig Q' := by
  obtain ⟨CF0, h⟩ := h
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h⟩ := h ε CF hCF
  exact ⟨C0, x₀, fun C hC D large₂ he hx hR T Lc μ₀ hL G => H _ _ _ _ _ (h C hC D large₂ he hx hR T Lc μ₀ hL G)⟩

theorem gbig_and' {Q Q' : GP} (h : GBig Q) (h' : GBig Q') : GBig fun G μ₀ C x b => Q G μ₀ C x b ∧ Q' G μ₀ C x b := by
  obtain ⟨CF0, h⟩ := h
  obtain ⟨CF0', h'⟩ := h'
  refine ⟨max CF0 CF0', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h⟩ := h ε CF (le_of_max_le_left hCF)
  obtain ⟨C0', x₀', h'⟩ := h' ε CF (le_of_max_le_right hCF)
  exact ⟨max C0 C0', max x₀ x₀', fun C hC D large₂ he hx hR T Lc μ₀ hL G =>
    ⟨h C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ₀ hL G,
      h' C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ₀ hL G⟩⟩

end GlobalTheory.BotFormula.ClassSumMonotone

theorem GlobalTheory.BotFormula.theta_integral_classSum : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X →
      ∃ v : ℂ, v ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (g : GA D WW) (pt : GA D P.a → GA D A),
          (∀ x, GlobalTheory.BotFormula.IsFinPt A (pt x) x) → ∀ T : Tup D P.a P.d P.n,
            X.I W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g =
              v * ∑ᶠ x : GlobalTheory.NormSum.Cls D P.a (GlobalTheory.NormSum.intG D P.a),
                ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D P.a) x.out : ℂ))⁻¹ * X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g (pt x.out) := by
  intro hPr hTA hLM hInp hBS
  refine GlobalTheory.BotFormula.ClassSumMonotone.gbig_mono' (GlobalTheory.BotFormula.ClassSumMonotone.gbig_and' (GlobalTheory.T.bottom_triangle_theta_eval hPr hTA hLM hInp hBS) (GlobalTheory.T.bottom_triangle_pair_compare hPr hTA hLM hInp hBS)) ?_
  intro D T Lc sc G μ₀ C x b H
  obtain ⟨H3, H4⟩ := H
  intro W hW i j A A' WW X δ t0 hX
  obtain ⟨v, hv, hsum⟩ := GlobalTheory.T.integral_fundamentalDomain_eq_vol_mul_classSum A hX.std.1 X.m X.fd hX.is.meas.1 hX.is.meas.2
  refine ⟨v, hv, fun s Q P P' hB ea ed g pt hpt T => ?_⟩
  exact hsum P.a ea pt hpt _ (GlobalTheory.T.definiteBottomTriple_thetaKernel_left_rational_invariant hX s _ g)
    (fun k hk y => H4 W hW i j A A' WW X hX s Q δ t0 P P' hB ea ed g T k hk y)
    (fun x k hx hk y => H3 W hW i j A A' WW X hX s _ g P.a x k hx hk y)

end
