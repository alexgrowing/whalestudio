import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleNonzeroPeriod
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomLayerParametersMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleNonzeroPeriodStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.KerFin
theorem bottomTheta_kernel_finite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω₀ : ℂ, Ω₀ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
            GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
            ∀ T, X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g y = Ω₀ * u * starRingEnd ℂ (P.term x h T) := by
  intro hPr hTI hLM hInp hBS
  refine gbig_comb (_root_.GlobalTheory.T.theta_parameters_match hPr hTI hLM hInp hBS) GlobalTheory.BotWeights.weights_const ?_
  intro D T Lc sc G μ₀ C x b q2 q3 W hW i j A A' WW X δ t0 hX hβ
  obtain ⟨r, rc, κ, hr, hrc, hκ, H2⟩ := q2 W hW i j A A' WW X δ t0 hX hβ
  obtain ⟨n₀, H3⟩ := q3 i j δ t0
  obtain ⟨Ω, hΩ, H1⟩ := GlobalTheory.T.bottomTriple_thetaKernel_minors_eq_const_conjJet G W hW i j A A' WW X hX r rc hr hrc n₀
  refine ⟨Ω * starRingEnd ℂ κ, mul_ne_zero hΩ ((map_ne_zero _).2 hκ), fun s Q P P' hB => ?_⟩
  obtain ⟨u, hu0, huQ, huU, hEq⟩ := H2 s Q P P' hB
  refine ⟨u, hu0, huQ, huU, fun ea ed h g x y hg hy Tu => ?_⟩
  have hne : κ * starRingEnd ℂ u ≠ 0 := mul_ne_zero hκ ((map_ne_zero _).2 hu0)
  rw [H1 P.a P.d P.n ea ed (H3 s Q P P' hB) s g y hg.1 hy.1 Tu, hEq ea ed h g x y hg hy,
    GlobalTheory.FunObj.NormUniq.applyAt0_smul _ hne]
  simp only [GlobalTheory.NormSum.Pair.term, map_mul, Complex.conj_conj]
  ring
end GlobalTheory.KerFin
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottomTheta_kernel_finiteDimensional : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω₀ : ℂ, Ω₀ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
            GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
            ∀ T, X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g y = Ω₀ * u * starRingEnd ℂ (P.term x h T) := by
  first | exact @_root_.GlobalTheory.KerFin.bottomTheta_kernel_finite | exact _root_.GlobalTheory.KerFin.bottomTheta_kernel_finite | (intros; apply _root_.GlobalTheory.KerFin.bottomTheta_kernel_finite <;> assumption)
end
