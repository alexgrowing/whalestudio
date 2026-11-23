import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleNonzeroConstantSecond
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleNonzeroConstantSecondStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise
noncomputable section
namespace GlobalTheory.BotSmallDict
open GlobalTheory.BotFormula (IsFinPt)
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {δ t0 : ℂ}
end GlobalTheory.BotSmallDict
namespace GlobalTheory.BotSmallDict
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.RowVacScalar (detIdl idemAt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (stdSnd)
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {δ t0 : ℂ}
end GlobalTheory.BotSmallDict
namespace GlobalTheory.BotSmallDict
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.RowVacScalar (detIdl idemAt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (stdSnd)
variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
  {A A' WW : HSp D} {X : Tri T A A' WW} {μ₀ : T} {δ t0 : ℂ} {s : T} {Q : ℕ} {P P' : Pair D ⊤ δ t0 Q}
theorem bottomKernel_eq_classSum_term : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω₂ : ℂ, Ω₂ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (h : GA D P'.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
            ∀ (x : GA D P'.a) (g' : GA D A'), GlobalTheory.BotFormula.IsFinPt A' g' x → ∀ T' : Tup D P'.a P'.d P'.n,
              X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g g' = Ω₂ * u * P'.term x h T' := by
  intro _ _ _ hI _
  refine ⟨0, fun _ _ _ => ⟨0, 0, fun _ _ D large₂ _ _ hR T Lc μ₀ hL G => ?_⟩⟩
  intro W _ i j A A' WW X δ t0 hX hβ
  have hc : D.host.ccK = ⊤ := hR.size.2.2.2.2.2.2.2.2.2.2.2.2.2
  by_cases hex : ∃ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P'
  · obtain ⟨s₀, Q₀, P₀, P₀', hB₀⟩ := hex
    have s1 : X.rA'.s = fun _ => 1 := funext fun τ => (hX.std'.2.2 τ).1
    have s3 : X.rW.s = fun _ => 1 := funext fun τ => (hX.stdW.2.2 τ).1
    have hv := hX.is.isVac'
    rw [s1, s3] at hv
    obtain ⟨κ, hκ, hvac⟩ := vac_const (hI D) hc (setup hc hX P₀'.crv) P₀'.pt0 hX.std'.2.1 hX.stdW.2.1 hv
    refine ⟨(∏ τ, GlobalTheory.NormExact.period D δ 1 τ ^ (P₀'.a * P₀'.n τ)) * κ,
      mul_ne_zero (Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (period_ne_zero P₀'.crv τ)) hκ, fun s Q P P' hB => ?_⟩
    have hS : A'.rank = P'.a := hX.rank'.trans hB.rank.2.1.symm
    have hT : WW.rank = P'.d := by rw [hB.rank.2.2.2, hB.rank.2.2.1, ← hX.rank, ← hX.rank', hX.is.rank]
    obtain ⟨ζ, hζ, r1⟩ := hvac hS hT P'.e0 P'.vac P'.W.nz
    obtain ⟨ζ', hζ', r2⟩ := reads_datum (hI D) hR hL hX hβ hB hS hT r1
    have hu := hζ.mul hζ'.isAlgUnit
    refine ⟨ζ * ζ', hu.1, hu.2.1, fun p _ _ lam => hu.2.2 p lam, fun ea ed h g hg x g' hg' T' => ?_⟩
    obtain ⟨-, e1, -, e2, -⟩ := GlobalTheory.BottomReal.bottom_real_eq G hL hB₀ hB
    rw [ker'_eq (hI D) hc hL hX hB ea ed (mul_ne_zero (mul_ne_zero hκ hζ.1) hζ'.ne_zero) r2 hg hg' T', e1, e2]
    ring
  · exact ⟨1, one_ne_zero, fun s Q P P' hB => absurd ⟨s, Q, P, P', hB⟩ hex⟩
end GlobalTheory.BotSmallDict
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
theorem _root_.GlobalTheory.T.smallStage_bottomKernel_eq_term : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω₂ : ℂ, Ω₂ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P'.a = A'.rank) (ed : P'.d = WW.rank) (h : GA D P'.d) (g : GA D WW), GlobalTheory.BotFormula.IsFinPt WW g h →
            ∀ (x : GA D P'.a) (g' : GA D A'), GlobalTheory.BotFormula.IsFinPt A' g' x → ∀ T' : Tup D P'.a P'.d P'.n,
              X.ker' W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T') g g' = Ω₂ * u * P'.term x h T' := by
  first | exact @_root_.GlobalTheory.BotSmallDict.bottomKernel_eq_classSum_term | exact _root_.GlobalTheory.BotSmallDict.bottomKernel_eq_classSum_term | (intros; apply _root_.GlobalTheory.BotSmallDict.bottomKernel_eq_classSum_term <;> assumption)
end
