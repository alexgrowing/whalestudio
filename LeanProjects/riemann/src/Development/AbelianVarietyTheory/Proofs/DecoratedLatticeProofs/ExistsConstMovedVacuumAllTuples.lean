import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacTIff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnStepsAreStandardHermitianPairs
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDataDifferBySplittingFactorQuotient
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitInduction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumAtIdentityNonzeroConstantStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumInvariantUnderSingleSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumInvariantUnderStdLatticeStabilizersStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedVacuumInvariantRationalFinitePartsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.VacAll

theorem vacT_twist {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {θ : InfFam (I.rec7 l Z)}
    {i : ℕ} {hi : i + 1 ≤ B.R.m} {c₀ : ℂ} {ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ} {μ₀ μ : (AE (I.rec7 l Z))ˣ →* Circle}
    {om₀ om : Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))}
    {vac : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ} (hv : IsThetaFunO ψ _ _ vac)
    (h0 : IsWeilDatumO ψ _ _ μ₀ μ₀ om₀) (h1 : IsWeilDatumO ψ _ _ μ μ om) (H : VacT I l Z θ i hi c₀ μ₀ om₀ vac) :
    VacT I l Z θ i hi c₀ μ om vac := by
  intro g hg h hh N N' hN hN' x y hx hy
  have e := GlobalTheory.WeilChange.weilData_differ_by_splitFac _ ψ _ _ μ₀ μ₀ μ μ om₀ om h0 h1 g h x y hx hy vac hv
  rw [e, xiS_smul, H g hg h hh N N' hN hN' x y hx hy]
  funext z
  have a1 : (μ₀ x : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have a2 : (μ₀ y : ℂ) ≠ 0 := Circle.coe_ne_zero _
  simp only [splitFacO, Circle.coe_mul, Circle.coe_inv]
  field_simp

end GlobalTheory.AdForm.VacAll

namespace GlobalTheory.AdForm.VacAll

theorem vacT_one : GlobalTheory.Published.StrongApproxSU → ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∃ c₀ : ℂ, c₀ ≠ 0 ∧ VacT I l Z θ i hi c₀ μ om vac := by
  intro hSA B X I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw
  obtain ⟨c₀, hc₀, h1⟩ := GlobalTheory.T.movedVacuum_at_identity_nonzero_constant I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw
  have hstd := (GlobalTheory.AdForm.StdStepsT.stdPair_steps_all I hI hP l Z ψ θ hψ hθ).1 i hi
  refine ⟨c₀, hc₀, vacT_iff.2 fun g hg h hh => ?_⟩
  obtain ⟨r, s, k, hr, hs, hk, hkL, rfl⟩ :=
    GlobalTheory.SplitDec.exists_rat_split_stab hSA _ _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) hstd.gS g hg
  obtain ⟨r', s', k', hr', hs', hk', hkL', rfl⟩ :=
    GlobalTheory.SplitDec.exists_rat_split_stab hSA _ _ _ (rankN (I.rec7 l Z) (i + 1) hi) hstd.gT h hh
  have h2 := GlobalTheory.T.movedVacuum_invariant_under_stdLattice_stabilizers I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw c₀ 1 1 (one_mem _) (one_mem _) h1 k hk k' hk' hkL hkL'
  rw [one_mul, one_mul] at h2
  have h3 := GlobalTheory.AdForm.VacConst.split_induction _ (fun g => MoveT I l Z θ i hi c₀ μ om vac g k') (fun g hg H e he t ht => by
    have := GlobalTheory.T.movedVacuum_invariant_under_singleSplitPlace I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw c₀ g k' hg hk' H e he t 1 ht
      (GlobalTheory.AdForm.VacConst.suppAt_one e _)
    rwa [one_mul] at this) hs
  have hsk := mul_mem h3.1 hk
  have h4 := GlobalTheory.AdForm.VacConst.split_induction _ (fun h => MoveT I l Z θ i hi c₀ μ om vac (s * k) h) (fun h hh H e he t ht => by
    have := GlobalTheory.T.movedVacuum_invariant_under_singleSplitPlace I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw c₀ (s * k) h hsk hh H e he 1 t
      (GlobalTheory.AdForm.VacConst.suppAt_one e _) ht
    rwa [one_mul] at this) hs'
  have h5 := GlobalTheory.T.movedVacuum_invariant_rationalFiniteParts I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw c₀ _ _ hsk (mul_mem h4.1 hk')
    (h4.2 k' hk' (h3.2 k hk h2)) r r' hr hr'
  rw [mul_assoc, mul_assoc]
  exact h5

theorem vacT_all : GlobalTheory.Published.StrongApproxSU → ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → VacT I l Z θ i hi c₀ μ om vac := by
  intro hSA B X I hI hP l Z ψ θ hψ hθ i hi vac hvac
  by_cases hex : ∃ (a : I.ι) (μ : (AE (I.rec7 l Z))ˣ →* Circle) (om : Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))),
      ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) ∧ IsWeilDatumO ψ _ _ μ μ om
  · obtain ⟨a₀, μ₀, om₀, hc0, hw0⟩ := hex
    obtain ⟨c₀, hc, H⟩ := vacT_one hSA I hI hP l Z ψ θ hψ hθ i hi vac hvac a₀ μ₀ om₀ hc0 hw0
    exact ⟨c₀, hc, fun a μ om _ hw => vacT_twist hvac.2.2 hw0 hw H⟩
  · exact ⟨1, one_ne_zero, fun a μ om hc hw => (hex ⟨a, μ, om, hc, hw⟩).elim⟩

end GlobalTheory.AdForm.VacAll
